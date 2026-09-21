(ns writ.book
  "check-book: scan a namespace's forms and run every rule.

  The forms are read as data (quote a vector of top-level forms).  Data, law and
  proof declarations are collected; every defn is kind-checked,
  match-expanded and checked by writ.check; the law gate runs last.

  Order carries meaning, as in bend: a def may reference only names defined
  earlier (no mutual recursion), a law may be cited only by a proof that comes
  after its own proof, and a law name is declared once."
  (:require [clojure.java.io :as io]
            [writ.check :as ck]
            [writ.data :as dt]
            [writ.kind :as kind]
            [writ.match :as mt]
            [writ.law :as lw]
            [writ.ann :as ann]
            [writ.defn :as d]
            [writ.types :as ty]
            [writ.norm :as norm]))

(defn- wdefn? [f]
  (let [tail (drop 2 f)
        tail (if (string? (first tail)) (rest tail) tail)
        tail (if (map? (first tail)) (rest tail) tail)
        params (first tail)
        after (second tail)]
    (boolean (and (vector? params)
                  (or (some #{:-} params) (= ':- after))))))

(defn- plain-of [f]
  (if (wdefn? f)
    (let [[_ nm0 & tail] f
          tail (if (string? (first tail)) (rest tail) tail)
          [attrs tail] (if (map? (first tail)) [(first tail) (rest tail)] [nil tail])
          ;; the attr-map position is defn metadata: it belongs on the name,
          ;; where the descend marker is read from
          nm (if attrs (vary-meta nm0 merge attrs) nm0)
          params (first tail)
          body (rest tail)]
      (d/build nm params body))
    f))

(defn- param-names
  "Parameter name -> quantity, the matchable scope of a defn."
  [params]
  (into {} (comp (filter symbol?)
                 (map (fn [p] [(symbol (name p)) (ann/quantity-of p)])))
        params))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(defn- first-dup [xs]
  (loop [seen #{}, xs (seq xs)]
    (if-not xs
      nil
      (if (contains? seen (first xs))
        (first xs)
        (recur (conj seen (first xs)) (next xs))))))

(defn- def-form? [f]
  (and (seq? f) (symbol? (first f)) (= "def" (name (first f)))))

(def ^:private deflike-heads
  "Heads that bind top-level names but are not plain def/defn.  A book checks
  def, defn, data, law and proof only; silently skipping these would leave
  their bodies unchecked (Typed Clojure's stance: unknown code is an error,
  never an unsound pass-through)."
  #{"declare" "defonce" "defmulti" "defmethod" "defmacro" "defprotocol"
    "defrecord" "deftype" "defstruct" "definline" "definterface"})

(defn- deflike-form? [f]
  (and (seq? f) (symbol? (first f)) (contains? deflike-heads (name (first f)))))

(defn- ns-form? [f]
  (and (seq? f) (symbol? (first f)) (= "ns" (name (first f)))))

(defn- comment-form? [f]
  (and (seq? f) (symbol? (first f)) (= "comment" (name (first f)))))

(defn- refer-syms
  "Unqualified names a single :require or :use entry refers in
  (`:refer [a b]`, `:only [a b]`)."
  [entry]
  (when (sequential? entry)
    (loop [xs (seq entry), acc []]
      (if-not xs
        acc
        (if (contains? #{:refer :only} (first xs))
          (let [v (fnext xs)]
            (recur (rest (rest xs))
                   (if (sequential? v) (into acc (filter symbol?) v) acc)))
          (recur (next xs) acc))))))

(defn- ns-refers
  "Every name referred in by the book's ns form (:require :refer, :use
  :only).  These are external names,
  not book-local defs, so the ordering rule lets them through."
  [forms]
  (into #{}
        (comp (filter ns-form?)
              (mapcat (fn [nsf]
                        ;; names referred from the book's own ns are book
                        ;; names, not externals
                        (let [own (name (second nsf))]
                          (->> (rest nsf)
                               (filter #(and (sequential? %) (contains? #{:require :use} (first %))))
                               (mapcat rest)
                               (remove #(and (sequential? %) (= own (name (first %)))))
                               (mapcat refer-syms))))))
        forms))

(defn- book-names
  "Every top-level name the book binds: def/defn names, data types and
  their constructors.  A book is one namespace, so these shadow
  clojure.core for the whole book -- forward references included, which
  then read as the ordering errors they are."
  [forms]
  (into #{}
        (comp (remove #(or (ns-form? %) (comment-form? %)))
              (mapcat (fn [f]
                        (cond
                          ;; a law or proof expands to a def of its name
                          (or (lw/law-form? f) (lw/proof-form? f)) [(second f)]
                          (def-form? f) [(second f)]
                          (ck/defn-form? f) [(second f)]
                          (dt/data-form? f) (let [dl (dt/parse f)]
                                              (cons (:name dl) (keys (:ctors dl))))
                          :else []))))
        forms))

(defn- def-value
  "A def's value form, behind an optional docstring only -- the same read
  the host performs (a map in that position is the value, not metadata)."
  [f]
  (let [tail (drop 2 f)]
    (cond
      (empty? tail) :writ/no-value
      (string? (first tail)) (if (next tail) (second tail) (first tail))
      :else (first tail))))

(defn- walk-self-refs
  "Reject a def's own name anywhere in its value outside a fn body: during
  init the name is unbound, and Bend never lets a self-reference escape as
  a value (tests/halt/type_level_recursion).  Quote subtrees only store the
  symbol; inside a fn body a self-reference is recursion, and there it
  must be a call head, checked for descent with the def's other rules."
  [nm form]
  (cond
    (= nm form)
    (fail! "def `" nm "` refers to itself in its own value; a name is unbound "
           "during its own init -- Bend's defs reference earlier names only")

    (seq? form)
    (when-not (and (symbol? (first form))
                   (contains? #{"fn" "fn*" "quote" "clojure.core/fn"
                                "clojure.core/fn*"} (str (first form))))
      (doseq [a form] (walk-self-refs nm a)))

    (coll? form) (doseq [x form] (walk-self-refs nm x))

    :else nil))

(defn- fn-arity
  "[:min :max] for a parameter vector; a nil max means variadic."
  [psyms]
  (let [ri (first (keep-indexed (fn [i p] (when (= '& p) i)) psyms))]
    (if (some? ri)
      {:min ri :max nil}
      {:min (count psyms) :max (count psyms)})))

(defn- book-arities
  "name -> {:min :max} for every book fn: defn parameters, a def whose value
  is a fn, and data constructors (their field count).  A book is never
  evaluated, so writ owns the arity contract the host would otherwise
  enforce with a runtime ArityException."
  [forms]
  (into {}
        (comp (remove #(or (lw/law-form? %) (lw/proof-form? %) (ns-form? %)
                           (comment-form? %)))
              (mapcat (fn [f]
                        (cond
                          (ck/defn-form? f)
                          (let [plain (plain-of f)
                                [_ _ & tail] plain
                                tail (if (string? (first tail)) (rest tail) tail)
                                tail (if (map? (first tail)) (rest tail) tail)]
                            {(:name (d/signature plain)) (fn-arity (vec (first tail)))})

                          (def-form? f)
                          (let [v (def-value f)]
                            (cond
                              (and (seq? v) (symbol? (first v))
                                   (contains? #{"fn" "fn*"} (name (first v))))
                              (let [tail (rest v)
                                    named? (symbol? (first tail))
                                    ps (if named? (second tail) (first tail))]
                                {(second f) (fn-arity (vec ps))})

                              ;; no value form at all: the ordering gate
                              ;; owns it ("must carry a value")
                              (= :writ/no-value v) nil

                              ;; any other value -- a fn above, else a
                              ;; docstring, nil, a number, a collection or a
                              ;; quoted form: a constant, callable at no
                              ;; arity (the host fails the cast to IFn)
                              :else {(second f) :not-fn}))

                          (dt/data-form? f)
                          (let [dl (dt/parse f)]
                            (into {(:name dl) {:type true :min 0 :max 0}}
                                  (map (fn [[c info]] [c {:min (count (:fields info))
                                                             :max (count (:fields info))
                                                             :ctor true}]))
                                  (:ctors dl)))

                          :else nil))))
        forms))

(defn- typed-sigs
  "Signatures with host class hints dropped: only types writ knows under
  `tenv` are checked."
  [sigs tenv]
  (let [t (fn [x] (ty/binder-type (when (some? x) (with-meta 'x {:writ/type x})) tenv))]
    (into {} (map (fn [[k s]] [k {:params (mapv t (:params s)) :ret (t (:ret s))}]))
          sigs)))

(defn- book-sigs
  "name -> {:params [type] :ret type} for every book defn and def of an
  fn, read from its annotations; a missing annotation is nil (unknown)."
  [forms]
  (into {}
        (keep (fn [f]
                (cond
                  (and (def-form? f) (symbol? (second f))
                       (let [v (def-value f)]
                         (and (seq? v) (symbol? (first v))
                              (contains? #{"fn" "fn*"} (name (first v))))))
                  (let [v (def-value f)
                        ps (if (symbol? (second v)) (nth v 2 nil) (second v))]
                    (when (vector? ps)
                      [(second f) {:params (mapv #(or (:writ/type (meta %)) (:tag (meta %)))
                                                 (remove #{'&} ps))
                                   :ret nil}]))
                  :else
                (when (and (ck/defn-form? f) (symbol? (second f)))
                  (let [sig (d/signature (plain-of f))]
                    [(symbol (name (:name sig)))
                     {:params (mapv :type (remove #(= '& (:name %)) (:params sig)))
                      :ret (:ret sig)}])))))
        forms))

(defn- check-one! [tenv0 f ok shadow arities sigs]
  (let [plain (plain-of f)
        sig (d/signature plain)
        ;; a plain defn keeps its attr-map in place; w/defn moved it onto the name
        tenv (d/forall-tenv (let [a (nth plain 2 nil)]
                              (if (map? a) (vary-meta (second plain) merge a) (second plain)))
                            tenv0)
        params (:params sig)
        ret (:ret sig)
        scope (param-names (map :name params))
        allowed (set (map (fn [p] (symbol (clojure.core/name (:name p)))) params))
        types (into {} (keep (fn [p] (when-let [t (ty/binder-type (:name p) tenv)]
                                       [(symbol (clojure.core/name (:name p))) t])))
                    params)
        pf (mt/rewrite tenv scope plain types)]
    ;; a parameter's type may name only the parameters before it (a
    ;; telescope, as in Bend); the return type sees them all
    (doseq [[i p] (map-indexed vector params)]
      (when (:type p)
        (kind/check-type (:type p) tenv
                         (set (map (fn [q] (symbol (clojure.core/name (:name q)))) (take i params)))))
      (kind/check-binder-kind (:name sig) p tenv))
    (when ret (kind/check-type ret tenv allowed))
    (ck/check-defn pf ok shadow arities {:tenv tenv :sigs (typed-sigs sigs tenv)})
    (:name sig)))

(defn check-standalone
  "Check one defn outside a book: an annotated w/defn goes through the same
  kind, match and type checks a book runs, with the datatypes
  declared so far (writ.data/registry); a plain defn goes straight to the
  checker.  No ordering rule applies."
  [form]
  (let [f (d/annotate-fns form)]
    (if (and (ck/defn-form? f) (wdefn? f))
      (do (check-one! @dt/registry f nil nil nil {}) {:ok true})
      (ck/check-defn f))))

(defn- check-law-prop!
  "Walk a law's proposition: quantifier domains are types, and each
  equality side is checked like code by ck/check-law-term."
  [lname prop tenv ok shadow arities law-names]
  (let [head (fn [s] (and (seq? prop) (symbol? (first prop)) (= s (name (first prop)))))]
    (cond
      (head "=") (doseq [t (rest prop)] (ck/check-law-term lname t ok shadow arities law-names))
      (or (head "=>") (head "and"))
      (doseq [q (rest prop)] (check-law-prop! lname q tenv ok shadow arities law-names))
      (or (head "forall") (head "exists"))
      (let [[_ [_ t] body] prop]
        (kind/check-type t tenv #{})
        (check-law-prop! lname body tenv ok shadow arities law-names))
      :else nil)))

(defn- ns-info
  "The book's ns name and its :require aliases (alias -> target ns)."
  [forms]
  (let [nsf (first (filter ns-form? forms))
        nm (when nsf (second nsf))
        aliases (into {}
                      (comp (filter #(and (sequential? %) (= :require (first %))))
                            (mapcat rest)
                            (filter sequential?)
                            (keep (fn [e]
                                    (let [m (apply hash-map (rest e))]
                                      (when-let [a (:as m)] [(name a) (name (first e))])))))
                      (when nsf (rest nsf)))]
    {:name (some-> nm name) :aliases aliases}))

(defn- normalize-names
  "Resolve qualified names the way the book's ns would: a name qualified
  with the book's own ns (or an alias of it) is a book-local name, so the
  ordering rule sees it; any other alias resolves to its target ns, so
  c/eval under [clojure.core :as c] is clojure.core/eval.  Quoted data is
  left alone."
  [form {:keys [name aliases]}]
  (letfn [(fix [s]
            (let [ns (namespace s)
                  target (get aliases ns ns)]
              (cond
                (nil? ns) s
                (= target name) (with-meta (symbol (clojure.core/name s)) (meta s))
                (not= target ns) (with-meta (symbol target (clojure.core/name s)) (meta s))
                :else s)))
          (walk [f]
            (cond
              (symbol? f) (fix f)
              (and (seq? f) (= 'quote (first f))) f
              (seq? f) (with-meta (apply list (map walk f)) (meta f))
              (vector? f) (with-meta (mapv walk f) (meta f))
              (map? f) (into (empty f) (map (fn [[k v]] [(walk k) (walk v)])) f)
              (set? f) (into (empty f) (map walk) f)
              :else f))]
    (walk form)))

(defn check-book
  [forms]
  (let [info (ns-info forms)
        forms (mapv (fn [f] (if (ns-form? f) f (d/annotate-fns (normalize-names f info))))
                    forms)
        shadow (book-names forms)
        arities (book-arities forms)
        sigs (book-sigs forms)
        refers (ns-refers forms)
        decls (mapv dt/parse (filter dt/data-form? forms))
        _ (when-let [d (first-dup (mapv :name decls))]
            (fail! "data name `" d "` is declared more than once"))
        _ (when-let [c (first-dup (mapcat (fn [dl] (map key (:ctors dl))) decls))]
            (fail! "constructor `" c "` is declared by two types"))
        law-forms (filter lw/law-form? forms)
        law-names (mapv (comp :name lw/parse-law) law-forms)
        _ (when (not= (count law-names) (count (distinct law-names)))
            (fail! "duplicate law name: `" (first (drop 1 (first (filter #(> (count %) 1)
                                                                          (partition-by identity (sort law-names))))))
                   "` is declared more than once"))
        laws (into {} (map (fn [f] (let [l (lw/parse-law f)] [(:name l) l])) law-forms))
        proofs (mapv lw/parse-proof (filter lw/proof-form? forms))]
    (let [tenv
    (loop [fs forms, tenv {}, ok (ns-refers forms), seen #{}]
      (if-let [f (first fs)]
        (cond
          ;; a law or proof defs its name, so it may not reuse a book
          ;; name; a law's terms are checked like code, at its position
          (or (lw/law-form? f) (lw/proof-form? f))
          (let [n (second f)]
            (when (contains? seen n)
              (fail! "`" n "` is declared more than once"))
            (when (lw/law-form? f)
              (let [{:keys [prop]} (lw/parse-law f)]
                (lw/check-prop-shape! prop)
                (check-law-prop! n prop tenv ok shadow arities
                                 (into (set law-names) (map :name proofs)))))
            ;; a proof discharges a law declared before it
            (when (lw/proof-form? f)
              (let [cited (:law (lw/parse-proof f))]
                (when (and (contains? laws cited) (not (contains? seen cited)))
                  (fail! "proof `" n "` discharges law `" cited "`, which is declared "
                         "later; a law comes before its proof"))))
            (recur (rest fs) tenv ok (conj seen n)))

          (dt/data-form? f)
          (let [dl (dt/parse f)
                ;; a type and its constructors are book-level names: neither
                ;; may collide with a name another form already declared
                names (cons (:name dl) (keys (:ctors dl)))]
            (doseq [n names]
              (when (contains? seen n)
                (fail! "`" n "` is declared more than once")))
            ;; a field sees the types declared so far, its own type's
            ;; parameters, and the type itself (recursive fields)
            (doseq [[_ c] (:ctors dl), ft (:fields c)]
              (kind/check-type ft
                               (assoc tenv (:name dl) (dt/env dl))
                               ;; the type's own name resolves through tenv, so
                               ;; a parametric type needs its arguments
                               (set (:params dl))))
             (recur (rest fs) (assoc tenv (:name dl) (dt/env dl))
                    (into ok names) (into seen names)))

          (def-form? f)
          (let [n (second f)
                _ (when-not (symbol? n)
                    (fail! "First argument to def must be a symbol, had: `" n "`"))
                _ (when (some? (namespace n))
                    (fail! "Cannot def namespace qualified symbol: `" n "`"))
                _ (when (or (> (count f) 4)
                           (and (= (count f) 4) (not (string? (nth f 2 nil)))))
                    (fail! "Too many arguments to def `" n "`: a def carries "
                           "an optional docstring and one value"))
                _ (when (< (count f) 3)
                    (fail! "def `" n "` must carry a value; a book is never "
                           "evaluated, so an unbound name cannot be known"))
                v (if (= (count f) 4) (nth f 3 nil) (nth f 2 nil))
                ;; a def value is a definition too: BendTT checks every
                ;; definition at its binder, so any seq value runs the full
                ;; pipeline (ordering, affine locals, recursion).  Match
                ;; rewriting additionally needs a fn's params for its scope.
                v (if (and (seq? v) (symbol? (first v))
                           (contains? #{"fn" "fn*"} (name (first v))))
                    (let [tail (rest v)
                          named? (symbol? (first tail))
                          params (if named? (second tail) (first tail))
                          pscope (into {} (comp (filter symbol?)
                                                (map (fn [s] [(symbol (name s))
                                                              (ann/quantity-of s)])))
                                      params)]
                      (mt/rewrite tenv pscope v
                                  (into {} (keep (fn [s] (when-let [t (ty/binder-type s tenv)]
                                                           [(symbol (name s)) t])))
                                        (filter symbol? params))))
                    v)]
            (when (contains? seen n)
              (fail! "def `" n "` is declared more than once"))
            (when (contains? refers n)
              (fail! "`" n "` already refers to a name the ns form brings in; a "
                     "book def cannot redefine it"))
            ;; the name is unbound during its own init: outside a fn body
            ;; it may not appear at all; inside one it is recursion,
            ;; checked for descent below
            (walk-self-refs n v)
            (let [anon-fn? (and (seq? v) (symbol? (first v))
                                (contains? #{"fn" "fn*"} (name (first v)))
                                ;; a NAMED fn owns its own recursion (the
                                ;; named-fn machinery checks descent); an
                                ;; anonymous fn's params and body drive the
                                ;; checks, so the wrapper is stripped
                                (not (symbol? (second v))))]
              (if anon-fn?
                (let [tail (rest v)
                      params (first tail)
                      body (rest tail)]
                  (ck/check-defn (list* 'clojure.core/defn n params body)
                                 ok shadow arities
                                 {:tenv tenv :sigs (typed-sigs sigs tenv)}))
                (when (and (seq? v) (symbol? (first v)))
                  (ck/check-defn (list 'clojure.core/defn n [] v)
                                 ok shadow arities
                                 {:tenv tenv :sigs (typed-sigs sigs tenv)}))))
            (recur (rest fs) tenv (conj ok n) (conj seen n)))

          (ck/defn-form? f)
          (let [_ (when (and (symbol? (second f)) (contains? refers (second f)))
                    (fail! "`" (second f) "` already refers to a name the ns form "
                           "brings in; a book def cannot redefine it"))
                _ (when (and (symbol? (second f)) (contains? seen (second f)))
                    (fail! "defn `" (second f) "` is declared more than once"))
                n (check-one! tenv f ok shadow arities sigs)]
            (recur (rest fs) tenv (conj ok n) (conj seen n)))

          (deflike-form? f)
          (fail! "`" (first f) "` is not supported in a book; a book checks "
                  "def, defn, data, law and proof forms only")

          (or (ns-form? f) (comment-form? f))
          (recur (rest fs) tenv ok seen)

          :else
          (fail! "`" (if (and (seq? f) (symbol? (first f))) (first f) f)
                 "` is not supported in a book; a book checks "
                 "def, defn, data, law and proof forms only"))
        tenv))]
      (binding [norm/*opaque* shadow
                norm/*numeric-fns* (into #{} (keep (fn [[k s]]
                                                     (when (contains? '#{Nat Int Float Double}
                                                                      (some-> (:ret s) ty/plain-type))
                                                       k)))
                                         sigs)]
        (lw/gate laws proofs tenv)))
    {:ok true}))

(defn read-forms
  "Read every top-level form in a source file."
  [path]
  (with-open [r (java.io.PushbackReader. (io/reader path))]
    (loop [forms []]
      (let [form (read {:eof ::eof} r)]
        (if (= ::eof form)
          forms
          (recur (conj forms form)))))))

(defn check-files
  "Read the given source files and check them as one book."
  [& paths]
  (check-book (vec (mapcat read-forms paths))))
