(ns writ.check
  "The annotation checker.

  `check-defn` takes a Clojure `defn` form and enforces:

  * quantities -- every binder is used the way its annotation says: affine
    (`1`) at most once (zero uses is legal weakening), erased (`:zero`)
    never, reusable (`:many`) freely.  Binders are the parameters plus every
    local the body introduces (let/loop bindings and fn parameters), and a
    local may not shadow an earlier binder.

  * termination -- recursion must be marked `^{:writ/descend true}`.  Every
    recursive call, including `recur`, must then descend: the arguments
    before the shrinking one are passed unchanged, and the shrinking one is
    structurally smaller -- a value destructured from a parameter, or a
    projection (`dec`/`rest`/`nth`/...) of one.

  * ordering -- with `ok` (the set of names defined earlier in the book), a
    call to an unknown name is rejected: Bend's defs reference earlier names
    only, which rules out mutual recursion.

  Returns `{:ok true}` or throws an ex-info carrying `:writ/error true`."
  (:require [writ.quant :as q]
            [writ.ann :as ann]
            [writ.kind :as kind]
            [writ.lower :as l]
            [writ.uses :as u]
            [writ.types :as ty]
            [clojure.string]))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(defn- qname-of [p] (if (symbol? p) (symbol (clojure.core/name p)) p))

(def ^:dynamic *affine*
  "When false, the quantity rules (affinity, erasure, reuse, captures and
  overlapping destructures) are skipped.  writ.spec checks plain Clojure,
  which carries no quantity annotations, with this off."
  true)

(def ^:dynamic *descend-all*
  "When true, every defn is checked for descent as if it were marked
  ^{:writ/descend true}.  writ.spec checks plain Clojure with this on."
  false)

(def core-names
  "Names resolvable in clojure.core; invoking them is always in scope."
  (into #{} (map key) (ns-publics 'clojure.core)))

(def core-arities
  "name -> {:min :max} for non-macro clojure.core publics, derived from the
  host's own :arglists at load time (typedclojure checks core call arity
  from its annotations of clojure.core; writ's port reads the host's own
  declarations instead of keeping a hand-rolled table).  A nil :max means
  some arglist is variadic."
  (into {}
        (keep (fn [[k v]]
                (let [m (meta v)]
                  (when (and (:arglists m) (not (:macro m)))
                    (let [forms (map (fn [al]
                                       (let [ri (first (keep-indexed
                                                         (fn [i s] (when (= '& s) i))
                                                         al))]
                                         [(if ri ri (count al)) (boolean ri)]))
                                     (:arglists m))]
                      [(symbol (clojure.core/name k))
                       {:min (apply min (map first forms))
                        :max (when-not (some second forms)
                               (apply max (map first forms)))}])))))
        (ns-publics 'clojure.core)))

(defn- required? [observed declared]
  (case declared
    :0 (= observed q/q0)
    :1 (not= observed q/qw)
    :w true))

(def ^:private destructure-temp?
  "Compiler-generated binders are not the programmer's: destructure's G__123
  temps and auto-gensyms like if-let's temp__5__auto are read several times
  by the generated code, so they carry :w, not the default affine."
  (let [pat (re-pattern "(?:^G__\\d+|__auto)(?:__\\d+)?$")]
    (fn [n] (boolean (and (symbol? n) (re-find pat (name n)))))))

(defn- count-str [qq]
  (case qq :0 "0 times" :1 "once" :w "more than once"))

;; --- AST walking ---------------------------------------------------------

(defn- ast-children [ast]
  (case (:op ast)
    :if [(:test ast) (:then ast) (:else ast)]
    :do (conj (:stmts ast) (:ret ast))
    :let (conj (mapv second (:bindings ast)) (:body ast))
    :loop (conj (mapv second (:bindings ast)) (:body ast))
    :fn [(:body ast)]
    :invoke (conj (:args ast) (:fn ast))
    :recur (:args ast)
    :case (conj (mapv :body (:clauses ast)) (:scrut ast) (:default ast))
    :vec (:items ast)
    :set (:items ast)
    :map (concat (:keys ast) (:vals ast))
    []))

(defn- walk-ast [ast f]
  (f ast)
  (doseq [c (ast-children ast)] (when (map? c) (walk-ast c f))))

(defn- ref? [x] (and (map? x) (= :ref (:op x))))

;; --- quantities ----------------------------------------------------------

(defn- binder-syms
  "Every local binder the body introduces, in walk order: let/loop bindings
  and fn parameters, metadata included."
  [ast]
  (let [acc (atom [])]
    (walk-ast ast (fn [n]
                    (case (:op n)
                      (:let :loop) (doseq [[b _] (:bindings n)]
                                     (swap! acc into (l/binding-names b)))
                      :fn (doseq [p (remove nil? (:params n))] (swap! acc conj p))
                      nil)))
    @acc))

(declare check-param-dups display)

(defn- check-quantities
  [nm params raw-ast body-ast]
  ;; binder discipline runs on the raw (pre-uniquify) AST, where names are
  ;; what the programmer wrote: shadowing and duplicates are theirs to fix
  (let [pnames (set (map qname-of params))]
    (doseq [b (binder-syms raw-ast)]
      (when (contains? pnames (qname-of b))
        (fail! "`" b "` in `" nm "` shadows a parameter")))
    (walk-ast raw-ast
              (fn [n]
                (cond
                  (= :fn (:op n)) (check-param-dups nm (remove nil? (:params n)))
                  (contains? #{:let :loop} (:op n))
                  ;; destructure rebinds its own G__ temporaries in sequence;
                  ;; only names the programmer wrote are theirs to keep unique
                  (let [bs (remove destructure-temp?
                                  (mapcat (fn [bb] (l/binding-names (first bb))) (:bindings n)))]
                    (when (not= (count bs) (count (distinct bs)))
                      (fail! "duplicate binder in `" nm "`"))))))
    (let [locals (binder-syms body-ast)
          declared (into {} (map (fn [p] [(qname-of p)
                                          (if (destructure-temp? p) :w (ann/quantity-of p))]))
                         (concat params locals))
          obs (u/uses declared body-ast)]
      (doseq [n (keys declared)]
        (let [d (get declared n)
              observed (get obs n q/q0)]
          (when-not (required? observed d)
            (fail! "`" (display n) "` in `" nm "` is used " (count-str observed)
                   " but is declared " (ann/qname d))))))))

(declare named-fns)

(defn- display
  "A binder's name as the programmer wrote it: uniquify's suffix removed."
  [s]
  (if (symbol? s) (symbol (clojure.string/replace (name s) #"__\d+$" "")) s))

(defn- gensym?
  "A name a macro made up (doseq's `G__1`, a syntax-quoted `x__auto__`),
  which the programmer never wrote and cannot find in their code."
  [s]
  (and (symbol? s) (boolean (re-find #"^G__\d+$|__auto__" (name (display s))))))

(defn- check-overlaps
  "Destructuring consumes its source like a match; a pattern whose binders
  overlap (a key read twice, `:as` beside fields) copies the source, which
  is legal only when the source is a reusable binder."
  [nm params raw-ast]
  (let [declared (into {} (map (fn [b] [(qname-of b) (ann/quantity-of b)]))
                       (concat (filter symbol? params) (binder-syms raw-ast)))]
    (doseq [p params]
      (when-let [why (and (coll? p) (l/pattern-overlap p))]
        (when-not (= :w (ann/quantity-of p))
          (fail! "a parameter of `" nm "` destructures into overlapping binders ("
                 why "); that copies it -- mark the pattern ^:many"))))
    (walk-ast raw-ast
      (fn [n]
        (doseq [[init why] (:writ/overlaps n)]
          (when-not (and (symbol? init) (= :w (get declared (qname-of init))))
            (fail! "`" (pr-str init) "` in `" nm "` is destructured into "
                   "overlapping binders (" why "); that copies it -- only a "
                   "reusable (^:many) binder may be copied")))))))

(def duplicating-core
  "Core fns whose result holds a plain argument more than once."
  '#{repeat replicate constantly iterate cycle})

(defn- check-captures
  "A closure is affine and a core higher-order fn may call its fn argument
  any number of times, so an affine binder captured by a fn passed to one
  is copied (Bend: a template argument must be closed).  Book fns, local
  fns and the defn itself check their own params, so passing a closure to
  them is fine.  A core fn that duplicates a plain argument copies an
  affine binder passed to it."
  [nm params body-ast shadow]
  (let [declared (into {} (map (fn [p] [(qname-of p) (if (destructure-temp? p) :w
                                                         (ann/quantity-of p))]))
                       (concat (filter symbol? params) (binder-syms body-ast)))
        fn-locals (into {} (keep (fn [[b init]] (when (= :fn (:op init)) [(qname-of b) init])))
                        (let [acc (atom [])]
                          (walk-ast body-ast (fn [n] (when (contains? #{:let :loop} (:op n))
                                                       (swap! acc into (:bindings n)))))
                          @acc))
        local-fns (into (set (keys fn-locals))
                        (map (fn [f] (qname-of (:name f)))) (named-fns body-ast))
        pset (set (keys declared))
        core-head (fn [f]
                    (when (ref? f)
                      (let [s (:name f)]
                        (cond
                          (= "clojure.core" (namespace s)) (symbol (name s))
                          (namespace s) s
                          (or (contains? local-fns s) (contains? pset s)
                              (= (qname-of s) (qname-of nm))
                              (and shadow (contains? shadow s))) nil
                          :else s))))
        captures (fn [fnode]
                   (let [inner (into (set (map qname-of (binder-syms fnode)))
                                     (map (fn [f] (qname-of (:name f)))) (named-fns fnode))
                         acc (atom #{})]
                     (walk-ast fnode (fn [n] (when (and (ref? n)
                                                        (not (contains? inner (:name n)))
                                                        (= :1 (get declared (:name n))))
                                               (swap! acc conj (:name n)))))
                     @acc))]
    (walk-ast body-ast
      (fn [n]
        (when (= :invoke (:op n))
          (let [f (:fn n)
                head (when-not (= :fn (:op f)) (core-head f))
                param-head? (and (ref? f) (contains? pset (:name f))
                                 (not (contains? local-fns (:name f))))
                target (or head (when param-head? (:name f)))]
            (when target
              (doseq [a (:args n)]
                (let [fnode (cond (= :fn (:op a)) a
                                  (ref? a) (get fn-locals (:name a)))]
                  (when fnode
                    (when-let [c (first (sort (captures fnode)))]
                      (fail! "`" (display c) "` in `" nm "` is captured by a fn passed to `"
                             (display target) "`, which may be called more than once; "
                             "mark it ^:many or pass it as an argument")))
                  (when (and head (contains? duplicating-core (symbol (name head)))
                             (ref? a) (= :1 (get declared (:name a))))
                    (fail! "`" (display (:name a)) "` in `" nm "` is passed to `"
                           (display head) "`, which copies it; mark it ^:many")))))))))))

;; --- termination ---------------------------------------------------------

(defn- self-calls [self ast]
  (let [acc (atom [])]
    (walk-ast ast (fn [n]
                    (when (and (= :invoke (:op n))
                               (= :ref (:op (:fn n)))
                               (= (qname-of (:name (:fn n))) (qname-of self)))
                      (swap! acc conj n))))
    @acc))

(defn- named-fns [ast]
  (let [acc (atom [])]
    (walk-ast ast (fn [n] (when (and (= :fn (:op n)) (:name n)) (swap! acc conj n))))
    @acc))

;; Bend's descent law: a self-call's arguments are read left to right, each
;; passed unchanged until one is a strict subterm of ITS OWN column, and a
;; column only shrinks where a test has refined it (a match arm, in Bend).
;; Every term is traced to its origin: the frame column it copies, or the
;; column it is a strict subterm of plus what each projection step needs
;; proven.  Branch tests prove facts about columns along the path.

(def ^:private shrink-needs
  "A shrinking projection -> what its column must be proven to be: rest-like
  steps need it non-empty ((rest ()) is ()), next-like steps non-nil, and
  both need it finite ((rest (range)) never runs out); element reads need
  it non-nil.  dec is tracked separately, per depth."
  '{rest #{:empty :finite}, pop #{:empty :finite}, next #{:nil :finite},
    nnext #{:nil :finite}, butlast #{:nil :finite},
    first #{:nil}, second #{:nil}, last #{:nil}, peek #{:nil}, ffirst #{:nil}})

(defn- lit-val [a] (when (and (map? a) (= :lit (:op a))) (:val a)))

(defn- pos-int-lit? [a] (let [v (lit-val a)] (and (integer? v) (pos? v))))

(defn- core-head
  "The clojure.core fn an invoke calls, unless a param, local or book name
  binds that name."
  [t info]
  (when (and (map? t) (= :invoke (:op t)) (ref? (:fn t)))
    (let [s (:name (:fn t))]
      (when (and (or (nil? (namespace s)) (= "clojure.core" (namespace s)))
                 (not (contains? (:bound info) s)))
        (symbol (name s))))))

(defn- shrink-step
  "[step operand]: step is :dec, :inc or a set of structural needs.  A
  lookup with a default is not a step: the default can hand the value back."
  [t info]
  (let [h (core-head t info)
        args (:args t)
        n (count args)
        [a b] args]
    (case h
      dec (when (= n 1) [:dec a])
      inc (when (= n 1) [:inc a])
      - (when (and (= n 2) (= 1 (lit-val b))) [:dec a])
      + (cond (and (= n 2) (= 1 (lit-val b))) [:inc a]
              (and (= n 2) (= 1 (lit-val a))) [:inc b]
              :else nil)
      (rest pop next nnext butlast first second last peek ffirst)
      (when (= n 1) [(get shrink-needs h) a])
      ;; a literal nil default cannot hand the column back: the read is
      ;; an element or nil, both below a non-nil column
      (nth get) (when (or (= n 2) (and (= n 3) (= :lit (:op (nth args 2)))
                                       (nil? (lit-val (nth args 2)))))
                  [#{:nil} a])
      drop (when (and (= n 2) (pos-int-lit? a)) [#{:empty :finite} b])
      nthrest (when (and (= n 2) (pos-int-lit? b)) [#{:empty :finite} a])
      nthnext (when (and (= n 2) (pos-int-lit? b)) [#{:nil :finite} a])
      subvec (when (and (<= 2 n 3) (pos-int-lit? b)) [#{:empty :finite} a])
      nil)))

(defn- numeric-only? [o] (every? vector? (:needs o)))

(defn- origin
  "Where `t` comes from, relative to the column names in `stop`:
  {:col c :net 0 :strict? false} for an unchanged copy of column c;
  {:col c :strict? true :needs #{..}} for a strict subterm, where needs
  are what each step requires of the column; for a dec/inc chain, :net is
  how far below c the value sits and each dec at depth k needs [:num k]
  (c minus k proven positive).  Copies, (seq x), let chains, destructure
  and match temporaries are followed; a loop binder outside `stop` is
  opaque (recur rebinds it)."
  [t info stop]
  (cond
    (ref? t)
    (let [n (:name t)]
      (cond
        (contains? stop n) {:col n :net 0 :strict? false :needs #{}}
        (contains? (:loops info) n) nil
        (contains? (:binds info) n) (origin (get (:binds info) n) info stop)
        :else nil))

    ;; destructure's map coercion and a match's tag read branch on the
    ;; value's shape; both branches must agree on the column
    (= :if (:op t))
    (let [a (origin (:then t) info stop)
          b (origin (:else t) info stop)
          coercion? (contains? '#{seq? vector? map?} (core-head (:test t) info))]
      (cond
        (and a b (= (:col a) (:col b)) (= (:net a 0) (:net b 0)))
        {:col (:col a) :net (:net a 0) :strict? (and (:strict? a) (:strict? b))
         :needs (into (:needs a) (:needs b))}
        (and coercion? (or a b) (not (and a b)))
        (assoc (or a b) :strict? false :needs #{} :net 0)
        :else nil))

    (= :invoke (:op t))
    (if-let [[step x] (shrink-step t info)]
      (when-let [o (origin x info stop)]
        (case step
          :dec (when (numeric-only? o)
                 (let [k (:net o 0)]
                   {:col (:col o) :net (inc k) :strict? true
                    :needs (conj (:needs o) [:num k])}))
          ;; inc undoes a dec; back at (or past) the column is not smaller
          :inc (when (and (numeric-only? o) (pos? (:net o 0)))
                 (let [k (dec (:net o 0))]
                   (assoc o :net k :strict? (pos? k))))
          (when (and (numeric-only? o) (zero? (:net o 0)) (empty? (:needs o)))
            {:col (:col o) :net 0 :strict? true :needs (into (:needs o) step)})
          ))
      (when (and (= 'seq (core-head t info)) (= 1 (count (:args t))))
        (origin (first (:args t)) info stop)))

    :else nil))

(defn- test-facts
  "[then else]: the facts a branch test proves about columns, as sets of
  [:pos c k] / [:nonzero c k] (c minus k is positive / nonzero),
  [:nonempty c], [:nonnil c] and [:eq c v]."
  [test info stop]
  (let [col (fn [e] (:col (origin e info stop)))
        num (fn [e] (let [o (origin e info stop)]
                      (when (and o (numeric-only? o)) [(:col o) (:net o 0)])))
        num-fact (fn [f e] (if-let [[c k] (num e)] #{[f c k]} #{}))
        one (fn [f c] (if c #{[f c]} #{}))
        h (core-head test info)
        [a b] (:args test)
        none [#{} #{}]
        ;; `and` and `or` expand to (let [g x] (if g more g)) and
        ;; (let [g x] (if g g more))
        [g x body] (when (and (= :let (:op test)) (= 1 (count (:bindings test))))
                     (let [[[g x]] (:bindings test)] [g x (:body test)]))
        g-ref? (fn [e] (and (ref? e) (= g (:name e))))]
    (cond
      (and g (= :if (:op body)) (g-ref? (:test body)) (g-ref? (:else body)))
      (let [[t1 _] (test-facts x info stop)
            [t2 _] (test-facts (:then body) info stop)]
        [(into t1 t2) #{}])

      (and g (= :if (:op body)) (g-ref? (:test body)) (g-ref? (:then body)))
      (let [[_ e1] (test-facts x info stop)
            [_ e2] (test-facts (:else body) info stop)]
        [#{} (into e1 e2)])

      :else
    (case h
      zero? [#{} (num-fact :nonzero a)]
      pos? [(num-fact :pos a) #{}]
      (= ==) (let [[e v] (cond (lit-val b) [a (lit-val b)]
                               (lit-val a) [b (lit-val a)]
                               :else [nil nil])]
               (cond
                 (nil? e) none
                 (= 0 v) [#{} (num-fact :nonzero e)]
                 (integer? v) [(into (one :nonnil (col e))
                                     (if-let [[c k] (num e)]
                                       (if (zero? k) #{[:eq c v]} #{})
                                       #{}))
                               #{}]
                 (some? v) [(one :nonnil (col e)) #{}]
                 :else none))
      < (cond (= 0 (lit-val a)) [(num-fact :pos b) #{}]
              (= 1 (lit-val b)) [#{} (num-fact :pos a)]
              :else none)
      > (cond (= 0 (lit-val b)) [(num-fact :pos a) #{}]
              (= 1 (lit-val a)) [#{} (num-fact :pos b)]
              :else none)
      <= (cond (= 0 (lit-val b)) [#{} (num-fact :pos a)] :else none)
      >= (cond (= 0 (lit-val a)) [#{} (num-fact :pos b)] :else none)
      (seq not-empty) [(one :nonempty (col a)) #{}]
      empty? [#{} (one :nonempty (col a))]
      nil? [#{} (one :nonnil (col a))]
      (some? coll? map? vector? seq? sequential? list? set? string? contains?)
      [(one :nonnil (col a)) #{}]
      not (let [[t e] (test-facts a info stop)] [e t])
      ;; any other test: a truthy value is non-nil
      (if (or (ref? test) (origin test info stop))
        [(one :nonnil (col test)) #{}]
        none)))))

(defn- case-clause-facts
  "Facts a `case` clause proves: when its test constants are all non-nil,
  the scrutinee is non-nil there, and so is the column an element read
  like (first x) took it from -- (first nil) is nil."
  [ast clause info stop]
  (let [test (:test clause)
        consts (if (seq? test) test [test])
        scrut (:scrut ast)
        col (fn [e] (:col (origin e info stop)))]
    (if (and (seq consts) (every? some? consts))
      (into #{}
            (comp (remove nil?) (map (fn [c] [:nonnil c])))
            [(col scrut)
             (when (contains? '#{first second last peek nth get ffirst}
                              (core-head scrut info))
               (col (first (:args scrut))))])
      #{})))

(defn- proven? [need c facts info]
  (if (vector? need)
    (let [k (second need)]
      (or (contains? facts [:pos c k])
          (and (contains? (:nat info) c) (contains? facts [:nonzero c k]))))
    (case need
      :empty (contains? facts [:nonempty c])
      :nil (or (contains? facts [:nonnil c]) (contains? facts [:nonempty c]))
      :finite (contains? (:finite info) c))))

(defn- literal-smaller? [a c facts]
  (let [v (lit-val a)]
    (and (integer? v) (>= v 0)
         (some (fn [f] (and (= :eq (first f)) (= c (second f)) (< v (nth f 2))))
               facts))))

(defn- need-text [need c]
  (let [c (display c)]
    (if (vector? need)
      (let [k (second need)
            v (if (zero? k) (str "`" c "`") (str "`" c "` minus " k))]
        (str "`" c "` must first be tested so that " v " is positive (a `pos?` "
             "test), or nonzero (a `zero?` test) when `" c "` is a Nat"))
      (case need
        :empty (str "`" c "` must first be tested non-empty (a `seq` or `empty?` test)")
        :nil (str "`" c "` must first be tested non-nil (a truthiness, `some?` or `seq` test)")
        :finite (str "`" c "` must be a finite collection: give it the type (List T), "
                     "(Vec T), (Set T), (Map K V) or a datatype -- with `ann` in a "
                     "spec, or an annotation -- a lazy seq may never run out")))))

(defn- check-descent!
  "Bend's descent law at one self-call or recur: the arguments before the
  shrinking one pass their columns unchanged, and the shrinking one is a
  strict subterm of its own column under a guard proving the shrink."
  [nm args names facts info & [what where]]
  (let [what (or what (str "recursive call to `" nm "`"))
        where (or where "parameters")
        stop (set names)
        os (mapv #(origin % info stop) args)
        own? (fn [i] (let [o (nth os i)] (and o (= (:col o) (nth names i nil)))))
        smaller (fn [i] (or (literal-smaller? (nth args i) (nth names i nil) facts)
                            (and (own? i) (:strict? (nth os i)))))
        idx (first (filter smaller (range (count args))))]
    (when (nil? idx)
      (fail! what " does not descend: no argument is a "
             "structurally smaller part of its own parameter (destructure it, "
             "or use dec/rest/next of it under a test)"))
    (dotimes [i idx]
      (when-not (and (own? i) (not (:strict? (nth os i))))
        (fail! what " does not descend: argument " (inc i)
               " before the shrinking one must be passed unchanged; put `"
               (display (nth names idx)) "` first in the " where)))
    (when-not (literal-smaller? (nth args idx) (nth names idx) facts)
      (let [c (nth names idx)]
        (doseq [need (sort-by pr-str (:needs (nth os idx)))]
          (when-not (proven? need c facts info)
            (let [shown (get (:sources info) c c)]
              (fail! what " does not descend: argument "
                     (inc idx) " shrinks `" (display shown) "` without a guard; "
                     (need-text need shown)))))))))

(defn- term-info
  "What origin tracing needs about a body: let binders -> init, loop binder
  names (opaque), every name a projection could be shadowed by, the
  columns known to be Nat, and those known to be finite collections."
  [params ast shadow tenv]
  (let [tenv (or tenv {})
        finite-type? (fn [t]
                       (and (some? t)
                            (or (= 'String t)
                                (and (seq? t) (contains? '#{List Vec Set Map} (first t)))
                                (and (symbol? t) (contains? tenv t) (not (:tvar (get tenv t))))
                                (and (seq? t) (contains? tenv (first t))))))
        binds (atom {})
        loops (atom #{})
        sources (atom {})
        nat (atom (into #{} (comp (filter #(= 'Nat (ty/binder-type % tenv)))
                                  (map qname-of))
                        params))
        finite (atom (into #{} (comp (filter #(finite-type? (ty/binder-type % tenv)))
                                     (map qname-of))
                           params))
        copy-of (fn [init s]
                  (let [x (if (and (= :invoke (:op init))
                                   (contains? '#{seq vec} (core-head init {:bound #{}}))
                                   (= 1 (count (:args init))))
                            (first (:args init))
                            init)]
                    (and (ref? x) (contains? s (qname-of (:name x))))))]
    (walk-ast ast
      (fn [n]
        (case (:op n)
          :let (doseq [[b init] (:bindings n)] (swap! binds assoc b init))
          :loop (doseq [[b init] (:bindings n)]
                  (swap! loops conj b)
                  (when (gensym? b)
                    (let [x (if (and (= :invoke (:op init)) (= 1 (count (:args init)))
                                     (contains? '#{seq vec} (core-head init {:bound #{}})))
                              (first (:args init))
                              init)]
                      (when (ref? x) (swap! sources assoc b (:name x)))))
                  (when (or (= 'Nat (ty/binder-type b tenv))
                            (let [v (lit-val init)] (and (integer? v) (>= v 0)))
                            (and (ref? init) (contains? @nat (qname-of (:name init))))
                            (= 'count (core-head init {:bound #{}})))
                    (swap! nat conj b))
                  (when (or (finite-type? (ty/binder-type b tenv))
                            (copy-of init @finite))
                    (swap! finite conj b)))
          nil)))
    {:binds @binds
     :loops @loops
     :sources @sources
     :nat @nat
     :finite @finite
     :bound (into (set shadow) (comp (remove nil?) (map qname-of)) params)}))

(defn- self-escape! [nm]
  (fail! "`" nm "` refers to itself as a value; a self-reference must be the "
         "head of a call, where its descent is checked"))

(declare walk-term)

(defn- ast-tail-bags
  "[non-tail-children tail-children] for each AST op.  A `recur` is legal
  only in a tail child (Clojure compiles only tail recursion); a recur in a
  non-tail child is a compile error in Clojure, so it is rejected here too."
  [ast]
  (case (:op ast)
    :if [(vector (:test ast)) [(:then ast) (:else ast)]]
    :do [(vec (:stmts ast)) [(:ret ast)]]
    :let [(mapv second (:bindings ast)) [(:body ast)]]
    :loop [(mapv second (:bindings ast)) [(:body ast)]]
    :fn [nil [(:body ast)]]
    :case [(vector (:scrut ast)) (cond-> (mapv :body (:clauses ast))
                                   (:default ast) (conj (:default ast)))]
    :invoke [(conj (vec (:args ast)) (:fn ast)) nil]
    :recur [(vec (:args ast)) nil]
    :vec [(vec (:items ast)) nil]
    :set [(vec (:items ast)) nil]
    :map [(vec (concat (:keys ast) (:vals ast))) nil]
    [nil nil]))

(defn- frame
  "The loop-frame a binder form pushes: every name it binds, and how many
  source slots a recur must rebind (a destructured binding is one slot)."
  [bs]
  {:names (vec (mapcat (fn [b] (map qname-of (l/binding-names b))) bs))
   :slots (count bs)})

(defn- check-recur-shape
  "The recur frame contract as a shape error, checked before every semantic
  pass.  typed.cljc.analyzer's parse-recur validates tail position and
  arity at parse time, before any analysis; here the arity gate lived in
  the termination walk, which runs after the quantity pass, so a
  wrong-arity recur was masked by an affinity error (a doubled argument
  is also a double use) or by the marking message.  The frame logic is
  identical to walk-term's, only hoisted."
  [nm params ast]
  (let [seed (assoc (frame (filter some? params)) :tries 0)
        walk (fn walk [ast loops tail?]
               (when (= :recur (:op ast))
                 (when-not tail?
                   (fail! "`recur` in `" nm "` must be in tail position"))
                 (let [slots (or (:slots (peek loops))
                                 (count (:names (peek loops))))]
                   (when (not= (count (:args ast)) slots)
                     (fail! "`recur` in `" nm "` rebinds " slots
                            " value(s) but is passed " (count (:args ast))))))
               (let [[nt t] (ast-tail-bags ast)
                     loops-t (case (:op ast)
                               :loop (conj loops (frame (map first (:bindings ast))))
                               :fn   (conj loops (frame (filter some? (:params ast))))
                               loops)]
                 (doseq [c (distinct (remove nil? nt))] (walk c loops false))
                 (doseq [c (distinct (remove nil? t))] (walk c loops-t true))))]
    (walk ast [seed] true)))

(defn- walk-term
  "Walk a body under its loop frames and the facts its branch tests prove.
  A recur must be in tail position, marked, not across a try, and descend
  against its own frame; a call to `self` must be marked and descend
  against `self-params`; `self` anywhere else is an escaping value."
  [ast loops ctx tail? tries facts]
  (let [{:keys [nm self self-params marked? info]} ctx
        self? (fn [t] (and (ref? t) (= (qname-of (:name t)) (qname-of self))))]
    (when (and (self? ast)) (self-escape! self))
    (when (= :recur (:op ast))
      (when-not tail?
        (fail! "`recur` in `" nm "` must be in tail position"))
      (when-not marked?
        (fail! "`" nm "` recurs through `loop`/`recur`: mark it "
               "^{:writ/descend true} so the recursion is checked to descend"))
      (let [fr (peek loops)
            names (vec (:names fr))
            slots (or (:slots fr) (count names))]
        (when (> tries (or (:tries fr) 0))
          (fail! "`recur` in `" nm "` cannot cross a `try`; Clojure compiles it "
                 "only inside the try's own loop"))
        (when (not= (count (:args ast)) slots)
          (fail! "`recur` in `" nm "` rebinds " slots " value(s) but is passed "
                 (count (:args ast))))
        (check-descent! nm (:args ast) names facts info
                        (if (and (seq names) (every? gensym? names))
                          (str "a macro's loop in `" nm "`, such as a `doseq`,")
                          (str "`recur` in `" nm "`"))
                        (if (:loop? fr) "`loop` bindings" "parameters"))))
    (when (and (= :invoke (:op ast)) (self? (:fn ast)))
      (when-not marked?
        (fail! "`" self "` is recursive: mark it ^{:writ/descend true} so every "
               "call is checked to descend"))
      (check-descent! self (:args ast) (mapv qname-of (filter some? self-params))
                      facts info))
    (let [stop (into (set (map qname-of (filter some? self-params)))
                     (mapcat :names) loops)
          [ft fe] (when (= :if (:op ast)) (test-facts (:test ast) info stop))
          loops-t (case (:op ast)
                    :loop (conj loops (assoc (frame (map first (:bindings ast)))
                                             :tries tries :loop? true))
                    :fn   (conj loops (assoc (frame (filter some? (:params ast)))
                                             :tries tries))
                    loops)
          tries* (if (:writ/try? ast) (inc tries) tries)
          go (fn [c ls tail? fs] (when (map? c) (walk-term c ls ctx tail? tries* fs)))]
      (case (:op ast)
        :case (do (go (:scrut ast) loops false facts)
                  (doseq [cl (:clauses ast)]
                    (go (:body cl) loops-t tail? (into facts (case-clause-facts ast cl info stop))))
                  (go (:default ast) loops-t tail? facts))
        :if (do (go (:test ast) loops false facts)
                (go (:then ast) loops-t tail? (into facts ft))
                (go (:else ast) loops-t tail? (into facts fe)))
        ;; the head of a self-call is the call, not an escaping value
        :invoke (do (when-not (self? (:fn ast)) (go (:fn ast) loops false facts))
                    (doseq [a (:args ast)] (go a loops false facts)))
        (let [[nt t] (ast-tail-bags ast)]
          (doseq [c (distinct (remove nil? nt))] (go c loops false facts))
          ;; an fn and a loop each open their own recur frame, so their body
          ;; is in tail position whatever position the fn or loop is in
          (doseq [c (distinct (remove nil? t))]
            (go c loops-t (if (#{:fn :loop} (:op ast)) true tail?) facts)))))))

(defn- check-termination [nm params body-ast marked? shadow tenv]
  (let [info (term-info params body-ast shadow tenv)]
    ;; the defn body is itself an implicit loop: a tail recur there rebinds
    ;; the defn's own params, so the loop stack is seeded with them
    (walk-term body-ast [(assoc (frame (filter some? params)) :tries 0)]
               {:nm nm :self nm :self-params params :marked? marked? :info info}
               true 0 #{})
    ;; a named local fn owns its recursion the same way: BendTT 2.5 runs the
    ;; descent test at every self-reference, and an fn carries no marker to
    ;; opt out, so its self-calls must descend unconditionally
    (doseq [f (named-fns body-ast)]
      (let [finfo (term-info (:params f) (:body f) shadow tenv)]
        (walk-term (:body f) [(assoc (frame (filter some? (:params f))) :tries 0)]
                   {:nm (qname-of (:name f)) :self (:name f) :self-params (:params f)
                    :marked? true :info finfo}
                   true 0 #{})))))

(defn- fn-node-entries
  "let/loop binders initialized to an fn, in a raw AST: [binder fn-node]."
  [ast]
  (let [acc (atom [])]
    (letfn [(walk [a]
              (when (map? a)
                (when (contains? #{:let :loop} (:op a))
                  (doseq [[b init] (:bindings a)]
                    (when (and (symbol? b) (= :fn (:op init)))
                      (swap! acc conj [b init]))))
                (doseq [c (ast-children a)] (walk c))))]
      (walk ast))
    @acc))

(defn- invoked-names
  "Node names invoked anywhere in `ast`, fn boundaries included: a nested
  closure's calls belong to the enclosing binder's call graph."
  [nodes ast]
  (let [acc (atom #{})]
    (letfn [(walk [a]
              (when (map? a)
                (when (and (= :invoke (:op a))
                           (= :ref (:op (:fn a)))
                           (contains? nodes (qname-of (:name (:fn a)))))
                  (swap! acc conj (qname-of (:name (:fn a)))))
                (doseq [c (ast-children a)] (walk c))))]
      (walk ast)
      @acc)))

(defn- check-local-cycles
  "Bend's defs reference earlier names only, so no descent can be checked
  across a cycle: a defn and the local fns it binds must form a call graph
  whose only loops are self-recursions (those run the descent rule).  Runs
  on the raw AST: uniquify renames binders but not the raw cross-fn
  references inside fn bodies, so keys must be the names as written."
  [nm raw-ast]
  (let [nm* (qname-of nm)
        entries (fn-node-entries raw-ast)
        nodes (into #{nm*} (map first) entries)
        edges (into {nm* (invoked-names nodes raw-ast)}
                    (map (fn [[b init]] [b (invoked-names nodes init)]))
                    entries)
        on-path (atom #{})
        visit (fn visit [n]
                (swap! on-path conj n)
                (doseq [m (get edges n)]
                  (if (contains? @on-path m)
                    (when (not= m n)
                      (fail! "`" n "` and `" m "` are mutually recursive in `"
                             nm "`; Bend's defs reference earlier names only, "
                             "so no descent can be checked across a cycle"))
                    (visit m)))
                (swap! on-path disj n))]
    (doseq [n nodes] (visit n))))

;; --- reusable functions (BendTT: + never forms over a function type) ------

(defn- check-fn-reuse
  "A function is never reusable.  Quantity checking alone cannot know a
  binder's kind, so the reuse gate runs here for every binder that does not
  carry a type: a fn parameter marked ^:many, a let/loop local marked ^:many
  and bound to an fn value (directly or through a chain of copies), and a
  reusable parameter that is applied."
  [nm params body-ast]
  (let [pq (into {} (map (fn [p] [(qname-of p)
                                   {:q (ann/quantity-of p)
                                    :typed? (some? (:tag (meta p)))}]))
                     params)
        base (into #{} (comp (remove #(and (some? (:tag (meta %)))
                                           (not (kind/function-type? (:tag (meta %))))))
                              (map qname-of))
                       params)
        fn-locals (atom #{})
        _ (walk-ast body-ast
                    (fn [n]
                      (when (contains? #{:let :loop} (:op n))
                        (doseq [[b init] (:bindings n)]
                          (let [bs (mapv qname-of (l/binding-names b))
                                many? (some (fn [x] (= :w (ann/quantity-of x)))
                                            (l/binding-names b))]
                            (when many?
                              (cond
                                (= :fn (:op init))
                                (swap! fn-locals into bs)

                                (ref? init)
                                (let [src (qname-of (:name init))]
                                  (when (or (contains? @fn-locals src)
                                            (contains? base src))
                                    (swap! fn-locals into bs))))))))))]
    (walk-ast body-ast
      (fn [n]
        (case (:op n)
          ;; an untyped reusable fn param; a typed one answers to the
          ;; Data proof in writ.types
          :fn (doseq [p (remove nil? (:params n))]
                (when (and (= :w (ann/quantity-of p)) (nil? (ty/binder-type p {}))
                           (nil? (:tag (meta p))) (nil? (:writ/type (meta p))))
                  (fail! "`" p "` in `" nm "` cannot be reusable (^:many): "
                         "a function is never reusable")))
          (:let :loop) (doseq [[b init] (:bindings n)]
                         (when (and (= :fn (:op init))
                                    (some (fn [x] (= :w (ann/quantity-of x)))
                                          (l/binding-names b)))
                           (fail! "`" (first (l/binding-names b)) "` in `" nm
                                  "` cannot be reusable (^:many): it is bound to a "
                                  "function, and a function type cannot be reused")))
          :invoke (let [callee (when (ref? (:fn n)) (qname-of (:name (:fn n))))
                        info (get pq callee)]
                    (cond
                      ;; an applied untyped parameter is a function; a typed one
                      ;; answers to the kind rule, which owns reusable binders
                      (and info (= :w (:q info)) (not (:typed? info)))
                      (fail! "`" callee "` in `" nm "` cannot be reusable (^:many): "
                             "it is applied, and a function is never reusable")

                      (contains? @fn-locals callee)
                      (fail! "`" callee "` in `" nm "` cannot be reusable (^:many): "
                             "it is applied, and a function type cannot be reused")))
          nil)))))

;; --- ordering ------------------------------------------------------------

(def ^:private nested-def-heads
  "Heads that bind a top-level name. Inside a body they would escape the
  book: a book is never evaluated, so there is no var to create and the
  name would slip past every rule (order, quantity, termination)."
  #{"def" "defn" "defn-" "declare" "defonce" "defmulti" "defmethod" "defmacro"
    "defprotocol" "defrecord" "deftype" "defstruct" "definline" "definterface"})

(defn- case-test-consts
  "The constants one case clause matches: a plain literal, itself; a group
  `(1 2)`, its members; a quoted form, itself (it is one constant).  A bare
  symbol is not a constant -- Clojure rejects it at compile time, and a
  book is never compiled, so writ owns the contract here."
  [nm c]
  (cond
    (seq? c) (if (= 'quote (first c))
               [c]
               (mapcat (fn [m] (case-test-consts nm m)) c))
    (symbol? c) (fail! "case test `" c "` in `" nm "` must be a compile-time "
                       "constant; quote it to compare against the symbol itself")
    :else [c]))

(defn- check-param-dups
  "Parameters are binders, so the duplicate-binder rule applies; `_` is the
  wildcard exception and may repeat.  Uniquify renames duplicate fn params
  apart, so the discipline is enforced on the raw params."
  [nm params]
  (let [ps (remove #(or (nil? %) (= '_ %)) params)]
    (when (not= (count ps) (count (distinct ps)))
      (fail! "duplicate parameter in `" nm "`: `"
             (first (first (filter #(> (count %) 1) (partition-by identity ps))))
             "` appears twice"))))

(defn- check-case-constants [nm ast]
  ;; Clojure rejects duplicate case test constants at compile time; a book
  ;; is never compiled, so writ owns that contract here
  (walk-ast ast
    (fn [n]
      (when (= :case (:op n))
        (let [seen (atom #{})
              dup (atom nil)]
          (doseq [c (mapcat (fn [t] (case-test-consts nm t))
                            (mapv :test (:clauses n)))]
            (when (and (nil? @dup) (contains? @seen c))
              (reset! dup c))
            (swap! seen conj c))
          (when @dup
            (fail! "duplicate case test constant: `" (pr-str @dup) "` in `"
                   nm "`; a clause for it already exists")))))))

(defn- lookup-shape
  "What a call-position value is: :kw (keyword lookup), :lookup (symbol,
  vector, map or set lookup), :not-fn (never callable on either host) or
  :fn (an ordinary callable)."
  [x]
  (let [v (:val x)]
    (cond
      (and (= :lit (:op x)) (keyword? v)) :kw
      (and (= :lit (:op x))
           (or (symbol? v) (vector? v) (map? v) (set? v))) :lookup
      (and (= :lit (:op x))
           (or (number? v) (string? v) (char? v) (boolean? v) (nil? v))) :not-fn
      (contains? #{:vec :map :set} (:op x)) :lookup
      :else :fn)))

(defn- check-lookup-calls
  "A keyword, symbol, vector, map or set in call position is a lookup
  fn: both hosts reject the call with no arguments, and a lookup takes
  at most the collection and a default (keywords keep the round-13
  minimum -- jolt accepts a keyword call with extra arguments).  A
  number, string, character, boolean or nil is not a function on either
  host at any arity.  A book is never evaluated, so writ owns these
  contracts."
  [nm ast]
  (walk-ast ast
    (fn [n]
      (when (= :invoke (:op n))
        (let [shape (lookup-shape (:fn n))
              argc (count (:args n))]
          (cond
            (= shape :not-fn)
            (fail! "`" (pr-str (:val (:fn n))) "` in `" nm
                   "` is not a function; a number, string, character, "
                   "boolean or nil cannot be called")

            (and (= shape :lookup) (zero? argc))
            (fail! "a collection or symbol is called with no arguments in `" nm
                   "`; the collection to read is missing")

            (and (= shape :lookup) (> argc 2))
            (fail! "a lookup call in `" nm "` takes at most the collection "
                   "and a default but is passed " argc " arguments")

            (and (= shape :kw) (zero? argc))
            (fail! "a keyword is called with no arguments in `" nm
                   "`; the collection to read is missing")))))))

(defn- check-effects
  "Effect code is rejected like throw and interop: an effect fn or macro
  (l/effect-names) in call or value position, unqualified or spelled
  clojure.core/x.  A book name, parameter or local of the same name
  shadows the core one (lower already kept such a head unexpanded)."
  [nm params raw-ast shadow]
  (let [bound (into (conj (set shadow) (qname-of nm))
                    (comp (map qname-of) (remove nil?))
                    (concat params (binder-syms raw-ast)
                            (map :name (named-fns raw-ast))))
        effect! (fn [s]
                  (fail! "`" s "` in `" nm "` is effect code (eval/load, namespace "
                         "or var mutation, state, concurrency or I/O); writ checks "
                         "pure data-and-functions code only"))]
    (walk-ast raw-ast
      (fn [n]
        (when (and (ref? n) (l/host-member? (:name n)))
          (fail! "`" (:name n) "` is host interop or effect code; "
                 "writ checks pure data-and-functions code only"))
        (when (and (ref? n) (l/effect-head? (:name n) bound))
          (if (contains? l/interop-names (symbol (name (:name n))))
            (fail! "`" (:name n) "` is host interop or effect code; "
                   "writ checks pure data-and-functions code only")
            (effect! (:name n))))))))

(def pair-tails
  "Core fns whose variadic tail is key/value pairs, ported from typedclojure's
  clojure.core annotations, which type the tail as `(t/cat k v) :*`: name
  -> the fixed arguments before the pairs.  Both hosts throw on an odd
  tail."
  '{hash-map 0, array-map 0, sorted-map 0, sorted-map-by 1, assoc 1})

(defn- check-arity! [target ar n*]
  (when (or (< n* (:min ar))
            (and (some? (:max ar)) (> n* (:max ar))))
    (cond
      (nil? (:max ar))
      (fail! "`" target "` takes at least " (:min ar)
             " argument(s) but is passed " n*)
      (= (:min ar) (:max ar))
      (fail! "`" target "` takes " (:max ar)
             " argument(s) but is passed " n*)
      :else
      (fail! "`" target "` takes between " (:min ar) " and "
             (:max ar) " argument(s) but is passed " n*))))

(defn- check-pairs! [nm target n*]
  (when-let [fixed (get pair-tails target)]
    (let [tail (- n* fixed)]
      (when (and (pos? tail) (odd? tail))
        (if (= 'assoc target)
          (fail! "`assoc` in `" nm "` takes an even number of key/vals after "
                 "the map but is passed " tail)
          (fail! "`" target "` in `" nm "` is passed an odd number of map "
                 "entries; keys and values come in pairs"))))))

(defn- type-used! [c nm]
  (fail! "`" c "` in `" nm "` is a type; a type name is not a value or a fn"))

(defn- ctor-built! [c nm]
  (fail! "`" c "` in `" nm "` is a constructor; a constructor appears only in a "
         "`match` pattern -- w/data declares a type for the checker, and a book "
         "takes data apart, it does not build it"))

(defn- check-names [nm params body-ast ok shadow arities]
  ;; a book is one namespace: a name it binds shadows clojure.core for the
  ;; whole book, so core is disjoined by the book's own names and a forward
  ;; reference reads as the ordering error it is
  (let [core (if (seq shadow) (reduce disj core-names shadow) core-names)
        pset (into #{} (comp (map qname-of) (remove nil?)) (concat params (binder-syms body-ast)))
        ;; the defn's own signature is a known arity even outside a book
        ;; (w/defn checks through here with arities nil): a self-call must
        ;; match its own parameter vector, not the same-named core fn
        self-ar (let [ri (first (keep-indexed (fn [i p] (when (= '& p) i)) params))]
                  (if (some? ri)
                    {:min ri :max nil}
                    {:min (count params) :max (count params)}))
        local-fn-names (into #{} (map (fn [f] (qname-of (:name f)))) (named-fns body-ast))]
    (walk-ast body-ast
              (fn [n]
                (case (:op n)
                  ;; the ordering rule governs book-local names only:
                  ;; qualified symbols (wc/check-files, w/check) are
                  ;; host API, not book defs.  The host, effect and
                  ;; nested-definition gates are not ordering rules,
                  ;; so they run standalone too
                  :invoke
                  (do
                  ;; clojure.core/x is the core fn whatever the book binds
                  (when (and (= :ref (:op (:fn n)))
                             (= "clojure.core" (namespace (:name (:fn n)))))
                    (let [target (qname-of (:name (:fn n)))
                          n* (count (:args n))]
                      (when-let [ar (get core-arities target)]
                        (check-arity! (:name (:fn n)) ar n*))
                      (check-pairs! nm target n*)))
                  (when (and (= :ref (:op (:fn n)))
                             (nil? (namespace (:name (:fn n)))))
                    (let [target (qname-of (:name (:fn n)))]
                      (cond
                        (= target 'set!)
                        (fail! "`set!` mutates a var; writ checks pure code, "
                               "and an affine value cannot be mutated")

                        (contains? nested-def-heads (name target))
                        (fail! "`" target "` inside a body is not supported: "
                               "a book defines names at the top level only, in book order")

                        (= target 'var)
                        (do (when-not (= 1 (count (:args n)))
                              (fail! "Wrong number of args to var, had: "
                                     (count (:args n))))
                            (let [a (first (:args n))]
                              (when-not (and (map? a) (= :ref (:op a))
                                             (symbol? (:name a)))
                                (fail! "The argument to `var` must be a symbol"))))

                        ;; the JVM special forms typed.clj.analyzer parses
                        (or (contains? '#{throw new monitor-enter monitor-exit
                                        reify* deftype* case* import*} target)
                            (.startsWith (name target) "."))
                        (fail! "`" target "` is host interop or effect code; "
                               "writ checks pure data-and-functions code only"))
                      ;; a book is never evaluated, so writ owns the arity
                      ;; contract the host would enforce with a runtime
                      ;; ArityException -- book fns and ctors first, then
                      ;; the core table for names the book does not bind
                      ;; (a book-bound non-fn name is the book's value,
                      ;; never the core one).  No local binder or local fn
                      ;; shadows either table.
                      ;; w/data declares types for the checker only; a
                      ;; book takes data apart, it never builds it
                      (when (and (not (contains? pset target)) arities
                                 (:ctor (get arities target)))
                        (ctor-built! target nm))
                      (when (and (not (contains? pset target)) arities
                                 (:type (get arities target)))
                        (type-used! target nm))
                      (when-let [ar (and (not (contains? pset target))
                                         (not (contains? local-fn-names target))
                                         (or (and arities (get arities target))
                                             (when (= target (qname-of nm)) self-ar)
                                             (when-not (and shadow
                                                            (contains? shadow target))
                                               (get core-arities target))))]
                        (if (= ar :not-fn)
                          ;; a constant bound by an EARLIER def is not
                          ;; callable at any arity; a forward reference stays
                          ;; an ordering error, reported by the ok-gate below
                          (when (and (some? ok) (contains? ok target))
                            (fail! "`" target "` in `" nm "` is not a function; "
                                   "a constant defined in this book cannot be called"))
                          (check-arity! target ar (count (:args n)))))
                      ;; key/value pair tails of core fns the book does not bind
                      (when (and (not (contains? pset target))
                                 (not (contains? local-fn-names target))
                                 (not (and arities (get arities target)))
                                 (not= target (qname-of nm))
                                 (not (and shadow (contains? shadow target))))
                        (check-pairs! nm target (count (:args n)))))
                    (when (some? ok)
                      (let [target (qname-of (:name (:fn n)))]
                        (when (and (not (contains? pset target))
                                   (not (contains? local-fn-names target))
                                   (not (contains? core target))
                                   ;; (var x) reads a value, so x itself is
                                   ;; checked as a reference below
                                   (not= target 'var)
                                   (not (contains? ok target))
                                   (not= target (qname-of nm)))
                          (fail! "`" target "` is used in `" nm
                                 "` but is defined later or is not a known name; "
                                 "Bend's defs reference earlier names only"))))))
                  ;; a value position is a use like a call: a forward def
                  ;; reference must not slip through just because it is
                  ;; never invoked
                  :ref
                  (do
                  (when (and arities (nil? (namespace (:name n)))
                             (not (contains? pset (qname-of (:name n))))
                             (:ctor (get arities (qname-of (:name n)))))
                    (ctor-built! (qname-of (:name n)) nm))
                  (when (and arities (nil? (namespace (:name n)))
                             (not (contains? pset (qname-of (:name n))))
                             (:type (get arities (qname-of (:name n)))))
                    (type-used! (qname-of (:name n)) nm))
                  (when (some? ok)
                    (let [target (qname-of (:name n))]
                      (when (and (nil? (namespace (:name n)))
                                 (not (contains? '#{nil true false &} target))
                                 (not (contains? pset target))
                                 (not (contains? local-fn-names target))
                                 (not (contains? core target))
                                 (not (contains? ok target))
                                 (not= target (qname-of nm)))
                        (fail! "`" target "` is used in `" nm
                               "` but is defined later or is not a known name; "
                               "Bend's defs reference earlier names only")))))
                  nil)))))

;; --- law terms -----------------------------------------------------------

(defn- value-refs
  "Names referenced as values (not as call heads) in a raw AST."
  [ast]
  (let [acc (atom #{})]
    (letfn [(walk [a head?]
              (when (map? a)
                (when (and (ref? a) (not head?) (nil? (namespace (:name a))))
                  (swap! acc conj (:name a)))
                (if (= :invoke (:op a))
                  (do (walk (:fn a) true) (doseq [x (:args a)] (walk x false)))
                  (doseq [c (ast-children a)] (walk c false)))))]
      (walk ast false))
    @acc))

(defn check-law-term
  "Check one term of a law like code: calls obey book order and arity,
  effect code is rejected, case constants are distinct and lookups well
  formed.  A name in value position is a variable of the law (implicitly
  universal, or bound by a quantifier), so only call heads must resolve."
  [label form ok shadow arities law-names]
  (let [raw (binding [l/*locals* (into (set shadow) (value-refs (l/lower form)))]
              (l/lower form))
        vars (vec (value-refs raw))]
    (walk-ast raw (fn [n]
                    (when (contains? #{:recur :loop} (:op n))
                      (fail! "a law term in `" label "` cannot loop or recur; state "
                             "the iteration through a defn and cite that"))))
    (doseq [v vars]
      (when (contains? law-names v)
        (fail! "`" v "` in law `" label "` names a law or proof, which is not a value")))
    (check-effects label vars raw shadow)
    (check-case-constants label raw)
    (check-lookup-calls label raw)
    (check-names label vars (l/uniquify raw) ok shadow arities)))

;; --- entry ---------------------------------------------------------------

(defn defn-form?
  [form]
  (and (seq? form) (symbol? (first form)) (contains? #{"defn" "defn-"} (name (first form)))))

(defn- check-local-arities
  "A book is never evaluated, so writ owns the runtime ArityException
  contract for calls to local fns too: named local fns, let/loop binders
  initialized to fns (letfn lowers to those), and anonymous fns called
  directly.  Runs on the raw AST, where binder names and the references
  inside fn bodies agree (uniquify leaves cross-fn references raw).  A
  name that also appears as a fn parameter anywhere shadows with unknown
  arity -- the same flatness trade the book-fn gate makes -- and a local
  fn passed as a value is never arity-checked at its eventual call site."
  [nm raw-ast]
  (let [param-names (atom #{})
        ars (atom {})
        _ (walk-ast raw-ast
                    (fn [n]
                      (cond
                        (= :fn (:op n))
                        (do (doseq [p (remove nil? (:params n))]
                              (swap! param-names conj (qname-of p)))
                            (when (and (:name n) (:writ/arity n))
                              (swap! ars assoc (qname-of (:name n)) (:writ/arity n))))

                        (contains? #{:let :loop} (:op n))
                        (doseq [[b init] (:bindings n)]
                          (when (and (symbol? b) (:writ/arity init))
                            (swap! ars assoc (qname-of b) (:writ/arity init)))))))
        arities (reduce dissoc @ars @param-names)
        check! (fn [what ar n*]
                 (when (or (< n* (:min ar))
                           (and (some? (:max ar)) (> n* (:max ar))))
                   (if (nil? (:max ar))
                     (fail! what " takes at least " (:min ar)
                            " argument(s) but is passed " n*)
                     (fail! what " takes " (:max ar)
                            " argument(s) but is passed " n*))))]
    (walk-ast raw-ast
      (fn [n]
        (when (= :invoke (:op n))
          (cond
            (and (= :ref (:op (:fn n)))
                 (nil? (namespace (:name (:fn n)))))
            (when-let [ar (get arities (qname-of (:name (:fn n))))]
              (check! (str "`" (qname-of (:name (:fn n))) "`") ar (count (:args n))))

            (= :fn (:op (:fn n)))
            (when-let [ar (:writ/arity (:fn n))]
              (check! "an anonymous fn" ar (count (:args n))))))))))

(defn check-defn
  "Check one `defn` form.  `ok` is the set of names defined earlier in the
  book (nil skips the ordering rule); `shadow` is every name the book
  binds, which hides clojure.core book-wide.  Returns {:ok true} or throws."
  ([form] (check-defn form nil))
  ([form ok] (check-defn form ok nil))
  ([form ok shadow] (check-defn form ok shadow nil))
  ([form ok shadow arities] (check-defn form ok shadow arities nil))
   ([form ok shadow arities ctx]
    (let [[_ nm & tail] form
          _ (when-not (symbol? nm)
              (fail! "First argument to defn must be a symbol, had: `" nm "`"))
          _ (when (and (symbol? nm) (namespace nm))
              (fail! "Cannot defn namespace qualified symbol: `" nm
                     "`; a book is one namespace"))
          tail (if (string? (first tail)) (rest tail) tail)
          attrs (when (map? (first tail)) (first tail))
          tail (if attrs (rest tail) tail)
          params (first tail)
         _ (when-not (vector? params)
             (fail! (if (and (sequential? params) (seq params)
                               (vector? (first params)))
                           (str "`" nm "` is multi-arity; writ checks a single arity")
                           (str "`" nm "` requires a vector of parameters"))))
         _ (when (vector? params)
             (let [ri (first (keep-indexed (fn [i p] (when (= '& p) i)) params))]
               (when (and (some? ri)
                          (or (= ri (dec (count params)))
                              (not (symbol? (get params (inc ri))))
                              (= '& (get params (inc ri)))
                              (> (count params) (+ ri 2))))
                 (fail! "`" nm "`: a rest parameter must be followed by "
                        "exactly one rest name"))
         _ (when (vector? params)
             (doseq [p (remove #{'&} params)]
               (when (and (symbol? p) (not (l/valid-binding-symbol? p)))
                 (fail! "Bad binding form: `" p "`; a parameter "
                        "must be a simple symbol"))))))
         body (rest tail)
         _ (when (and (= ':- (first body)) (nil? (second body)))
             (fail! "`:-` in `" nm "` must be followed by a return type"))
         _ (when (vector? params)
             (doseq [i (range (count params))]
               (when (and (= ':- (get params i))
                          (or (= i (dec (count params)))
                              (= ':- (get params (inc i)))))
                 (fail! "`:-` in `" nm "` must be followed by a type"))))
         ;; the book's names and the params shadow macros while lowering
         raw-ast (binding [l/*locals* (into (conj (set shadow) nm)
                                            (comp (filter symbol?) (remove #{'&}))
                                            params)]
                   (l/lower (if (= 1 (count body)) (first body) (cons 'do body))))
         body-ast (l/uniquify raw-ast)
         marked? (boolean (or *descend-all* (:writ/descend attrs) (:writ/descend (meta nm))))]
     (check-param-dups nm (vec params))
     (check-recur-shape nm params body-ast)
     (check-effects nm params raw-ast shadow)
     (when *affine*
       (check-quantities nm params raw-ast body-ast)
       (check-overlaps nm params raw-ast)
       (check-captures nm params body-ast shadow))
     (check-case-constants nm raw-ast)
     (check-lookup-calls nm raw-ast)
     (check-local-cycles nm raw-ast)
     (check-termination nm params body-ast marked? shadow (:tenv ctx))
     (check-local-arities nm raw-ast)
     (when *affine* (check-fn-reuse nm params body-ast))
     (check-names nm params body-ast ok shadow arities)
     ;; the defn's own signature types its self-calls
     (let [tenv (or (:tenv ctx) {})
           self {:params (mapv #(ty/binder-type % tenv) (remove #{'&} params))
                 :ret (ty/binder-type nm tenv)}]
       (ty/check-types nm params (:tag (meta nm)) body-ast
                       (-> ctx
                           (assoc :tenv tenv :shadow shadow)
                           (update :sigs assoc (qname-of nm) self))))
     {:ok true})))
