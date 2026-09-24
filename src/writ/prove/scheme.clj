(ns writ.prove.scheme
  "What a proof is made of, shared by the prover's search and the proof
  checker: a law as goals under hypotheses, the cases of an inductive type
  and the induction hypotheses at its smaller values, hypotheses taken
  apart into facts, and earlier laws as rewrite rules.  The search decides
  which of these to use; writ.prove.check replays its choices with these
  same definitions and the rewriter, and nothing else."
  (:require [clojure.string :as str]
            [writ.prove.term :as t :refer [head]]
            [writ.prove.rewrite :as rw]
            [writ.prove.translate :as tr]))

;; --- goals -----------------------------------------------------------------------

(defn op? [p s] (and (seq? p) (symbol? (first p)) (= s (name (first p)))))

(defn split-foralls [p]
  (loop [p p, bs []]
    (if (op? p "forall")
      (let [[_ [x ty] body] p] (recur body (conj bs [x ty])))
      [bs p])))

(defn goal
  "{:hyps [term] :goals [term]} for a law body: `=>` adds its hypothesis,
  `and` asks for each part, anything else is a term that must be truthy."
  [tctx vars p]
  (let [tm #(tr/lower-term tctx vars %)]
    (cond
      (op? p "=>") (let [{:keys [hyps goals]} (goal tctx vars (nth p 2))]
                     {:hyps (into [(tm (nth p 1))] hyps) :goals goals})
      (op? p "and") (let [gs (map #(goal tctx vars %) (rest p))]
                      (when (some (comp seq :hyps) gs) (tr/outside! "an `=>` inside `and`"))
                      {:hyps [] :goals (vec (mapcat :goals gs))})
      (or (op? p "forall") (op? p "exists")) (tr/outside! (str "a nested `" (first p) "`"))
      :else {:hyps [] :goals [(tm p)]})))

;; --- cases of an inductive type ------------------------------------------------------

(defn plain [ty] (cond (symbol? ty) (symbol (name ty))
                        (seq? ty) (apply list (map plain ty))
                        :else ty))

(defn cases
  "The cases of variable v of type ty: [{:desc :value :types {var type}
  :smaller [term]}], or nil when ty is not inductive."
  [v ty tenv]
  (let [ty (plain ty)
        nm (fn [s] (symbol (str v "-" s)))]
    (cond
      (and (seq? ty) (contains? '#{List Vec} (first ty)))
      (let [el (second ty) h (nm "h") tl (nm "t")]
        (cond-> []
          (= 'List (first ty)) (conj {:desc (str v " = nil") :value t/tnil :types {} :smaller []})
          true (conj {:desc (str v " = ()") :value [:sq t/enil] :types {} :smaller []})
          true (conj {:desc (str v " = (" h " & " tl ")")
                      :value [:sq [:econs h tl]]
                      :types {h el tl {:elems el}}
                      :smaller (cond-> [[:sq tl] [:sq t/enil]]
                                 (= 'List (first ty)) (conj t/tnil))})))

      (= 'Nat ty)
      (let [p (nm "p")]
        [{:desc (str v " = 0") :value [:lit 0] :types {} :smaller []}
         {:desc (str v " = " p " + 1") :value [:lin 1 [[p 1]]] :types {p 'Nat} :smaller [p]}])

      (let [h (if (seq? ty) (first ty) ty)]
        (and (symbol? h) (get tenv h) (not (:tvar (get tenv h)))))
      (let [[h args] (if (seq? ty) [(first ty) (vec (rest ty))] [ty []])
            d (get tenv h)
            sub (zipmap (:params d) args)
            subst-ty (fn st [x] (cond (symbol? x) (get sub x x)
                                      (seq? x) (apply list (map st x))
                                      :else x))]
        (vec (for [[c info] (sort-by (comp str key) (:ctors d))
                   :let [fs (mapv subst-ty (:fields info))
                         vs (mapv #(nm (str (str/lower-case (str c)) (inc %))) (range (count fs)))]]
               {:desc (str v " = [:" c (apply str (map #(str " " %) vs)) "]")
                :value [:sq (t/elems-of (into [[:lit (keyword (str c))]] vs))]
                :types (zipmap vs fs)
                :smaller (vec (for [[x f] (map vector vs fs) :when (= (plain f) ty)] x))})))

      :else nil)))

;; --- recognizers ------------------------------------------------------------------
;; A law proved for every value of a type holds at a term only if the term
;; is of that type.  The prover's logic is untyped, like ACL2's: a type is
;; a hypothesis, and a recognizer states it.  Each recognizer takes a value
;; apart the way the type's cases do, so what it accepts is what a proof
;; over the type covers.

(def ^:private scalar-checks
  '{Bool boolean? String string? Char char? Keyword keyword? Symbol symbol?
    Float number? Double number?})

(def ^:private rec-var '%x)

(defn- type-var? [tenv ty]
  (or (= 'Any ty)
      (and (symbol? ty) (:tvar (get tenv ty)))
      (and (symbol? ty) (not (get tenv ty)) (not (contains? scalar-checks ty))
           (not (contains? '#{Nat Int Unit} ty)))))

(defn- rec-name [ty]
  (symbol "writ.prove.types"
          (str (-> (pr-str ty) (str/replace #"[\s()]+" "-") (str/replace #"^-|-$" "")) "?")))

(defn- conj-terms [cs]
  (if (empty? cs)
    [:lit true]
    (reduce (fn [a c] [:if c a [:lit false]]) (reverse cs))))

(defn recognizers
  "Recognizers for `types` (and the types their parts have) under tenv:
  {:names {type name} :defs {name def} :checks {type template} :lists
  #{name}}.  A template is a term in `%x` saying a value is of the type:
  :any for a type every value is of (a type variable), and no entry for a
  type with no recognizer (a set, a map, a fn), which only a variable of
  that type is known to be."
  [tenv types]
  (let [out (atom {:names {} :defs {} :checks {} :lists #{}})
        bad (atom #{})]
    (letfn [(check [ty e]
              (let [ty (plain ty)]
                (cond
                  (= 'Nat ty) [:if [:call 'integer? e] [:call '<= [:lit 0] e] [:lit false]]
                  (= 'Int ty) [:call 'integer? e]
                  (= 'Unit ty) [:call '= e t/tnil]
                  (contains? scalar-checks ty) [:call (scalar-checks ty) e]
                  (type-var? tenv ty) [:lit true]
                  :else (when-let [n (rec ty)] [:app n e]))))
            (rec [ty]
              (let [known (:names @out)]
                (if (contains? known ty)
                  (get known ty)
                  (let [n (rec-name ty)
                        _ (swap! out assoc-in [:names ty] n)
                        body (body-of ty rec-var)]
                    (if body
                      (do (swap! out assoc-in [:defs n]
                                 {:params [rec-var] :body body
                                  :recursive? (boolean (some #(and (= :app (head %)) (= n (second %)))
                                                             (t/subterms body)))})
                          n)
                      (do (swap! bad conj n) n))))))
            (body-of [ty x]
              (let [[h & args] (if (seq? ty) ty [ty])]
                (cond
                  (contains? '#{List Vec} h)
                  (when-let [c (check (first args) [:call 'first x])]
                    (swap! out update :lists conj (rec-name ty))
                    [:if [:call 'seq x]
                     [:if c [:app (rec-name ty) [:call 'rest x]] [:lit false]]
                     (if (= 'List h)
                       [:if [:call '= x t/tnil] [:lit true] [:call '= x [:sq t/enil]]]
                       [:call '= x [:sq t/enil]])])

                  (= 'Tuple h)
                  (let [cs (map-indexed (fn [i a] (check a [:call 'nth x [:lit i]])) args)]
                    (when (every? some? cs)
                      [:if [:call '= [:call 'count x] [:lit (count args)]] (conj-terms cs) [:lit false]]))

                  (and (symbol? h) (get tenv h) (:ctors (get tenv h)))
                  (let [d (get tenv h)
                        sub (zipmap (:params d) args)
                        st (fn st [y] (cond (symbol? y) (get sub y y) (seq? y) (apply list (map st y)) :else y))
                        arms (for [[c info] (sort-by (comp str key) (:ctors d))
                                   :let [fs (map st (:fields info))
                                         cs (map-indexed (fn [i f] (check f [:call 'nth x [:lit (inc i)]])) fs)]]
                               (when (every? some? cs)
                                 [[:call '= [:call 'first x] [:lit (keyword (str c))]]
                                  [:if [:call '= [:call 'count x] [:lit (inc (count fs))]] (conj-terms cs) [:lit false]]]))]
                    (when (every? some? arms)
                      (reduce (fn [e [c b]] [:if c b e]) [:lit false] (reverse arms))))

                  :else nil)))]
      (doseq [ty types] (check ty rec-var))
      ;; a recognizer whose type, or a part's, has none is dropped, and so
      ;; is every one that calls it
      (loop []
        (let [{:keys [defs]} @out
              gone (set (for [[n d] defs
                              :when (or (contains? @bad n)
                                        (some #(and (= :app (head %)) (contains? @bad (second %))
                                                    (not= n (second %)))
                                              (t/subterms (:body d))))]
                          n))]
          (when (seq gone)
            (swap! bad into gone)
            (swap! out update :defs #(apply dissoc % gone))
            (recur))))
      (let [{:keys [names] :as o} @out
            all (into (set types) (keys names))]
        (assoc o
               :names (into {} (remove (fn [[_ n]] (contains? @bad n))) names)
               :lists (set (remove #(contains? @bad %) (:lists o)))
               :checks (into {} (for [ty all
                                      :let [ty (plain ty)
                                            c (cond (type-var? tenv ty) :any
                                                    (contains? '#{Nat Int} ty) nil
                                                    :else (let [c (check ty rec-var)]
                                                            (when-not (and (= :app (head c)) (contains? @bad (second c)))
                                                              c)))]
                                      :when c]
                                  [ty c])))))))

;; --- goals under hypotheses ---------------------------------------------------

(defn truthy? [x]
  (case (head x) :lit (not (false? (second x))) (:sq :fn :cfn) true false))

(defn falsy? [x] (or (= t/tnil x) (= [:lit false] x)))

(defn solve-eq
  "For d = 0, a variable and the term it equals, when some variable has
  coefficient 1 or -1 in d."
  [d]
  (let [[c pairs] (cond (= :lin (head d)) [(second d) (nth d 2)]
                        (symbol? d) [0 [[d 1]]]
                        :else [nil nil])]
    (when c
      (first (for [[x k] pairs
                   :when (and (symbol? x) (contains? #{1 -1} k))
                   :let [others (remove #(= x (first %)) pairs)
                         ;; x*k + c + others = 0  =>  x = -(c + others)/k
                         m {:c (- (* k c)) :m (into {} (map (fn [[a j]] [a (- (* k j))])) others)}]]
               [x (rw/lin->term m)])))))

(defn assume-hyp
  "[ctx vacuous?] with hypothesis h, already normalised, taken as true.
  (if c a false) holds when c and a do, as does (if c a c), the shape
  `and` lowers to; (if c false b) holds when c does not and b does.  So
  each part becomes a fact of its own."
  [ctx h]
  (cond
    (truthy? h) [ctx false]
    (falsy? h) [ctx true]
    (and (= :if (head h)) (or (falsy? (nth h 3)) (= (nth h 1) (nth h 3))))
    (let [[c1 v1] (assume-hyp ctx (nth h 1))]
      (if v1 [c1 true] (assume-hyp c1 (rw/normalize c1 (nth h 2)))))
    (and (= :if (head h)) (falsy? (nth h 2)))
    (let [c1 (rw/assume ctx (nth h 1) false)]
      (assume-hyp c1 (rw/normalize c1 (nth h 3))))
    :else [(rw/assume ctx h true) false]))

(defn subst-all
  "opts, g and hyps with the variable substitution m applied throughout,
  the induction hypotheses included."
  [opts g hyps m]
  (let [s #(t/subst % m)]
    [(update opts :ih (fn [ih] (mapv (fn [i] (-> i (update :lhs s) (update :rhs s)
                                                (update :hyp #(some-> % s))))
                                     ih)))
     (s g) (mapv s hyps)]))

(defn instance [g-terms v value]
  (mapv #(t/subst % {v value}) g-terms))

(defn ih-for
  "The law at a smaller value, as rewrites: an equality rewrites its left
  side to its right, anything else rewrites to true."
  [opts {:keys [hyps goals]} v smaller]
  (let [free (:ih-free opts)
        ;; a variable the law is quantified over as well stays free in the
        ;; hypothesis: renamed to a pattern variable, and held to its type
        ren (into {} (map (fn [[x _]] [x (symbol (str "?ih%" x))])) free)
        pvars (set (vals ren))
        nctx (rw/context (-> opts (dissoc :ih)
                             (update :types merge (into {} (map (fn [[x ty]] [(ren x) ty])) free))))
        n #(rw/normalize nctx %)
        type-hyps (for [[x ty] free
                        :when (contains? '#{Nat Int} ty)]
                    (cond-> [:call 'integer? (ren x)]
                      (= 'Nat ty) (as-> h [:if h [:call '<= [:lit 0] (ren x)] [:lit false]])))
        hyp (when (seq (concat hyps type-hyps))
              (reduce (fn [a b] [:if a b [:lit false]])
                      (concat (map #(t/subst % ren) hyps) type-hyps)))]
    (vec (for [s smaller
               g goals
               :let [gi (t/subst (t/subst g ren) {v s})
                     hi (some-> hyp (t/subst {v s}))]]
           (cond-> (if (and (= :call (head gi)) (= '= (second gi)) (= 4 (count gi)))
                     {:hyp hi :lhs (n (nth gi 2)) :rhs (n (nth gi 3))}
                     {:hyp hi :lhs (n gi) :rhs [:lit true]})
             (seq pvars) (assoc :vars pvars
                                :types (into {} (map (fn [[x ty]] [(ren x) (plain ty)])) free)))))))

(defn useful-ih
  "The hypotheses that can rewrite something: not one whose left side
  normalised to a bare variable, which would match every term."
  [ihs]
  (vec (remove (comp symbol? :lhs) ihs)))

(defn replace-term [t from to]
  (cond (= t from) to
        (and (vector? t) (not (contains? #{:lit :cfn} (head t))))
        (if (= :lin (head t))
          [:lin (second t) (mapv (fn [[a k]] [(replace-term a from to) k]) (nth t 2))]
          (into [(head t)] (map #(replace-term % from to)) (rest t)))
        :else t))

(defn lemma-rules
  "An earlier proved law as rewrite rules: each equality rewrites its left
  side to its right, anything else rewrites to true, under the law's
  hypotheses.  Its variables are renamed apart and become pattern
  variables; its sides are normalised the way a goal's subterms are."
  [{:keys [name prop]} defs tenv own]
  (try
    (let [[bs body] (split-foralls prop)
          ren (into {} (map (fn [[x _]] [x (symbol (str "?" name "%" x))])) bs)
          vars (mapv first bs)
          g (goal (tr/context own) vars body)
          types (into {} (map (fn [[x ty]] [(ren x) (plain ty)])) bs)
          ctx (rw/context {:defs defs :tenv tenv :types types})
          n #(rw/normalize ctx (t/subst % ren))
          hyp (when (seq (:hyps g))
                (t/subst (reduce (fn [a b] [:if a b [:lit false]]) (:hyps g)) ren))]
      (when (seq bs)
        (vec (for [gl (:goals g)
                   :let [calls (fn [x] (count (filter #(= :app (head %)) (t/subterms x))))
                         [l r] (if (and (= :call (head gl)) (= '= (second gl)) (= 4 (count gl)))
                                 (let [a (n (nth gl 2)) b (n (nth gl 3))]
                                   ;; rewrite toward fewer calls of definitions:
                                   ;; (= (+ a b) (total ...)) rewrites the call
                                   (if (< (calls a) (calls b)) [b a] [a b]))
                                 [(n gl) [:lit true]])]
                   :when (not (or (symbol? l) (= :lin (head l))))]
               {:name name :vars (set (vals ren)) :types types :hyp hyp :lhs l :rhs r}))))
    (catch clojure.lang.ExceptionInfo _ nil)))


;; --- the steps a proof takes ------------------------------------------------------

(defn case-context
  "[ctx vacuous? n]: the hyps taken as facts, the induction hypotheses read
  under them, and the goal g normalised there.  vacuous? when a hypothesis
  is false, and then there is nothing to prove."
  [opts g hyps]
  (let [take-all (fn [ctx0 hs]
                   (reduce (fn [[c vac] h]
                             (if vac [c vac] (assume-hyp c (rw/normalize c h))))
                           [ctx0 false] hs))
        [ctx vacuous] (take-all (rw/context (dissoc opts :ih)) hyps)
        ;; a hypothesis read before a later one decided its test (an or
        ;; whose first case a split ruled out) is read again under all of
        ;; them
        [ctx vacuous] (if vacuous [ctx vacuous] (take-all ctx hyps))
        ctx (assoc ctx :ih (mapv (fn [i] (update i :lhs #(rw/normalize ctx %))) (:ih opts)))
        ctx (assoc ctx :memo (atom {}) :stuck (atom #{}) :int-memo (atom {}))]
    [ctx vacuous (when-not vacuous (rw/normalize ctx g))]))

(defn data-cases
  "One case per constructor of v's data type, as [[value types] ...]; nil
  when v is not of a data type.  A case split, not induction: no case
  gets a hypothesis."
  [opts v]
  (let [ty (get-in opts [:types v])
        h (if (seq? ty) (first ty) ty)
        d (when (symbol? h) (get-in opts [:tenv h]))]
    (when (and d (:ctors d) (not (:tvar d)))
      (mapv (juxt :value :types) (cases v ty (:tenv opts))))))

(defn list-cases
  "The two shapes of an unknown list of elements v: empty, and a head and
  a tail, as [[value types] [value types]]."
  [opts v]
  (let [el (:elems (get-in opts [:types v]))
        h (symbol (str v "h")) tl (symbol (str v "t"))]
    [[t/enil {}] [[:econs h tl] {h el tl {:elems el}}]]))

(defn induction-case
  "[opts gi] for case c of induction on v: its variables typed, the law at
  the case's smaller values as hypotheses, and the goals at the case."
  [opts g v c]
  (let [opts* (-> opts (update :types merge (:types c)) (assoc :ih []))
        opts* (assoc opts* :ih (useful-ih (ih-for opts* g v (:smaller c))))]
    [opts* {:hyps (instance (:hyps g) v (:value c))
            :goals (instance (:goals g) v (:value c))}]))

(defn- eq-goal? [g] (and (= :call (head g)) (= '= (second g)) (= 4 (count g))))

(defn generalization
  "The goal of generalising: equality hypothesis ih used right to left,
  then recursive call `call` replaced by fresh variable ys throughout.
  nil when ih is not an equality, or the call does not occur."
  [opts {:keys [hyps goals]} {:keys [lhs rhs hyp]} call ys]
  (when (and (nil? hyp) (not= [:lit true] rhs))
    (let [ctx (rw/context (dissoc opts :ih))
          n* #(rw/normalize ctx %)
          ;; an equality keeps its shape, each side normalised, so the
          ;; induction on the new variable gets an equation to rewrite by
          n (fn [g] (if (eq-goal? g) [:call '= (n* (nth g 2)) (n* (nth g 3))] (n* g)))
          goals* (mapv #(replace-term (n %) rhs lhs) goals)]
      (when (some #(some #{call} (t/subterms %)) goals*)
        {:hyps (mapv #(replace-term (n %) call ys) hyps)
         :goals (mapv #(replace-term % call ys) goals*)}))))

(defn accumulator-goals
  "For a fold `call` from 0 and the same fold `c-acc` from integer acc:
  that it gives an integer, and that it is acc plus the fold from 0."
  [call c-acc acc]
  [{:hyps [] :goals [[:call 'integer? c-acc]]}
   {:hyps [] :goals [[:call '= c-acc [:call '+ acc call]]]}])

(defn accumulator-rule
  "A proved accumulator goal as a rewrite rule, its acc and law variables
  free, acc held to be an integer."
  [opts nm goal acc law-vars]
  (let [ren (into {} (map (fn [x] [x (symbol (str "?" nm "%" x))])) (cons acc law-vars))
        g (t/subst (first (:goals goal)) ren)
        ctx (rw/context (-> opts (dissoc :ih)
                            (update :types merge
                                    (into {} (map (fn [[x v]] [v (if (= x acc) 'Int (get-in opts [:types x]))]))
                                          ren))))
        n #(rw/normalize ctx %)
        hyp [:call 'integer? (ren acc)]
        types (into {} (keep (fn [[x v]] (when-let [ty (if (= x acc) 'Int (get-in opts [:types x]))]
                                           [v (plain ty)])))
                    ren)]
    (if (= 'integer? (second g))
      {:name nm :vars (set (vals ren)) :types types :hyp hyp :lhs (n g) :rhs [:lit true]}
      {:name nm :vars (set (vals ren)) :types types :hyp hyp :lhs (n (nth g 2)) :rhs (n (nth g 3))})))
