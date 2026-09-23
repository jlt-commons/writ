(ns writ.prove
  "Prove writ.spec laws from the implementation's source.

  A law's terms and the target's definitions are translated to terms
  (writ.prove.translate) and rewritten to normal form (writ.prove.rewrite).
  The search tries, in order: the law as it stands; then structural
  induction on each quantified variable of an inductive type -- a list is
  nil, empty or a head and a tail, a Nat is 0 or p + 1, a datatype one case
  per constructor -- with the law at every smaller value as a hypothesis.
  Inside each case an open integer comparison is split into its two
  outcomes; an equality that holds is substituted away.

  A proof holds for every input on which the law's terms return, as with
  Typed Clojure; writ still runs every law, which catches the inputs where
  a term throws.  A proof that never unfolds one of the target's own
  definitions says nothing about the code, and is not reported."
  (:require [clojure.string :as str]
            [writ.prove.term :as t :refer [head]]
            [writ.prove.rewrite :as rw]
            [writ.prove.translate :as tr]))

;; --- goals -----------------------------------------------------------------------

(defn- op? [p s] (and (seq? p) (symbol? (first p)) (= s (name (first p)))))

(defn- split-foralls [p]
  (loop [p p, bs []]
    (if (op? p "forall")
      (let [[_ [x ty] body] p] (recur body (conj bs [x ty])))
      [bs p])))

(defn- goal
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

(defn- plain [ty] (cond (symbol? ty) (symbol (name ty))
                        (seq? ty) (apply list (map plain ty))
                        :else ty))

(defn- cases
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

;; --- proving a goal ---------------------------------------------------------------------

(defn- truthy? [x]
  (case (head x) :lit (not (false? (second x))) (:sq :fn :cfn) true false))

(defn- split-candidate [n]
  (first (filter #(contains? #{:le :ieq} (head %)) (rw/open-conditions n))))

(defn- solve-eq
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

(def ^:dynamic *stuck*
  "When bound to an atom, collects the goals a search could not close, as
  {:goal :facts}, for debugging the prover."
  nil)

(defn- falsy? [x] (or (= t/tnil x) (= [:lit false] x)))

(defn- assume-hyp
  "[ctx vacuous?] with hypothesis h, already normalised, taken as true.
  (if c a false) holds when c and a do, and (if c false b) when c does not
  and b does, so each part becomes a fact of its own."
  [ctx h]
  (cond
    (truthy? h) [ctx false]
    (falsy? h) [ctx true]
    (and (= :if (head h)) (falsy? (nth h 3)))
    (let [[c1 v1] (assume-hyp ctx (nth h 1))]
      (if v1 [c1 true] (assume-hyp c1 (rw/normalize c1 (nth h 2)))))
    (and (= :if (head h)) (falsy? (nth h 2)))
    (let [c1 (rw/assume ctx (nth h 1) false)]
      (assume-hyp c1 (rw/normalize c1 (nth h 3))))
    :else [(rw/assume ctx h true) false]))

(defn- elems-var
  "A variable of the goal that stands for an unknown list of elements, one
  a case split could reveal."
  [opts n]
  (first (filter #(map? (get-in opts [:types %])) (sort-by str (t/vars n)))))

(declare prove-goal)

(defn- subst-all
  "opts, g and hyps with the variable substitution m applied throughout,
  the induction hypotheses included."
  [opts g hyps m]
  (let [s #(t/subst % m)]
    [(update opts :ih (fn [ih] (mapv (fn [i] (-> i (update :lhs s) (update :rhs s)
                                                (update :hyp #(some-> % s))))
                                     ih)))
     (s g) (mapv s hyps)]))

(defn- by-list-cases
  "Prove g by splitting element-list variable v into empty and a head and
  a tail.  Not induction: the tail gets no hypothesis of its own."
  [opts g hyps depth v]
  (let [el (:elems (get-in opts [:types v]))
        h (symbol (str v "h")) tl (symbol (str v "t"))
        prove (fn [value types]
                (let [[o g* hs] (subst-all (update opts :types merge types) g hyps {v value})]
                  (prove-goal o g* hs (dec depth))))
        empty (prove t/enil {})
        more (when empty (prove [:econs h tl] {h el tl {:elems el}}))]
    (when (and empty more)
      {:by :list-cases :on v :empty empty :cons more})))

(defn- prove-goal
  "Prove boolean term g under hyps, splitting on open integer comparisons,
  and on the shape of an unknown list of elements.  Returns a trace or nil."
  [opts g hyps depth]
  (let [[ctx vacuous] (reduce (fn [[c vac] h]
                                (if vac
                                  [c vac]
                                  (assume-hyp c (rw/normalize c h))))
                              [(rw/context (dissoc opts :ih)) false] hyps)
        ;; the induction hypotheses, read under the facts of this case
        ctx (assoc ctx :ih (mapv (fn [i] (update i :lhs #(rw/normalize ctx %))) (:ih opts)))
        ctx (assoc ctx :memo (atom {}) :stuck (atom #{}))
        n (when-not vacuous (rw/normalize ctx g))]
    (swap! (:unfolded opts) into @(:unfolded ctx))
    (when (and *stuck* (not vacuous) (not (truthy? n)) (or (zero? depth) (nil? (split-candidate n))))
      (swap! *stuck* conj {:goal n :facts (:facts ctx)}))
    (cond
      vacuous {:by :hypothesis-false}
      (truthy? n) {:by :rewriting}
      (zero? depth) nil
      (nil? (split-candidate n))
      (when-let [v (elems-var opts n)]
        (by-list-cases opts g hyps depth v))
      :else
      (when-let [c (split-candidate n)]
        (let [yes (if-let [[x v] (and (= :ieq (head c)) (solve-eq (second c)))]
                    (let [[o g* hs] (subst-all opts g hyps {x v})]
                      (prove-goal o g* hs (dec depth)))
                    (prove-goal opts g (conj hyps c) (dec depth)))
              no (prove-goal opts g (conj hyps [:call 'not c]) (dec depth))]
          (when (and yes no) {:by :split :on c :then yes :else no}))))))

(defn- instance [g-terms v value]
  (mapv #(t/subst % {v value}) g-terms))

(defn- ih-for
  "The law at a smaller value, as rewrites: an equality rewrites its left
  side to its right, anything else rewrites to true."
  [opts {:keys [hyps goals]} v smaller]
  (let [nctx (rw/context (dissoc opts :ih))
        n #(rw/normalize nctx %)
        hyp (when (seq hyps)
              (reduce (fn [a b] [:if a b [:lit false]]) hyps))]
    (vec (for [s smaller
               g goals
               :let [gi (t/subst g {v s})
                     hi (some-> hyp (t/subst {v s}))]]
           (if (and (= :call (head gi)) (= '= (second gi)) (= 4 (count gi)))
             {:hyp hi :lhs (n (nth gi 2)) :rhs (n (nth gi 3))}
             {:hyp hi :lhs (n gi) :rhs [:lit true]})))))

(defn- prove-all
  "Prove every goal (under the hyps) in one context of opts."
  [opts {:keys [hyps goals]}]
  (let [ps (mapv #(prove-goal opts % hyps 8) goals)]
    (when (every? some? ps) ps)))

(defn- replace-term [t from to]
  (cond (= t from) to
        (and (vector? t) (not (contains? #{:lit :cfn} (head t))))
        (if (= :lin (head t))
          [:lin (second t) (mapv (fn [[a k]] [(replace-term a from to) k]) (nth t 2))]
          (into [(head t)] (map #(replace-term % from to)) (rest t)))
        :else t))

(declare by-induction)

(defn- by-generalizing
  "Prove an induction case by using an equality hypothesis the other way
  round, then generalising the recursive call it brought in to a fresh
  variable, and proving that more general goal by induction on it.  The
  goal holds for every value of the variable, so for the call's value
  too: generalising is always sound, only sometimes too strong."
  [opts {:keys [hyps goals]} smaller-vars]
  (when-not (:generalized? opts)
    (let [ctx (rw/context (dissoc opts :ih))
          n* #(rw/normalize ctx %)
          ;; an equality keeps its shape, each side normalised, so the
          ;; induction on the new variable gets an equation to rewrite by
          n (fn [g] (if (and (= :call (head g)) (= '= (second g)) (= 4 (count g)))
                      [:call '= (n* (nth g 2)) (n* (nth g 3))]
                      (n* g)))]
      (first
        (for [{:keys [lhs rhs hyp]} (:ih opts)
              :when (and (nil? hyp) (not= [:lit true] rhs))
              :let [goals* (mapv #(replace-term (n %) rhs lhs) goals)
                    calls (for [gl goals*, x (t/subterms gl)
                                :when (and (= :app (head x))
                                           (get-in opts [:rets (second x)])
                                           (some (set smaller-vars) (t/vars x)))]
                            x)]
              call (distinct calls)
              :let [ys (symbol (str "gen" (count (t/vars call))))
                    ty (get-in opts [:rets (second call)])
                    g* {:hyps (mapv #(replace-term (n %) call ys) hyps)
                        :goals (mapv #(replace-term % call ys) goals*)}
                    opts* (-> opts (assoc :generalized? true :ih [])
                              (update :types assoc ys ty))
                    p (or (prove-all opts* g*) (by-induction opts* g* ys ty))]
              :when p]
          {:by :generalizing :on (t/show call) :as ys :proof p})))))

(defn- by-induction [opts g v ty]
  (when-let [cs (cases v ty (:tenv opts))]
    (let [steps (for [c cs]
                  (let [opts* (-> opts
                                  (update :types merge (:types c))
                                  (assoc :ih []))
                        opts* (assoc opts* :ih (ih-for opts* g v (:smaller c)))
                        gi {:hyps (instance (:hyps g) v (:value c))
                            :goals (instance (:goals g) v (:value c))}]
                    [c (or (prove-all opts* gi)
                           (by-generalizing opts* gi (keys (:types c))))]))]
      (when (every? (comp some? second) steps)
        {:by :induction :on v
         :cases (mapv (fn [[c p]] {:case (:desc c) :proof p}) steps)}))))

(defn- case-vars [trace]
  (distinct (keep (fn [x] (when (and (map? x) (= :list-cases (:by x))) (:on x)))
                  (tree-seq coll? seq trace))))

(defn- conditions [trace]
  (distinct (keep (fn [x] (when (and (map? x) (= :split (:by x))) (:on x)))
                  (tree-seq coll? seq trace))))

(defn summary
  "A proof trace in one line."
  [trace]
  (let [on (->> (tree-seq coll? seq trace)
                (keep #(when (and (map? %) (= :induction (:by %))) (:on %)))
                first)
        cs (map (comp pr-str t/show) (conditions trace))]
    (str (if on (str "by induction on " on) "by rewriting")
         (when (seq cs) (str ", splitting on " (str/join " and " cs)))
         (when-let [vs (seq (case-vars trace))]
           (str ", with cases on " (str/join " and " vs)))
         (when-let [gs (seq (distinct (keep (fn [x] (when (and (map? x) (= :generalizing (:by x)))
                                                       (:on x)))
                                           (tree-seq coll? seq trace))))]
           (str ", generalising " (str/join " and " (map pr-str gs)))))))

(defn- lemma-rules
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
                   :let [[l r] (if (and (= :call (head gl)) (= '= (second gl)) (= 4 (count gl)))
                                 [(n (nth gl 2)) (n (nth gl 3))]
                                 [(n gl) [:lit true]])]
                   :when (not (symbol? l))]
               {:name name :vars (set (vals ren)) :hyp hyp :lhs l :rhs r}))))
    (catch clojure.lang.ExceptionInfo _ nil)))

(defn prove-law
  "Try to prove a law.  prop is the desugared law, its names qualified;
  defs are the translated definitions; target the implementation's ns;
  lemmas are the laws proved before it, as {:name :prop}.
  Returns {:proved true :trace :summary :lemmas} or {:proved false :reason}."
  [{:keys [prop defs tenv target own fuel lemmas rets]}]
  (try
    (let [[bs body] (split-foralls prop)
          vars (mapv first bs)
          tctx (tr/context own)
          g (goal tctx vars body)
          unfolded (atom #{})
          lemmas-used (atom #{})
          opts {:defs defs :tenv tenv :types (into {} (map (fn [[x ty]] [x (plain ty)])) bs)
                :unfolded unfolded :fuel (or fuel 20000) :lemmas-used lemmas-used
                :rets (or rets {})
                :lemmas (vec (mapcat #(lemma-rules % defs tenv own) lemmas))}
          attempt (fn [f] (reset! unfolded #{}) (reset! lemmas-used #{})
                    (let [r (f)] [r @unfolded]))
          tries (concat [#(some->> (prove-all opts g) (hash-map :by :cases :proofs))]
                        (for [[v ty] bs] #(by-induction opts g v ty)))
          [trace used] (or (first (filter first (map attempt tries))) [nil #{}])
          target-used (filter #(= (str target) (namespace %)) used)]
      (cond
        (nil? trace) {:proved false :reason "no proof found"}
        (empty? target-used) {:proved false :reason "the proof does not use the code"}
        :else {:proved true :trace trace
               :summary (str (summary trace)
                             (when (seq @lemmas-used)
                               (str ", citing " (str/join ", " (sort @lemmas-used)))))
               :lemmas (vec (sort @lemmas-used))}))
    (catch clojure.lang.ExceptionInfo e
      (cond
        (tr/outside-reason e) {:proved false :reason (ex-message e)}
        (:writ.prove.rewrite/fuel (ex-data e)) {:proved false :reason "the search ran out of fuel"}
        :else (throw e)))))

(defn definitions
  "Translate the defns of the target and the spec: [defs own].  pairs is
  [[ns-sym forms] ...]; each ns reads its own plain names first."
  [pairs]
  (let [qualified (into {} (for [[k v] (tr/own-names pairs) :when (namespace k)] [k v]))
        defs (into {}
                   (for [[ns-sym forms] pairs]
                     (let [own (merge qualified (into {} (for [[k v] (tr/own-names [[ns-sym forms]])
                                                               :when (nil? (namespace k))]
                                                           [k v])))]
                       (tr/defs-of (tr/context own) ns-sym forms))))]
    [defs qualified]))
