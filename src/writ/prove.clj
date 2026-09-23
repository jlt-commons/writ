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
            [writ.prove.translate :as tr]
            [writ.prove.check :as check]
            [writ.prove.scheme :as sc :refer [split-foralls goal plain cases truthy? falsy?
                                               solve-eq assume-hyp subst-all instance ih-for
                                               useful-ih replace-term lemma-rules]]))

;; --- proving a goal ---------------------------------------------------------------------
;; Every step records what the checker needs to replay it: writ.prove.check
;; follows the trace with writ.prove.scheme and the rewriter, and searches
;; for nothing.

(defn- split-candidate [n]
  (first (filter #(contains? #{:le :ieq} (head %)) (rw/open-conditions n))))

(def ^:dynamic *stuck*
  "When bound to an atom, collects the goals a search could not close, as
  {:goal :facts}, for debugging the prover."
  nil)

(defn- elems-var
  "A variable of the goal that stands for an unknown list of elements, one
  a case split could reveal."
  [opts n]
  (first (filter #(map? (get-in opts [:types %])) (sort-by str (t/vars n)))))

(declare prove-goal)

(defn- by-list-cases
  "Prove g by splitting element-list variable v into empty and a head and
  a tail.  Not induction: the tail gets no hypothesis of its own."
  [opts g hyps depth v]
  (let [[[ev et] [cv ct]] (sc/list-cases opts v)
        prove (fn [value types]
                (let [[o g* hs] (subst-all (update opts :types merge types) g hyps {v value})]
                  (prove-goal o g* hs (dec depth))))
        empty (prove ev et)
        more (when empty (prove cv ct))]
    (when (and empty more)
      {:by :list-cases :on v :empty empty :cons more})))

(defn- prove-goal
  "Prove boolean term g under hyps, splitting on open integer comparisons,
  and on the shape of an unknown list of elements.  Returns a trace or nil."
  [opts g hyps depth]
  (let [[ctx vacuous n] (sc/case-context opts g hyps)]
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

(defn- prove-all
  "Prove every goal (under the hyps) in one context of opts."
  [opts {:keys [hyps goals]}]
  (let [ps (mapv #(prove-goal opts % hyps 8) goals)]
    (when (every? some? ps) ps)))

(declare by-induction)

(defn- by-generalizing
  "Prove an induction case by using an equality hypothesis the other way
  round, then generalising the recursive call it brought in to a fresh
  variable, and proving that more general goal by induction on it.  The
  goal holds for every value of the variable, so for the call's value
  too: generalising is always sound, only sometimes too strong.  The
  variable ranges over the call's signed return type."
  [opts gi smaller-vars]
  (when-not (:generalized? opts)
    (first
      (for [[i ih] (map-indexed vector (:ih opts))
            :let [goals* (when (and (nil? (:hyp ih)) (not= [:lit true] (:rhs ih)))
                           (let [ctx (rw/context (dissoc opts :ih))]
                             (mapv #(replace-term (rw/normalize ctx %) (:rhs ih) (:lhs ih))
                                   (:goals gi))))]
            call (distinct (for [gl goals*, x (t/subterms gl)
                                 :when (and (= :app (head x))
                                            (get-in opts [:rets (second x)])
                                            (some (set smaller-vars) (t/vars x)))]
                             x))
            :let [ys (symbol (str "gen" (count (t/vars call))))
                  ty (get-in opts [:rets (second call)])
                  g* (sc/generalization opts gi ih call ys)
                  opts* (-> opts (assoc :generalized? true :ih []) (update :types assoc ys ty))
                  p (when g* (or (prove-all opts* g*) (by-induction opts* g* ys ty)))]
            :when p]
        {:by :generalizing :ih i :call call :as ys :ty ty :on (t/show call) :proof p}))))

(defn- by-induction [opts g v ty]
  (when-let [cs (cases v ty (:tenv opts))]
    (let [steps (for [c cs]
                  (let [[opts* gi] (sc/induction-case opts g v c)]
                    [c (or (prove-all opts* gi)
                           (by-generalizing (dissoc opts* :ih-free) gi (keys (:types c))))]))]
      (when (every? (comp some? second) steps)
        {:by :induction :on v :ty (plain ty)
         :cases (mapv (fn [[c p]] {:case (:desc c) :proof p}) steps)}))))

(defn- fuelled
  "f's result, or nil when it runs out of fuel."
  [f]
  (try (f)
       (catch clojure.lang.ExceptionInfo e
         (if (:writ.prove.rewrite/fuel (ex-data e)) nil (throw e)))))

(def synthetic-lemmas
  "The prover's own lemmas, which are not laws of the spec."
  '#{accumulator-is-an-integer accumulator-adds})

(defn- plus-of?
  "Is t the accumulator p grown by addition: (+ p e), (+ e p) or (inc p)?"
  [t p]
  (and (= :call (head t))
       (or (and (= 'inc (second t)) (= p (nth t 2 nil)))
           (and (= '+ (second t)) (= 4 (count t)) (some #{p} (drop 2 t))))))

(defn- accumulators
  "Calls in terms that fold with + into an accumulator starting at 0: a
  recursive definition whose recursive calls grow parameter i by
  addition, called with 0 there, and a reduce by such a fn from 0.  Each
  is {:call c :with (fn [acc] c-with-acc)}."
  [opts terms]
  (distinct
    (for [x (mapcat t/subterms terms)
          r (case (head x)
              :app (let [d (get-in opts [:defs (second x)])
                         args (vec (drop 2 x))
                         rec (filter #(and (= :app (head %)) (= (second x) (second %)))
                                     (t/subterms (:body d)))]
                     (when (and (:recursive? d) (seq rec))
                       (for [i (range (count args))
                             :when (and (= [:lit 0] (nth args i))
                                        (every? #(plus-of? (nth % (+ 2 i)) (nth (:params d) i)) rec))]
                         {:call x :with (fn [acc] (assoc x (+ 2 i) acc))})))
              :call (when (and (= 'reduce (second x)) (= 5 (count x)) (= [:lit 0] (nth x 3)))
                      (let [f (nth x 2)]
                        (when (or (= [:cfn '+] f)
                                  (and (= :fn (head f)) (= 2 (count (second f)))
                                       (plus-of? (nth f 2) (first (second f)))))
                          [{:call x :with (fn [acc] (assoc x 3 acc))}])))
              nil)]
      r)))

(defn- generalized-lemmas
  "For a fold into an accumulator starting at 0, prove that the fold from
  any integer acc is an integer, and is acc plus the fold from 0; each by
  induction on a list variable of the fold, acc left free in the
  hypothesis.  Returns the lemma rules and the step's trace, or nil.  The
  choice of fold is the search's; that the lemmas hold is the checker's
  to confirm."
  [opts {:keys [call with]}]
  (let [acc (symbol (str "acc%" (Math/abs (hash call))))
        c-acc (with acc)
        law-vars (filter #(get-in opts [:types %]) (sort-by str (t/vars call)))
        list-vars (filter #(let [ty (get-in opts [:types %])]
                             (and (seq? ty) (contains? '#{List Vec} (first ty))))
                          law-vars)
        opts* (-> opts (update :types assoc acc 'Int) (assoc :ih-free {acc 'Int}))
        prove (fn [o g] (first (keep (fn [v] (fuelled #(by-induction o g v (get-in opts [:types v]))))
                                     list-vars)))
        [int-goal eq-goal] (sc/accumulator-goals call c-acc acc)]
    (when (seq list-vars)
      (when-let [p1 (prove opts* int-goal)]
        (let [r1 (sc/accumulator-rule opts 'accumulator-is-an-integer int-goal acc law-vars)
              opts2 (update opts* :lemmas conj r1)]
          (when-let [p2 (prove opts2 eq-goal)]
            {:rules [r1 (sc/accumulator-rule opts 'accumulator-adds eq-goal acc law-vars)]
             :trace {:by :accumulator :call call :c-acc c-acc :acc acc :law-vars (vec law-vars)
                     :on (t/show call) :integer p1 :adds p2}}))))))

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
           (str ", generalising " (str/join " and " (map pr-str gs))))
         (when-let [as (seq (distinct (keep (fn [x] (when (and (map? x) (= :accumulator (:by x)))
                                                       (:on x)))
                                           (tree-seq coll? seq trace))))]
           (str ", generalising the accumulator of " (str/join " and " (map pr-str as)))))))

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
          ;; an attempt that runs out of fuel fails on its own; the others
          ;; still get their turn
          attempt (fn [f] (reset! unfolded #{}) (reset! lemmas-used #{})
                    (let [r (try (f)
                                 (catch clojure.lang.ExceptionInfo e
                                   (if (:writ.prove.rewrite/fuel (ex-data e)) nil (throw e))))]
                      [r @unfolded]))
          tries (concat [#(some->> (prove-all opts g) (hash-map :by :cases :proofs))]
                        (for [[v ty] bs] #(by-induction opts g v ty)))
          [trace used] (or (first (filter first (map attempt tries))) [nil #{}])
          ;; a fold into an accumulator: prove it adds, then try again with that
          [trace used] (if trace
                         [trace used]
                         (or (first
                               (for [cand (accumulators opts (fuelled
                                                               #(let [ctx (rw/context opts)]
                                                                  (mapv (fn [x] (rw/normalize ctx x))
                                                                        (concat (:hyps g) (:goals g))))))
                                     :let [gl (generalized-lemmas opts cand)]
                                     :when gl
                                     :let [opts* (update opts :lemmas into (:rules gl))
                                           r (first (filter first
                                                            (map attempt
                                                                 (concat [#(some->> (prove-all opts* g) (hash-map :by :cases :proofs))]
                                                                         (for [[v ty] bs] #(by-induction opts* g v ty))))))]
                                     :when r]
                                 [{:by :with :lemma (:trace gl) :proof (first r)} (second r)]))
                             [nil #{}]))
          target-used (filter #(= (str target) (namespace %)) used)
          ;; every proof is replayed by the checker before it is reported
          checked (when (and trace (seq target-used))
                    (check/check-proof (dissoc opts :lemmas-used :unfolded) g trace))]
      (cond
        (nil? trace) {:proved false :reason "no proof found"}
        (empty? target-used) {:proved false :reason "the proof does not use the code"}
        (not (:ok checked)) {:proved false
                             :reason (str "the proof checker rejected the proof: " (:reason checked))}
        :else (let [cited (sort (remove synthetic-lemmas @lemmas-used))]
                {:proved true :trace trace
                 :summary (str (summary trace)
                               (when (seq cited) (str ", citing " (str/join ", " cited))))
                 :lemmas (vec cited)})))
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
