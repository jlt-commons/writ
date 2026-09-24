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
  a term throws.  The logic is untyped, as ACL2's is: a lemma, or a
  hypothesis that varies, is used only at terms shown to be of its
  variables' types -- by a recognizer, and by each signed fn's contract,
  proved from its code before any law.  A proof that never unfolds one of the target's own
  definitions says nothing about the code, and is not reported -- unless
  it proves a lemma of a proof namespace, which may be about clojure.core
  alone."
  (:require [clojure.string :as str]
            [clojure.test.check.generators :as gen]
            [writ.prove.term :as t :refer [head]]
            [writ.prove.rewrite :as rw]
            [writ.prove.translate :as tr]
            [writ.prove.check :as check]
            [writ.prove.smt :as smt]
            [writ.prove.symbolic :as sym]
            [writ.prove.scheme :as sc :refer [split-foralls goal plain cases truthy? falsy?
                                               solve-eq assume-hyp subst-all instance ih-for
                                               useful-ih replace-term lemma-rules]]))

;; --- proving a goal ---------------------------------------------------------------------

(declare prove-goal)
;; Every step records what the checker needs to replay it: writ.prove.check
;; follows the trace with writ.prove.scheme and the rewriter, and searches
;; for nothing.

(defn- split-candidate
  "An open integer comparison to split on: in the goal, or in a fact that
  is still an if, such as a disjunction taken as a hypothesis."
  ([n] (split-candidate n nil))
  ([n ctx]
   (first (filter #(contains? #{:le :ieq} (head %))
                  (concat (rw/open-conditions n)
                          (for [[f v] (sort-by (comp pr-str key) (:facts ctx))
                                :when (and (true? v) (= :if (head f)))
                                c (rw/open-conditions f)
                                :when (not (contains? (:facts ctx) c))]
                            c))))))

(def ^:private enum-limit
  "The most values a bounded integer is split into, one case each."
  16)

(defn- enum-candidate
  "An integer variable that an unmodelled call takes, such as
  (bit-shift-left 1 k), whose facts bound it to a few values, as [k lo
  hi].  A case per value puts a literal in the call, which the rewriter
  computes."
  [ctx n]
  (first
    (for [x (sort-by pr-str (distinct (t/subterms n)))
          :when (and (= :call (head x))
                     (not (contains? '#{= not not= < <= > >= + - * inc dec zero? pos? neg?} (second x))))
          v (drop 2 x)
          :when (and (symbol? v) (rw/int-term? ctx v))
          :let [bound (fn [sign]
                        (first (for [[f tv] (:facts ctx)
                                     :when (and (true? tv) (= :le (head f)))
                                     :let [d (second f)]
                                     :when (and (= :lin (head d)) (= [[v sign]] (nth d 2)))]
                                 (* (- sign) (second d)))))
                lo (or (bound 1) (when (= 'Nat (get-in ctx [:types v])) 0))
                hi (bound -1)]
          :when (and lo hi (<= 1 (- hi lo) enum-limit))]
      [v lo hi])))

(defn- by-enumeration
  "Prove g by one case per value of v from lo to hi, which the facts
  bound it to: each case puts the value in for v."
  [opts g hyps depth [v lo hi]]
  (let [ps (mapv (fn [k]
                   (let [[o g* hs] (subst-all opts g hyps {v [:lit k]})]
                     (prove-goal o g* hs (dec depth))))
                 (range lo (inc hi)))]
    (when (every? some? ps)
      {:by :enumeration :on v :from lo :to hi :cases ps})))

(defn- data-var
  "A variable of a data type the goal or a fact takes apart, as (first v)
  or (= v ...): splitting it into its constructors reveals the tag."
  [opts n ctx]
  (first (for [x (sort-by pr-str (distinct (mapcat t/subterms (cons n (keys (:facts ctx))))))
               :when (and (= :call (head x)) (contains? '#{first =} (second x)))
               v (drop 2 x)
               :when (and (symbol? v) (sc/data-cases opts v))]
           v)))

(defn- by-data-cases
  "Prove g by splitting data variable v into one case per constructor."
  [opts g hyps depth v]
  (let [ps (mapv (fn [[value types]]
                   (let [[o g* hs] (subst-all (update opts :types merge types) g hyps {v value})]
                     (prove-goal o g* hs (dec depth))))
                 (sc/data-cases opts v))]
    (when (every? some? ps)
      {:by :data-cases :on v :cases ps})))

(def ^:dynamic *stuck*
  "When bound to an atom, collects the goals a search could not close, as
  {:goal :facts}, for debugging the prover."
  nil)

(defn- elems-var
  "A variable of the goal that stands for an unknown list of elements, one
  a case split could reveal."
  [opts n]
  (first (filter #(map? (get-in opts [:types %])) (sort-by str (t/vars n)))))

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
  "Prove boolean term g under hyps.  In order: a data value's tag is split
  into its constructors; integer arithmetic through and through goes to
  the solver whole; an open integer comparison is split into its two
  outcomes; a bounded integer an unmodelled call takes is split into its
  values; an unknown list of elements into its two shapes; and whatever
  is left open goes to the solver.  Returns a trace or nil."
  [opts g hyps depth]
  (let [[ctx vacuous n] (sc/case-context opts g hyps)
        split (delay (split-candidate n ctx))
        solve (delay (smt/prove ctx n))
        solved (fn [] (when-let [c @solve] {:by :solver :certificate c}))]
    (swap! (:unfolded opts) into @(:unfolded ctx))
    (when (and *stuck* (not vacuous) (not (truthy? n)) (or (zero? depth) (nil? @split)))
      (swap! *stuck* conj {:goal n :facts (:facts ctx)}))
    (cond
      vacuous {:by :hypothesis-false}
      (truthy? n) {:by :rewriting}
      (zero? depth) (solved)
      :else
      (if-let [v (data-var opts n ctx)]
        (by-data-cases opts g hyps depth v)
        (or ;; each data case, once its tags are known: the code run
            ;; symbolically, one small formula for the solver
            (when-not (:symbolic-tried opts)
              (when-let [[c used] (sym/prove opts hyps g)]
                (swap! (:unfolded opts) into used)
                {:by :symbolic :certificate c}))
            (when (smt/pure? ctx n) (solved))
            (if-let [c @split]
              (let [opts (assoc opts :symbolic-tried true)
                    yes (if-let [[x v] (and (= :ieq (head c)) (solve-eq (second c)))]
                          (let [[o g* hs] (subst-all opts g hyps {x v})]
                            (prove-goal o g* hs (dec depth)))
                          (prove-goal opts g (conj hyps c) (dec depth)))
                    no (when yes (prove-goal opts g (conj hyps [:call 'not c]) (dec depth)))]
                (when (and yes no) {:by :split :on c :then yes :else no}))
              (or (when-let [e (enum-candidate ctx n)] (by-enumeration opts g hyps depth e))
                  (when-let [v (elems-var opts n)] (by-list-cases opts g hyps depth v))
                  (solved))))))))

(defn- prove-all
  "Prove every goal (under the hyps) in one context of opts."
  [opts {:keys [hyps goals]}]
  (let [ps (mapv #(prove-goal opts % hyps 8) goals)]
    (when (every? some? ps) ps)))

(declare by-induction)

(defn- sample-gen
  "A generator for values of a prover type, or nil."
  [ty]
  (cond
    (= 'Nat ty) gen/nat
    (= 'Int ty) gen/small-integer
    (= 'Bool ty) gen/boolean
    (and (map? ty) (:elems ty)) (some-> (sample-gen (:elems ty)) gen/list)
    (and (seq? ty) (contains? '#{List Vec} (first ty))) (some-> (sample-gen (second ty)) gen/list)
    :else nil))

(defn- plausible?
  "Does goal gi survive a few random values of its variables?  A
  generalisation can make a goal false; testing it first, as ACL2s does,
  saves searching for a proof that is not there.  Only a value that makes
  the hypotheses true and a goal false counts; a throw is no evidence."
  [opts gi]
  (let [vs (vec (sort-by str (reduce into #{} (map t/vars (concat (:hyps gi) (:goals gi))))))
        gens (mapv #(sample-gen (get-in opts [:types %])) vs)]
    (or (some nil? gens)
        (not-any? (fn [i]
                    (let [env (zipmap vs (map #(gen/generate % (mod i 20) i) gens))]
                      (try (and (every? #(t/evaluate % env) (:hyps gi))
                                (not-every? #(t/evaluate % env) (:goals gi)))
                           (catch Throwable _ false))))
                  (range 30)))))

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
                  p (when (and g* (plausible? opts* g*))
                      (or (prove-all opts* g*) (by-induction opts* g* ys ty)))]
            :when p]
        {:by :generalizing :ih i :call call :as ys :ty ty :on (t/show call) :proof p}))))

(defn- varying
  "The variables of opts' :vary, but v, with their types: they stay free
  in an induction hypothesis on v."
  [opts v]
  (into {} (for [x (:vary opts)
                 :let [ty (get-in opts [:types x])]
                 :when (and ty (not= x v))]
             [x ty])))

(defn- by-induction [opts g v ty]
  (when-let [cs (cases v ty (:tenv opts))]
    (let [free (varying opts v)
          opts (cond-> opts (seq free) (assoc :ih-free free))
          steps (for [c cs]
                  (let [[opts* gi] (sc/induction-case opts g v c)]
                    [c (or (prove-all opts* gi)
                           (by-generalizing (dissoc opts* :ih-free) gi (keys (:types c))))]))]
      (when (every? (comp some? second) steps)
        (cond-> {:by :induction :on v :ty (plain ty)
                 :cases (mapv (fn [[c p]] {:case (:desc c) :proof p}) steps)}
          (seq free) (assoc :vary free))))))

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
    (str (cond on (str "by induction on " on)
               (some #(and (map? %) (= :symbolic (:by %))) (tree-seq coll? seq trace)) "by symbolic evaluation"
               :else "by rewriting")
         (when (seq cs) (str ", splitting on " (str/join " and " cs)))
         (when (some #(and (map? %) (= :solver (:by %))) (tree-seq coll? seq trace))
           ", with the solver")
         (when (some #(and (map? %) (= :symbolic (:by %))) (tree-seq coll? seq trace)) ", with the solver")
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

(defn- recompose
  "A counterexample over the expanded binders, as values of the law's own:
  a Tuple binder's value is the vector of its components'."
  [bs0 cex]
  (letfn [(value [x ty]
            (if (and (seq? ty) (= 'Tuple (first ty)))
              (vec (map-indexed (fn [i cty] (value (symbol (str x "-" i)) (plain cty))) (rest ty)))
              (get cex x)))]
    (into {} (for [[x ty] bs0] [x (value x (plain ty))]))))

(defn- expand-tuples
  "Each binder of a Tuple type as a vector of fresh variables, one per
  component, with the component's type: a value of (Tuple A B) is exactly
  a vector [a b] with a an A and b a B.  Returns [binders goal]."
  [bs g]
  (loop [todo (seq bs), out [], g g]
    (if-let [[x ty] (first todo)]
      (if (and (seq? ty) (= 'Tuple (first ty)))
        (let [xs (mapv #(symbol (str x "-" %)) (range (count (rest ty))))
              sub #(t/subst % {x (t/seq-term xs)})]
          (recur (concat (map vector xs (rest ty)) (rest todo)) out
                 {:hyps (mapv sub (:hyps g)) :goals (mapv sub (:goals g))}))
        (recur (rest todo) (conj out [x ty]) g))
      [out g])))

(defn- symbolic-cases
  "Prove goal g under hyps by splitting each data variable into its
  constructors, and running every case symbolically: small formulas, one
  per combination of tags, where one formula for all of them would make
  the solver search the tags too.  The same trace a case split on data
  and a symbolic leaf make, so the checker replays it as those."
  [opts hyps g]
  (if-let [v (first (filter #(sc/data-cases opts %)
                            (sort-by str (reduce into (t/vars g) (map t/vars hyps)))))]
    (let [ps (mapv (fn [[value types]]
                     (let [[o g* hs] (subst-all (update opts :types merge types) g hyps {v value})]
                       (symbolic-cases o hs g*)))
                   (sc/data-cases opts v))]
      (when (every? some? ps)
        {:by :data-cases :on v :cases ps}))
    (when-let [[c used] (sym/prove opts hyps g)]
      (swap! (:unfolded opts) into used)
      {:by :symbolic :certificate c})))

(defn- by-symbolic-cases
  "Every goal by symbolic-cases, when the code runs symbolically at all."
  [opts {:keys [hyps goals]}]
  (when (every? #(sym/formula opts hyps %) goals)
    (let [ps (mapv #(symbolic-cases opts hyps %) goals)]
      (when (every? some? ps)
        {:by :cases :proofs ps}))))

(defn- by-symbolic
  "Prove every goal by running it on symbolic values and handing the one
  formula to the solver: no case splits, so a step fn with many
  conditions is one query."
  [opts {:keys [hyps goals]}]
  (let [rs (mapv #(sym/prove opts hyps %) goals)]
    (when (every? some? rs)
      (swap! (:unfolded opts) into (mapcat second rs))
      {:by :symbolic :certificates (mapv first rs)})))

(defn- types-of
  "The types a law's variables, its lemmas' and the signatures name."
  [bs lemmas sigs]
  (distinct (map plain (concat (map second bs)
                               (mapcat #(map second (first (split-foralls (:prop %)))) lemmas)
                               (mapcat (fn [[_ {:keys [params ret]}]] (cons ret params)) sigs)))))

(defn- contract? [nm] (str/ends-with? (name nm) "%contract"))

(defn prove-law
  "Try to prove a law.  prop is the desugared law, its names qualified;
  defs are the translated definitions; target the implementation's ns;
  lemmas are the laws proved before it, as {:name :prop}; lemma, true
  for a lemma of a proof namespace, which may be about clojure.core alone;
  sigs, the target's signatures, {name {:params :ret}}; contracts, the
  rules prove-contracts gave for them.
  Returns {:proved true :trace :summary :lemmas} or {:proved false :reason}."
  [{:keys [prop defs tenv target own fuel lemmas rets total hint lemma sigs contracts]}]
  (try
    (let [[bs0 body] (split-foralls prop)
          tctx (tr/context own)
          g0 (goal tctx (mapv first bs0) body)
          [bs g] (expand-tuples (map (fn [[x ty]] [x (plain ty)]) bs0) g0)
          unfolded (atom #{})
          lemmas-used (atom #{})
          recs (sc/recognizers tenv (types-of bs lemmas sigs))
          defs (merge defs (:defs recs))
          opts {:defs defs :tenv tenv :types (into {} (map (fn [[x ty]] [x (plain ty)])) bs)
                :total total :vary (:vary hint) :recognizers recs
                :unfolded unfolded :fuel (or fuel 20000) :lemmas-used lemmas-used
                :rets (or rets {})
                :lemmas (into (vec (mapcat #(lemma-rules % defs tenv own)
                                           (if-let [use (:use hint)]
                                             (filter #(contains? (set use) (:name %)) lemmas)
                                             lemmas)))
                              contracts)}
          ;; an attempt that runs out of fuel fails on its own; the others
          ;; still get their turn
          ran-out (atom false)
          attempt (fn [f] (reset! unfolded #{}) (reset! lemmas-used #{})
                    (let [r (try (f)
                                 (catch clojure.lang.ExceptionInfo e
                                   (if (:writ.prove.rewrite/fuel (ex-data e))
                                     (do (reset! ran-out true) nil)
                                     (throw e))))]
                      [r @unfolded]))
          symbolic [#(by-symbolic-cases opts g) #(by-symbolic opts g)]
          rewriting [#(some->> (prove-all opts g) (hash-map :by :cases :proofs))]
          ;; a hint's variable first
          bs-order (if-let [v (:induct hint)]
                     (concat (filter #(= v (first %)) bs) (remove #(= v (first %)) bs))
                     bs)
          induction (for [[v ty] bs-order] #(by-induction opts g v ty))
          tries (cond
                  ;; that nothing throws is known only from running the code
                  ;; symbolically, where every throw is noted
                  total symbolic
                  (= :symbolic (:strategy hint)) symbolic
                  (= :rewriting (:strategy hint)) rewriting
                  (= :induction (:strategy hint)) induction
                  (:induct hint) (concat induction symbolic rewriting)
                  :else (concat [(first symbolic)] rewriting [(second symbolic)] induction))
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
          checked (when (and trace (or lemma (seq target-used)))
                    (check/check-proof (dissoc opts :lemmas-used :unfolded) g trace))]
      (cond
        (nil? trace) (cond-> {:proved false :reason (if @ran-out "the search ran out of fuel" "no proof found")}
                       (seq bs) (merge (when-let [cex (first (keep #(sym/counterexample opts (:hyps g) %) (:goals g)))]
                                         {:counterexample (recompose bs0 cex)})))
        (and (empty? target-used) (not lemma)) {:proved false :reason "the proof does not use the code"}
        (not (:ok checked)) {:proved false
                             :reason (str "the proof checker rejected the proof: " (:reason checked))}
        :else (let [cited (sort (remove #(or (contains? synthetic-lemmas %) (contract? %)) @lemmas-used))]
                {:proved true :trace trace
                 :summary (str (summary trace)
                               (when total ", and it never throws")
                               (when (seq cited) (str ", citing " (str/join ", " cited))))
                 :lemmas (vec cited)})))
    (catch clojure.lang.ExceptionInfo e
      (cond
        (tr/outside-reason e) {:proved false :reason (ex-message e)}
        (:writ.prove.rewrite/fuel (ex-data e)) {:proved false :reason "the search ran out of fuel"}
        :else (throw e)))))

(defn prove-contracts
  "Prove each signed fn's contract, as defunc does: on arguments of its
  parameter types, it returns a value of its return type -- where that
  type has a recognizer to say so.  An Int return is (integer? call); a
  Nat return is that and then (<= 0 call), proved once the call is known
  to be an integer.  A signature is only a claim; a contract proved from
  the code is a fact, and a lemma's variable may take a call of the fn as
  its value once the contract says the call is of the variable's type.
  Callees go first, so a fn may lean on the contracts of the fns it
  calls; one that fails is tried again only once a fn its code reaches
  has a new contract.  Each proof is replayed by the checker.
  Returns the proved contracts as lemma rules."
  [{:keys [defs tenv sigs fuel]}]
  (let [recs (sc/recognizers tenv (types-of [] [] sigs))
        defs (merge defs (:defs recs))
        goal (fn [f ps types nm check & [after]]
               (let [call (into [:app f] ps)
                     pat (into [:app f] (map #(symbol (str "?" %)) ps))]
                 [[f nm] {:types types :ps ps :after after
                          :g {:hyps [] :goals [(t/subst check {'%x call})]}
                          :rule {:name (symbol (str (name f) nm))
                                 :vars (set (map #(symbol (str "?" %)) ps))
                                 :types (into {} (map (fn [p] [(symbol (str "?" p)) (types p)])) ps)
                                 :lhs (t/subst check {'%x pat})
                                 :rhs [:lit true]}}]))
        goals (into {}
                    (for [[f {:keys [params ret]}] (sort-by key sigs)
                          :let [d (get defs f)
                                ret (plain ret)
                                c (get-in recs [:checks ret])]
                          :when (and (:params d) (= (count params) (count (:params d))))
                          :let [ps (mapv #(symbol (str "c%" %)) (range (count params)))
                                types (zipmap ps (map plain params))]
                          g (cond
                              (and (vector? c) (= :app (head c)))
                              [(goal f ps types "%contract" c)]
                              (contains? '#{Int Nat} ret)
                              (cond-> [(goal f ps types "%contract" [:call 'integer? '%x])]
                                (= 'Nat ret)
                                (conj (goal f ps types "%nonneg%contract"
                                            [:call '<= [:lit 0] '%x] [f "%contract"])))
                              :else [])]
                      g))
        attempt (fn [rules {:keys [types ps g]}]
                  (let [opts {:defs defs :tenv tenv :types types :recognizers recs
                              :unfolded (atom #{}) :lemmas-used (atom #{}) :fuel (or fuel 20000)
                              :lemmas rules :rets {}}
                        trace (fuelled
                                #(or (some->> (prove-all opts g) (hash-map :by :cases :proofs))
                                     (first (keep (fn [p] (by-induction opts g p (types p))) ps))))]
                    (when (and trace (:ok (check/check-proof (dissoc opts :lemmas-used :unfolded) g trace)))
                      trace)))
        ;; the fns each fn's code calls, itself and transitively
        callees (fn [f] (set (keep #(when (= :app (head %)) (second %))
                                   (some-> (get defs f) :body t/subterms))))
        reach (memoize (fn [f] (loop [seen #{f} todo [f]]
                                 (if-let [x (first todo)]
                                   (let [new (remove seen (callees x))]
                                     (recur (into seen new) (into (subvec todo 1) new)))
                                   seen))))
        ;; callees first, so a proof can lean on what it calls in the
        ;; same pass; a Nat's bound after its integer contract
        order (vec (sort-by (fn [[f nm]] [(count (reach f)) (str f) (= nm "%nonneg%contract")])
                            (keys goals)))
        ;; the contracts proved so far that f's code can use
        usable (fn [f proved] (set (filter (fn [[g]] (contains? (reach f) g)) proved)))]
    ;; a goal that failed is tried again only once a fn its code reaches
    ;; has a new contract: nothing else changes what it can prove
    (loop [rules [] proved #{} tried {} todo order]
      (let [[rules proved tried]
            (reduce (fn [[rules proved tried] [f :as k]]
                      (let [x (get goals k)
                            have (usable f proved)]
                        (if (or (and (:after x) (not (contains? proved (:after x))))
                                (= have (get tried k)))
                          [rules proved tried]
                          (if (attempt rules x)
                            [(conj rules (:rule x)) (conj proved k) tried]
                            [rules proved (assoc tried k have)]))))
                    [rules proved tried] todo)
            left (vec (remove proved todo))]
        (if (or (= (count left) (count todo))
                (not-any? (fn [[f :as k]]
                            (not= (get tried k) (usable f proved)))
                          left))
          rules
          (recur rules proved tried left))))))

(defn definitions
  "Translate the defns of the target and the spec: [defs own].  pairs is
  [[ns-sym forms] ...] or [[ns-sym forms refers] ...]; each ns reads its
  own plain names first, then the plain names in refers, name ->
  qualified name."
  [pairs]
  (let [qualified (into {} (for [[k v] (tr/own-names (map #(take 2 %) pairs)) :when (namespace k)] [k v]))
        defs (into {}
                   (for [[ns-sym forms refers] pairs]
                     (let [own (merge qualified refers
                                      (into {} (for [[k v] (tr/own-names [[ns-sym forms]])
                                                     :when (nil? (namespace k))]
                                                 [k v])))]
                       (tr/defs-of (tr/context own) ns-sym forms))))]
    [defs qualified]))
