(ns writ.prove.check
  "An independent check of a proof: it replays the trace the prover's
  search produced, and searches for nothing.

  At each step the checker rebuilds the goal itself, with the definitions
  in writ.prove.scheme and the rewriter, and confirms the step is one the
  logic allows:

  * rewriting closes a goal only when it normalises to a truthy value
  * a split on a condition proves both outcomes, and substitutes only an
    equation it solves for itself
  * cases on a list of elements prove both shapes
  * an induction's cases are exactly its type's cases, each proved with
    the hypotheses at that case's smaller values and no others
  * a generalisation uses an equality hypothesis the case really has, and
    the call it replaces really occurs
  * an accumulator's lemmas are proved before anything cites them, and a
    law cites only the lemmas it was given

  So what must be trusted is the rewrite rules (checked against the
  runtime by writ.prove.rewrite/self-test), the induction schemes, and
  this namespace: not the search, its heuristics or its bookkeeping."
  (:require [writ.prove.term :as t :refer [head]]
            [writ.prove.rewrite :as rw]
            [writ.prove.scheme :as sc]
            [writ.prove.smt :as smt]
            [writ.prove.symbolic :as sym]))

(defn- reject! [& msg]
  (throw (ex-info (apply str msg) {::rejected true})))

(declare check-goal check-cases check-induction)

(defn- check-goal
  "Replay the proof of boolean goal g under hyps.  The goal is normalised
  only for the steps that read it: a case split on data and a symbolic
  leaf do not, and normalising a large goal is where time goes."
  [opts g hyps p]
  (let [cc (delay (sc/case-context opts g hyps))
        vacuous (delay (second @cc))
        n (delay (nth @cc 2))]
    (case (:by p)
      :hypothesis-false (when-not @vacuous (reject! "a hypothesis said to be false is not"))
      :symbolic (when-not (sym/verify opts hyps g (:certificate p))
                  (reject! "the solver's certificate does not prove " (pr-str (t/show g))))
      :solver (let [[ctx _ n] (sc/case-context opts g hyps)]
                (when-not (or @vacuous (smt/verify ctx n (:certificate p)))
                  (reject! "the solver's certificate does not prove " (pr-str (t/show n)))))
      :rewriting (when-not (or @vacuous (sc/truthy? @n))
                   (reject! "the goal does not rewrite to true: " (pr-str (t/show @n))))
      :split (let [c (:on p)]
               (if-let [[x v] (and (= :ieq (head c)) (sc/solve-eq (second c)))]
                 (let [[o g* hs] (sc/subst-all opts g hyps {x v})]
                   (check-goal o g* hs (:then p)))
                 (check-goal opts g (conj hyps c) (:then p)))
               (check-goal opts g (conj hyps [:call 'not c]) (:else p)))
      :list-cases (let [v (:on p)]
                    (when-not (map? (get-in opts [:types v]))
                      (reject! "`" v "` is not a list of elements"))
                    (doseq [[[value types] sub] (map vector (sc/list-cases opts v) [(:empty p) (:cons p)])]
                      (let [[o g* hs] (sc/subst-all (update opts :types merge types) g hyps {v value})]
                        (check-goal o g* hs sub))))
      :enumeration (let [{v :on lo :from hi :to cs :cases} p
                         [ctx] (sc/case-context opts g hyps)
                         holds? #(= [:lit true] (rw/normalize ctx %))]
                     (when-not (and (symbol? v) (integer? lo) (integer? hi) (<= lo hi)
                                    (holds? [:call '<= [:lit lo] v]) (holds? [:call '<= v [:lit hi]]))
                       (reject! "the facts do not bound `" v "` to " lo ".." hi))
                     (when-not (= (count cs) (inc (- hi lo)))
                       (reject! "the cases on `" v "` are not one per value"))
                     (doseq [[k sub] (map vector (range lo (inc hi)) cs)]
                       (let [[o g* hs] (sc/subst-all opts g hyps {v [:lit k]})]
                         (check-goal o g* hs sub))))
      :data-cases (let [v (:on p)
                        cs (or (sc/data-cases opts v)
                               (reject! "`" v "` is not of a data type"))]
                    (when-not (= (count cs) (count (:cases p)))
                      (reject! "the cases on `" v "` are not one per constructor"))
                    (doseq [[[value types] sub] (map vector cs (:cases p))]
                      (let [[o g* hs] (sc/subst-all (update opts :types merge types) g hyps {v value})]
                        (check-goal o g* hs sub))))
      (reject! "a goal cannot be proved " (pr-str (:by p))))))

(defn- check-all
  "Replay one proof per goal: ps is what prove-all produced."
  [opts {:keys [hyps goals]} ps]
  (when-not (and (vector? ps) (= (count ps) (count goals)))
    (reject! "a proof for each goal is missing"))
  (doseq [[g p] (map vector goals ps)]
    (check-goal opts g hyps p)))

(defn- check-case-proof
  "An induction case is proved outright, or by generalising."
  [opts gi p]
  (if (vector? p)
    (check-all opts gi p)
    (case (:by p)
      :generalizing
      (let [{:keys [ih call as ty proof]} p
            h (get (:ih opts) ih)
            _ (when (or (:generalized? opts) (nil? h))
                (reject! "a generalisation with no hypothesis to use"))
            g* (or (sc/generalization opts gi h call as)
                   (reject! "the generalised call does not occur in the goal"))
            opts* (-> opts (assoc :generalized? true :ih []) (update :types assoc as ty))]
        (check-cases opts* g* proof))
      (reject! "an induction case cannot be proved " (pr-str (:by p))))))

(defn- check-induction
  "Replay an induction on v: its cases must be the type's cases.  A
  variable that varies in the hypothesis must be one of the goal's, at its
  own type."
  [opts g {:keys [on ty cases vary]}]
  (let [cs (or (sc/cases on ty (:tenv opts)) (reject! "`" on "` is not of an inductive type"))
        declared (get-in opts [:types on])
        _ (doseq [[x xty] vary]
            (when (or (= x on) (not= xty (get-in opts [:types x])))
              (reject! "`" x "` cannot vary in the hypothesis of an induction on `" on "`")))
        opts (cond-> opts (seq vary) (assoc :ih-free vary))]
    (when-not (= (sc/plain declared) ty)
      (reject! "induction on `" on "` as " (pr-str ty) " but it is " (pr-str declared)))
    (when-not (= (map :desc cs) (map :case cases))
      (reject! "the cases of `" on "` are " (pr-str (map :desc cs))))
    (doseq [[c {:keys [proof]}] (map vector cs cases)]
      (let [[opts* gi] (sc/induction-case opts g on c)]
        (check-case-proof (dissoc opts* :ih-free) gi proof)))))

(defn- check-cases
  "A goal set proved outright (a proof per goal) or by induction."
  [opts g p]
  (cond
    (vector? p) (check-all opts g p)
    (= :induction (:by p)) (check-induction opts g p)
    :else (reject! "cannot prove goals " (pr-str (:by p)))))

(defn- check-accumulator
  "Replay the accumulator lemmas, and return their rules.  What they state
  needs no check of its own: the replay proves it."
  [opts {:keys [call c-acc acc law-vars integer adds]}]
  (let [[int-goal eq-goal] (sc/accumulator-goals call c-acc acc)
        ;; acc stays free in these inductions' hypotheses
        opts* (-> opts (update :types assoc acc 'Int) (assoc :ih-free {acc 'Int}))
        induction (fn [p] (if (= :induction (:by p)) p (reject! "an accumulator lemma needs induction")))
        _ (check-induction opts* int-goal (induction integer))
        r1 (sc/accumulator-rule opts 'accumulator-is-an-integer int-goal acc law-vars)
        _ (check-induction (update opts* :lemmas conj r1) eq-goal (induction adds))]
    [r1 (sc/accumulator-rule opts 'accumulator-adds eq-goal acc law-vars)]))

(defn check-proof
  "Replay trace, a proof of goal g in opts (types, defs, tenv, and the
  lemma rules the proof may cite).  {:ok true} or {:ok false :reason}."
  [opts g trace]
  (try
    (let [opts (-> opts (assoc :unfolded (atom #{}) :lemmas-used (atom #{})) (dissoc :ih-free))]
      (case (:by trace)
        :cases (check-all opts g (:proofs trace))
        :induction (check-induction opts g trace)
        :symbolic (let [{:keys [hyps goals]} g
                        cs (:certificates trace)]
                    (when-not (= (count cs) (count goals))
                      (reject! "a certificate for each goal is missing"))
                    (doseq [[gl c] (map vector goals cs)]
                      (when-not (sym/verify opts hyps gl c)
                        (reject! "the solver's certificate does not prove " (pr-str (t/show gl))))))
        :with (let [rules (check-accumulator opts (:lemma trace))
                    opts* (update opts :lemmas into rules)
                    inner (:proof trace)]
                (case (:by inner)
                  :cases (check-all opts* g (:proofs inner))
                  :induction (check-induction opts* g inner)
                  (reject! "cannot replay " (pr-str (:by inner)))))
        (reject! "cannot replay " (pr-str (:by trace))))
      {:ok true})
    (catch clojure.lang.ExceptionInfo e
      (cond
        (::rejected (ex-data e)) {:ok false :reason (ex-message e)}
        (:writ.prove.rewrite/fuel (ex-data e)) {:ok false :reason "replaying it ran out of fuel"}
        :else (throw e)))))
