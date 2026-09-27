(ns writ.prove.smt
  "A goal the rewriter leaves open, handed to writ.solve.

  The goal and the facts it is under become one formula: facts imply that
  the goal is truthy.  Integer terms -- literals, linear forms, integer
  variables, quot and mod by a literal -- are the solver's terms, and
  comparisons of them its atoms.  Any other term is an atom of its own:
  an integer the solver knows nothing about, or the truth of a test, the
  same term always the same atom.  So the formula is weaker than the goal,
  never stronger, and when the solver finds it valid the goal holds.

  The formula is built the same way every time from the same goal and
  facts, and the solver's certificate is checked by writ.solve/verify, so
  the proof checker replays this step without searching."
  (:require [writ.prove.term :as t :refer [head]]
            [writ.prove.rewrite :as rw]
            [writ.solve :as solve]))

(def budget
  "Decisions the solver may make on one goal; past it, the goal stays open."
  3000)

(defn- atom-of
  "The symbol standing for term x, the next free one the first time."
  [atoms kind x]
  (or (get-in @atoms [:names x])
      (let [n (symbol (str "%" (name kind) (count (:names @atoms))))]
        (swap! atoms #(-> % (assoc-in [:names x] n) (assoc-in [:decls n] kind)))
        n)))

(declare truth)

(defn- int-of [ctx atoms x]
  (cond
    (t/int-lit? x) (second x)
    (= :lin (head x)) (into [:+ (second x)]
                            (for [[a k] (nth x 2)] [:* k (int-of ctx atoms a)]))
    (and (symbol? x) (rw/int-term? ctx x)) (atom-of atoms :int x)
    (and (= :call (head x)) (contains? '#{quot mod} (second x)) (= 4 (count x))
         (t/int-lit? (nth x 3)) (not (zero? (second (nth x 3)))) (rw/int-term? ctx (nth x 2)))
    [(keyword (name (second x))) (int-of ctx atoms (nth x 2)) (second (nth x 3))]
    (rw/int-term? ctx x) (atom-of atoms :int x)
    :else nil))

(defn- ints [ctx atoms xs]
  (let [vs (mapv #(int-of ctx atoms %) xs)]
    (when (every? some? vs) vs)))

(defn truth
  "The formula for 'x is truthy'."
  [ctx atoms x]
  (case (head x)
    :lit (not (false? (second x)))
    :nil false
    (:sq :fn :cfn) true
    :le (if-let [d (int-of ctx atoms (second x))] [:<= 0 d] (atom-of atoms :bool x))
    :ieq (if-let [d (int-of ctx atoms (second x))] [:= 0 d] (atom-of atoms :bool x))
    :if [:or [:and (truth ctx atoms (nth x 1)) (truth ctx atoms (nth x 2))]
         [:and [:not (truth ctx atoms (nth x 1))] (truth ctx atoms (nth x 3))]]
    :call (let [[_ f & args] x]
            (cond
              (and (= 'not f) (= 1 (count args))) [:not (truth ctx atoms (first args))]
              (and (contains? '#{= < <= > >=} f) (= 2 (count args)) (ints ctx atoms args))
              (into [(keyword (name f))] (ints ctx atoms args))
              :else (atom-of atoms :bool x)))
    (atom-of atoms :bool x)))

(defn goal-formula
  "{:formula :decls} saying the facts of ctx imply goal n is truthy."
  [ctx n]
  (let [atoms (atom {:names {} :decls {}})
        facts (vec (for [[c v] (t/sort-printed key (:facts ctx))
                         :when (boolean? v)]
                     (let [f (truth ctx atoms c)] (if v f [:not f]))))
        g (truth ctx atoms n)]
    {:formula [:=> (into [:and true] facts) g]
     :decls (:decls @atoms)}))

(defn pure?
  "Is the goal, under its facts, integer arithmetic through and through:
  no atom but integers?  Then the solver decides it whole."
  [ctx n]
  (every? #(= :int %) (vals (:decls (goal-formula ctx n)))))

(defn prove
  "A certificate that goal n holds under the facts of ctx, or nil."
  [ctx n]
  (let [{:keys [formula decls]} (goal-formula ctx n)]
    (when (some #(= :int %) (vals decls))
      (let [r (try (solve/valid? formula decls {:budget budget})
                   (catch clojure.lang.ExceptionInfo _ nil))]
        (when (= :valid (:result r))
          (:certificate r))))))

(defn verify
  "Does certificate c prove goal n under the facts of ctx?"
  [ctx n c]
  (let [{:keys [formula decls]} (goal-formula ctx n)]
    (try (solve/verify formula decls c)
         (catch clojure.lang.ExceptionInfo _ false))))
