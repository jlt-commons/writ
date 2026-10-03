(ns writ.prove
  "Prove writ.spec laws from the implementation's source.

  A law's terms and the target's definitions are translated to terms
  (writ.prove.translate) and rewritten to normal form (writ.prove.rewrite).
  The search tries, in order: the law as it stands; then structural
  induction on each quantified variable of an inductive type -- a list is
  nil, empty or a head and a tail, a Nat is 0 or p + 1, a datatype one case
  per constructor, an integer a loop counts up to a bound is at or past
  it, or below it with the law at one more -- with the law at every
  smaller value as a hypothesis.
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

(defn- innermost-test
  "The test an if's test comes down to: an or of ors, or a test that is
  itself an if, nests them, and a split on the innermost is atomic."
  [c]
  (if (= :if (head c)) (recur (nth c 1)) c))

(defn- split-candidate
  "An integer equation the facts pin down, to put in; else an open
  integer comparison to split on: in the goal, in a fact that is still
  an if, such as a disjunction taken as a hypothesis, or in what an
  induction hypothesis assumes; failing that, the test of an if with a
  branch that throws, or of one nested in another's test."
  ([n] (split-candidate n nil))
  ([n ctx]
   (let [free (into (t/vars n) (mapcat t/vars (keys (:facts ctx))))
         ;; a test inside a fn literal about its parameter is no case of
         ;; the goal's
         own? (fn [c] (every? free (t/vars c)))
         open? (fn [c] (and (own? c)
                            (or (nil? ctx)
                                (and (not (contains? (:facts ctx) c)) (nil? (rw/truthiness ctx c))))))]
   (or ;; two facts 0 <= d and 0 <= -d pin d to 0: an equation to put in
       (when ctx
         (let [les (t/sort-printed (for [[f v] (:facts ctx) :when (and (true? v) (= :le (head f)))] (second f)))]
           (first (for [[i a] (map-indexed vector les)
                        b (drop (inc i) les)
                        :when (= [:lit 0] (rw/normalize ctx [:lin 0 [[a 1] [b 1]]]))
                        :let [c [:ieq a]]
                        :when (and (not (contains? (:facts ctx) c)) (solve-eq a))]
                    c))))
       (first (filter #(and (contains? #{:le :ieq} (head %)) (own? %))
                      (concat (rw/open-conditions n)
                              (for [[f _] (t/sort-printed key (filter (fn [[f v]] (and (true? v) (= :if (head f))))
                                                                      (:facts ctx)))
                                    c (rw/open-conditions f)
                                    :when (not (contains? (:facts ctx) c))]
                                c)
                              ;; what an induction hypothesis still needs:
                              ;; deciding it lets the hypothesis rewrite
                              (for [{:keys [hyp]} (:ih ctx)
                                    :when hyp
                                    :let [h (rw/normalize ctx hyp)]
                                    c (cons h (rw/open-conditions h))]
                                c))))
       ;; the test of an if one of whose branches throws: the other
       ;; branch is all there is to prove
       (first (for [x (t/subterms n)
                    :when (and (= :if (head x)) (or (= [:bottom] (nth x 2)) (= [:bottom] (nth x 3))))
                    :let [c (innermost-test (nth x 1))]
                    :when (open? c)]
                c))
       ;; the test of an if that is itself an if's test, such as the
       ;; first case of an `or` over a step of a loop: the rewriter
       ;; reads only the outer test, so the two outcomes of the inner one
       ;; are what separates the cases
       (first (for [x (t/subterms n)
                    :when (and (= :if (head x)) (= :if (head (nth x 1))))
                    ;; the innermost test: an or of ors nests its tests
                    :let [c (innermost-test (nth (nth x 1) 1))]
                    :when (open? c)]
                c))))))

(def default-config
  "The prover's knobs, in one place, so a bench can try others (see
  writ.bench/tune): the rewrites one attempt may make, how deep a goal's
  case splits go, the most values a bounded integer is split into, the
  random values a generalised goal is tested on first, and the order the
  strategies are tried in -- :order in general, :loop-order when a
  recursion of the code climbs on a law's integer."
  {:fuel 20000
   :depth 8
   :enum-limit 16
   :plausible-samples 30
   :order [:symbolic-cases :rewriting :symbolic :induction]
   :loop-order [:climbing :symbolic-cases :rewriting :symbolic :structural]})

(defn- enum-candidate
  "An integer variable that an unmodelled call takes, such as
  (bit-shift-left 1 k), whose facts bound it to a few values, as [k lo
  hi].  A case per value puts a literal in the call, which the rewriter
  computes."
  [ctx n limit]
  (first
    ;; filtered before the sort: the same order, printing fewer terms
    (for [x (t/sort-printed (filter #(and (= :call (head %))
                                          (not (contains? '#{= not not= < <= > >= + - * inc dec zero? pos? neg?} (second %))))
                                    (distinct (t/subterms n))))
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
          :when (and lo hi (<= 1 (- hi lo) limit))]
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
  (let [data? (fn [v] (and (symbol? v) (sc/data-cases opts v)))]
    ;; only the calls with such a variable are put in order
    (first (for [x (t/sort-printed (filter #(and (= :call (head %)) (contains? '#{first =} (second %))
                                                 (some data? (drop 2 %)))
                                           (distinct (mapcat t/subterms (cons n (keys (:facts ctx)))))))
                 v (drop 2 x)
                 :when (data? v)]
             v))))

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
  {:goal :facts :case}, :case the induction cases the goal is in."
  nil)

(def ^:dynamic *case*
  "The induction cases the search is inside, outermost first."
  [])

(defn- elems-var
  "A variable of the goal that stands for an unknown list of elements, one
  a case split could reveal."
  [opts n]
  (first (filter #(:writ/elems (get-in opts [:types %])) (sort-by str (t/vars n)))))

(defn- by-list-cases
  "Prove g by splitting element-list variable v into empty and a head and
  a tail.  Not induction: the tail gets no hypothesis of its own."
  [opts g hyps depth v]
  (let [[[ev et] [cv ct]] (sc/list-cases opts v)
        prove (fn [value types]
                (let [[o g* hs] (subst-all (update opts :types merge types) g hyps {v value})]
                  (prove-goal o g* hs (dec depth))))
        ;; the open case first: without induction it is the one that
        ;; fails, at the bottom of the split, and the closed lists before
        ;; it grow with the depth, so they are not solved for nothing
        more (prove cv ct)
        empty (when more (prove ev et))]
    (when (and empty more)
      {:by :list-cases :on v :empty empty :cons more})))

(defn- prove-goal
  "Prove boolean term g under hyps.  In order: a data value's tag is split
  into its constructors; integer arithmetic through and through goes to
  the solver whole; an open integer comparison is split into its two
  outcomes; a bounded integer an unmodelled call takes is split into its
  values; an unknown list of elements into its two shapes; and whatever
  is left open goes to the solver.  Returns a trace or nil.  parent, the
  case-context of the goal before a split, is what a case of the split
  builds on."
  ([opts g hyps depth] (prove-goal opts g hyps depth nil))
  ([opts g hyps depth parent]
   (let [[ctx vacuous n :as here] (if parent
                                    (sc/case-context-after opts parent hyps)
                                    (sc/case-context opts g hyps))
         split (delay (split-candidate n ctx))
         solve (delay (smt/prove ctx n))
         solved (fn [] (when-let [c @solve] {:by :solver :certificate c}))]
     (swap! (:unfolded opts) into @(:unfolded ctx))
     (when (and *stuck* (not vacuous) (not (truthy? n)) (not (true? (rw/truthiness ctx n)))
                (or (zero? depth) (nil? @split)))
       (swap! *stuck* conj {:goal n :facts (:facts ctx) :case *case* :types (:types ctx)}))
     (cond
       vacuous {:by :hypothesis-false}
       ;; a value the facts or its form say is truthy: a number, a seq
       (or (truthy? n) (true? (rw/truthiness ctx n))) {:by :rewriting}
       ;; the law's terms throw here, and a law is about the inputs on
       ;; which they return -- unless it says they never throw
       (and (= [:bottom] n) (not (:total opts))) {:by :throws}
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
                           ;; each case builds on this one's normal form
                           (prove-goal opts g (conj hyps c) (dec depth) here))
                     no (when yes (prove-goal opts g (conj hyps [:call 'not c]) (dec depth) here))]
                 (when (and yes no) {:by :split :on c :then yes :else no}))
               (or (when-let [e (enum-candidate ctx n (:enum-limit opts (:enum-limit default-config)))]
                     (by-enumeration opts g hyps depth e))
                   (when-let [v (elems-var opts n)] (by-list-cases opts g hyps depth v))
                   (solved)))))))))

(defn- prove-all
  "Prove every goal (under the hyps) in one context of opts."
  [opts {:keys [hyps goals]}]
  (let [ps (mapv #(prove-goal opts % hyps (:depth opts (:depth default-config))) goals)]
    (when (every? some? ps) ps)))

(declare by-induction)

(defn- sample-gen
  "A generator for values of a prover type, or nil."
  [ty]
  (cond
    (= 'Nat ty) gen/nat
    (= 'Int ty) gen/small-integer
    (= 'Bool ty) gen/boolean
    (and (map? ty) (:writ/elems ty)) (some-> (sample-gen (:writ/elems ty)) gen/list)
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
                  (range (:plausible-samples opts (:plausible-samples default-config)))))))

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

(defn- induct
  "Prove g by induction on v with cases cs, each proved outright or by
  generalising; the trace, or nil."
  [opts g v ty cs]
  (let [free (varying opts v)
        opts (cond-> opts (seq free) (assoc :ih-free free))
        steps (for [c cs]
                (binding [*case* (conj *case* (str "induction on " v ", case " (:desc c)))]
                  (let [[opts* gi] (sc/induction-case opts g v c)]
                    [c (or (prove-all opts* gi)
                           (by-generalizing (dissoc opts* :ih-free) gi (keys (:types c))))])))]
    (when (every? (comp some? second) steps)
      (cond-> {:by :induction :on v :ty (plain ty)
               :cases (mapv (fn [[c p]] {:case (:desc c) :proof p}) steps)}
        (seq free) (assoc :vary free)))))

(defn- by-induction [opts g v ty]
  (when-let [cs (cases v ty (:tenv opts))]
    (induct opts g v ty cs)))

(defn- by-climbing
  "Prove g by induction on integer v climbing to bound e: the law where v
  is at or past e, and where it is below, from the law at v + 1."
  [opts g v ty e]
  (some-> (induct opts g v ty (sc/climbing-cases v e)) (assoc :climb e)))

(defn- climbing-bounds
  "The bounds integer variable v climbs to in terms: each e of a
  comparison v < e (or v <= e - 1) in them, or in the guards of a
  recursive definition they call, with its arguments put in -- a loop
  whose index counts up to e; with loops-only, only the guards.  e never
  mentions v, and is an integer."
  [opts terms v & {:keys [loops-only]}]
  (let [ctx (rw/context opts)
        guards (fn [x]
                 (let [d (get-in opts [:defs (second x)])]
                   (when (and (:recursive? d) (= (count (:params d)) (count (drop 2 x))))
                     (rw/open-conditions (t/subst (:body d) (zipmap (:params d) (drop 2 x)))))))
        conds (distinct (concat (when-not loops-only (mapcat rw/open-conditions terms))
                                (mapcat guards (filter #(= :app (head %)) (distinct (mapcat t/subterms terms))))))]
    (distinct
      (for [c conds
            :let [c (rw/normalize ctx c)
                  c (if (and (= :call (head c)) (= 'not (second c))) (nth c 2) c)]
            d (when (= :le (head c)) [(second c)])
            :let [[k0 pairs] (if (= :lin (head d)) [(second d) (nth d 2)] [0 [[d 1]]])
                  m (into {} pairs)]
            ;; 0 <= r - v says v <= r, so v < r + 1
            :when (= -1 (get m v))
            :let [e (rw/normalize ctx (rw/lin->term {:c (inc k0) :m (dissoc m v)}))]
            :when (and (not (contains? (t/vars e) v)) (sc/int-bound? ctx e))]
        e))))

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

(defn- trace-steps
  "The steps of a proof trace, the maps that say :by, in the order a
  preorder walk meets them.  A trace shares its subterms, so a subtree seen
  once is not walked again: tree-seq would expand the sharing, twenty times
  the distinct nodes in pong's traces."
  [trace]
  (let [seen (volatile! #{})
        out (volatile! [])]
    (letfn [(walk [x]
              (when (and (coll? x) (not (contains? @seen x)))
                (vswap! seen conj x)
                (when (and (map? x) (contains? x :by)) (vswap! out conj x))
                (doseq [c (seq x)] (walk c))))]
      (walk trace))
    @out))

(defn summary
  "A proof trace in one line."
  [trace]
  (let [steps (trace-steps trace)
        ons (fn [by] (distinct (keep #(when (= by (:by %)) (:on %)) steps)))
        by? (fn [by] (some #(= by (:by %)) steps))
        on (first (ons :induction))
        climb (some #(when (and (= :induction (:by %)) (contains? % :climb)) (:climb %)) steps)
        cs (map (comp pr-str t/show) (ons :split))]
    (str (cond on (str "by induction on " on (when climb (str " up to " (pr-str (t/show climb)))))
               (by? :symbolic) "by symbolic evaluation"
               :else "by rewriting")
         (when (seq cs) (str ", splitting on " (str/join " and " cs)))
         (when (or (by? :solver) (by? :symbolic)) ", with the solver")
         (when-let [vs (seq (ons :list-cases))]
           (str ", with cases on " (str/join " and " vs)))
         (when-let [gs (seq (ons :generalizing))]
           (str ", generalising " (str/join " and " (map pr-str gs))))
         (when-let [as (seq (ons :accumulator))]
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

(defn- law-setup
  "What a search for a law starts from, given prove-law's arguments: its
  bindings as written and with tuples taken apart, its goal, the
  recognizers of the types it and its lemmas name, and the definitions
  with theirs."
  [{:keys [prop defs tenv own lemmas sigs]}]
  (let [[bs0 body] (split-foralls prop)
        g0 (goal (tr/context own) (mapv first bs0) body)
        [bs g] (expand-tuples (map (fn [[x ty]] [x (plain ty)]) bs0) g0)
        recs (sc/recognizers tenv (types-of bs lemmas sigs))]
    {:bs0 bs0 :bs bs :g g :recs recs :defs (merge defs (:defs recs))}))

(def ^:private stuck-limit
  "The most stuck goals a failed search reports."
  3)

(defn- clip [s n] (if (> (count s) n) (str (subs s 0 n) " ...") s))

(defn- stuck-ranked
  "The goals a failed search got stuck on, those that say most first: of
  the attempt that worked hardest -- it got furthest -- then the ones
  deepest in induction cases, each once."
  [stuck attempts]
  (let [effort (into {} (map (juxt :name :fuel)) attempts)]
    (->> stuck
         (remove #(falsy? (:goal %)))
         (sort-by (fn [{c :case fs :facts a :attempt}] [(- (get effort a 0)) (- (count c)) (count fs)]))
         (reduce (fn [out {:keys [goal] :as s}]
                   (if (some #(= goal (:goal %)) out) out (conj out s)))
                 []))))

(defn- stuck-report
  "The stuck goals that say most, as Clojure forms with the facts they
  were given: [{:attempt :case :goal :facts}], strings clipped."
  [stuck attempts]
  (let [show #(clip (pr-str (t/show %)) 400)]
    (->> (stuck-ranked stuck attempts)
         (take stuck-limit)
         (mapv (fn [{:keys [attempt case goal facts]}]
                 {:attempt attempt :case (vec case) :goal (show goal)
                  :facts (vec (take 8 (for [[f v] (t/sort-printed key facts)]
                                        (show (if (false? v) [:call 'not f] f)))))})))))

(def ^:private counting-core
  "The core fns that recurse on an integer argument."
  '#{range repeat take drop nth take-last drop-last repeatedly iterate subvec nthrest nthnext})

(defn- counts-on?
  "Does variable v of terms reach an argument of a fn that calls itself, or
  of a core fn that recurses on a count?  Followed through the
  definitions the terms call, as the parameters v is passed in."
  [defs terms v]
  (let [mentions? (fn [taint x] (some taint (t/subterms x)))]
    (loop [todo (mapv (fn [t] [t #{v}]) terms), seen #{}]
      (if (empty? todo)
        false
        (let [[t taint] (peek todo), todo (pop todo)
              subs (t/subterms t)]
          (if (some #(and (= :call (head %)) (symbol? (second %))
                          (contains? counting-core (symbol (name (second %))))
                          (some (partial mentions? taint) (drop 2 %)))
                    subs)
            true
            (let [calls (for [x subs
                              :when (= :app (head x))
                              :let [q (second x)
                                    d (get defs q)
                                    at (keep-indexed (fn [i a] (when (mentions? taint a) i)) (drop 2 x))]
                              :when (and d (seq at))]
                          [q d (set (keep #(nth (:params d) % nil) at))])]
              (if (some (fn [[_ d]] (:recursive? d)) calls)
                true
                (let [fresh (remove #(contains? seen [(first %) (nth % 2)]) calls)]
                  (recur (into todo (keep (fn [[_ d ps]] (when (:body d) [(:body d) ps])) fresh))
                         (into seen (map (fn [[q _ ps]] [q ps]) fresh))))))))))))

(defn- reaches-recursion?
  "Can terms reach a call of a recursive definition: is one named in them,
  in a rewrite rule normalizing them may apply, or in the body of a
  definition named there, and so on?  A loop's guards come only from such
  calls, so when none is reachable no loop of the code climbs on a law's
  integer, and the terms need not be normalized to find that out."
  [defs rules terms]
  (let [named (fn [x] (for [s (tree-seq coll? seq x)
                            :when (and (vector? s) (contains? #{:app :dfn} (first s)))]
                        (second s)))]
    (loop [todo (into (vec (mapcat named terms)) (mapcat named rules)), seen #{}]
      (if-let [f (peek todo)]
        (let [todo (pop todo)
              d (get defs f)]
          (cond (contains? seen f) (recur todo seen)
                (:recursive? d) true
                :else (recur (into todo (named (:body d))) (conj seen f))))
        false))))

(defn prove-law
  "Try to prove a law.  prop is the desugared law, its names qualified;
  defs are the translated definitions; target the implementation's ns;
  lemmas are the laws proved before it, as {:name :prop}; lemma, true
  for a lemma of a proof namespace, which may be about clojure.core alone;
  sigs, the target's signatures, {name {:params :ret}}; contracts, the
  rules prove-contracts gave for them; refutes?, when given, says whether
  a counterexample (values of the law's variables) is one running the code
  confirms; counterexample-only, true when only the solver's
  counterexample is wanted, and no proof.
  Returns {:proved true :trace :summary :lemmas} or {:proved false :reason
  :stuck}, and :attempts, what each strategy tried did: {:name :outcome
  :fuel :ms}, the outcome :proved, :failed, :fuel or :rejected."
  [{:keys [prop defs tenv target own fuel lemmas rets total hint lemma sigs contracts replay prover guards sym-budget refutes? counterexample-only] :as args}]
  (try
    (let [cfg (merge default-config prover)
          {:keys [bs0 bs g recs defs]} (law-setup args)
          unfolded (atom #{})
          lemmas-used (atom #{})
          ;; what a lemma added later would need to change the search: the
          ;; terms lemmas were tried on, and whether the rules were read
          ;; for a loop to climb, and named none
          asked (atom #{})
          rules-read (atom nil)
          burned (atom 0)
          opts {:defs defs :tenv tenv :types (into {} (map (fn [[x ty]] [x (plain ty)])) bs)
                :total total :vary (:vary hint) :recognizers recs
                ;; the refinements' predicates, as hypotheses a proof may
                ;; try without first
                :guards (or guards #{})
                ;; the symbolic proofs tried, so two strategies that run the
                ;; same goal whole ask the solver once
                :sym-memo (atom {})
                :sym-budget sym-budget
                :unfolded unfolded :fuel (or fuel (:fuel cfg)) :lemmas-used lemmas-used :asked asked
                :depth (:depth cfg) :enum-limit (:enum-limit cfg) :plausible-samples (:plausible-samples cfg)
                :rets (or rets {}) :burned burned
                :lemmas (into (vec (mapcat #(lemma-rules % defs tenv own)
                                           (if-let [use (:use hint)]
                                             (filter #(contains? (set use) (:name %)) lemmas)
                                             lemmas)))
                              contracts)}
          ;; an attempt that runs out of fuel fails on its own; the others
          ;; still get their turn
          ran-out (atom false)
          ;; what each attempt did, and the goals the failed ones got stuck on
          attempts (atom [])
          stuck (atom [])
          attempt (fn [[nm f]]
                    (reset! unfolded #{}) (reset! lemmas-used #{})
                    (let [t0 (System/currentTimeMillis)
                          b0 @burned
                          seen (atom [])
                          [r outcome] (binding [*stuck* seen *case* []]
                                        (try (let [r (f)] [r (if r :proved :failed)])
                                             (catch clojure.lang.ExceptionInfo e
                                               (if (:writ.prove.rewrite/fuel (ex-data e))
                                                 (do (reset! ran-out true) [nil :fuel])
                                                 (throw e)))))]
                      (swap! attempts conj {:name nm :outcome outcome :fuel (- @burned b0)
                                            :ms (- (System/currentTimeMillis) t0)})
                      (when-not r (swap! stuck into (map #(assoc % :attempt nm)) @seen))
                      [r @unfolded]))
          symbolic [[:symbolic-cases #(by-symbolic-cases opts g)] [:symbolic #(by-symbolic opts g)]]
          rewriting [[:rewriting #(some->> (prove-all opts g) (hash-map :by :cases :proofs))]]
          ;; a hint's variable first
          bs-order (if-let [v (:induct hint)]
                     (concat (filter #(= v (first %)) bs) (remove #(= v (first %)) bs))
                     bs)
          ;; the law's terms normalised, and each call in them on its own:
          ;; one side that runs out of fuel does not hide the other's loop
          terms (delay (let [raw (concat (:hyps g) (:goals g))]
                         (vec (keep (fn [x] (fuelled #(rw/normalize (rw/context opts) x)))
                                    (distinct (concat raw (filter #(= :app (head %)) (mapcat t/subterms raw))))))))
          ;; induction on an integer helps only where the code recurses on
          ;; it: where it reaches an argument of a fn that calls itself (a
          ;; loop is one), or of a core fn that counts, such as range.
          ;; Elsewhere, the step case is the law again, and the search a waste
          on-int? (fn [v ty] (or (not (contains? '#{Nat Int} ty)) (= v (:induct hint))
                                 (counts-on? defs (concat (:hyps g) (:goals g)) v)))
          ;; an integer that a loop counts up to a bound, by induction on
          ;; the distance left
          climbing (for [[v ty] bs-order
                         :when (and (contains? '#{Nat Int} ty) (on-int? v ty))
                         e (or (fuelled #(climbing-bounds opts @terms v)) [])]
                     [[:climb v (t/show e)] #(by-climbing opts g v ty e)])
          ;; a loop of the code that climbs on a law's integer names the
          ;; induction its recursion follows: that one goes first, before
          ;; rewriting unrolls the loop a split at a time
          loop-climbs? (and (not counterexample-only)
                            (some (fn [[_ ty]] (contains? '#{Nat Int} ty)) bs)
                            (reset! rules-read (reaches-recursion? (:defs opts) (:lemmas opts) (concat (:hyps g) (:goals g))))
                            (some (fn [[v ty]] (and (contains? '#{Nat Int} ty)
                                                    (seq (fuelled #(climbing-bounds opts @terms v :loops-only true)))))
                                  bs))
          structural (for [[v ty] bs-order :when (on-int? v ty)] [[:induct v] #(by-induction opts g v ty)])
          induction (concat climbing structural)
          groups {:symbolic-cases [(first symbolic)] :symbolic [(second symbolic)] :rewriting rewriting
                  :climbing climbing :structural structural :induction induction}
          in-order (fn [ks] (mapcat groups ks))
          tries (cond
                  ;; that nothing throws is known only from running the code
                  ;; symbolically, where every throw is noted
                  total symbolic
                  (= :symbolic (:strategy hint)) symbolic
                  (= :rewriting (:strategy hint)) rewriting
                  (= :induction (:strategy hint)) induction
                  (:induct hint) (concat induction symbolic rewriting)
                  loop-climbs? (in-order (:loop-order cfg))
                  :else (in-order (:order cfg)))
          ;; one attempt at a time: the first that proves it ends the search
          ;; the solver's counterexample, of the law's variables, or nil
          cex (delay (when (seq bs)
                       (some->> (first (keep #(sym/counterexample opts (:hyps g) %) (:goals g)))
                                (recompose bs0))))
          ;; a law the code refutes has no proof to find: once a strategy
          ;; fails, the counterexample, confirmed by running the code there,
          ;; ends the search
          refuted (delay (boolean (and refutes? @cex (refutes? @cex))))
          first-proof (fn [ts] (loop [[t & more] ts]
                                 (when t
                                   (let [r (attempt t)]
                                     (cond (first r) r
                                           @refuted nil
                                           :else (recur more))))))
          ;; a proof found before is checked first: the checker, not the
          ;; search, is what a proof rests on, so an old one the code still
          ;; bears out needs no search
          replayed (when replay
                     (let [t0 (System/currentTimeMillis)
                           c (try (check/check-proof (dissoc opts :lemmas-used :unfolded) g replay)
                                  (catch Throwable e {:ok false :reason (ex-message e)}))]
                       (swap! attempts conj {:name :replay :outcome (if (:ok c) :proved :rejected) :fuel 0
                                             :ms (- (System/currentTimeMillis) t0)})
                       (when (:ok c)
                         (reset! lemmas-used (:lemmas-used c))
                         c)))
          [trace used] (cond
                         replayed [replay (:unfolded replayed)]
                         counterexample-only [nil #{}]
                         :else (or (first-proof tries) [nil #{}]))
          ;; a fold into an accumulator: prove it adds, then try again with that
          [trace used] (if (or trace counterexample-only @refuted)
                         [trace used]
                         (or (first
                               (for [cand (accumulators opts (fuelled
                                                               #(let [ctx (rw/context opts)]
                                                                  (mapv (fn [x] (rw/normalize ctx x))
                                                                        (concat (:hyps g) (:goals g))))))
                                     :let [gl (generalized-lemmas opts cand)]
                                     :when gl
                                     :let [opts* (update opts :lemmas into (:rules gl))
                                           acc [:accumulator (t/show (:call cand))]
                                           r (first-proof
                                               (concat [[(conj acc :rewriting) #(some->> (prove-all opts* g) (hash-map :by :cases :proofs))]]
                                                       (for [[v ty] bs] [(conj acc [:induct v]) #(by-induction opts* g v ty)])))]
                                     :when r]
                                 [{:by :with :lemma (:trace gl) :proof (first r)} (second r)]))
                             [nil #{}]))
          target-used (filter #(= (str target) (namespace %)) used)
          ;; every proof is replayed by the checker before it is reported
          checked (when (and trace (or lemma (seq target-used)))
                    (or replayed (check/check-proof (dissoc opts :lemmas-used :unfolded) g trace)))]
      (-> (cond
            (nil? trace) (cond-> {:proved false :reason (if @ran-out "the search ran out of fuel" "no proof found")
                                  :stuck (stuck-report @stuck @attempts)
                                  ;; the terms themselves, for proposing lemmas; not cached
                                  :stuck-raw (vec (take 6 (stuck-ranked @stuck @attempts)))}
                           @cex (assoc :counterexample @cex)
                           true (assoc :asked {:terms @asked :no-recursion (false? @rules-read)}))
            (and (empty? target-used) (not lemma)) {:proved false :reason "the proof does not use the code"}
            (not (:ok checked)) (do (swap! attempts #(conj (pop %) (assoc (peek %) :outcome :rejected)))
                                    {:proved false
                                     :reason (str "the proof checker rejected the proof: " (:reason checked))})
            :else (let [cited (sort (remove #(or (contains? synthetic-lemmas %) (contract? %)) @lemmas-used))]
                    {:proved true :trace trace
                     :summary (str (summary trace)
                                   (when total ", and it never throws")
                                   (when (seq cited) (str ", citing " (str/join ", " cited))))
                     :lemmas (vec cited)}))
          (cond-> replayed (assoc :replayed true))
          (assoc :attempts @attempts)))
    (catch clojure.lang.ExceptionInfo e
      (cond
        (tr/outside-reason e) {:proved false :reason (ex-message e)}
        (:writ.prove.rewrite/fuel (ex-data e)) {:proved false :reason "the search ran out of fuel"}
        :else (throw e)))))

(defn- lemma-fires?
  "Could one of rules have fired in a search that tried lemmas on terms,
  or have opened an induction on a loop where it found none?"
  [terms no-recursion defs rules]
  (let [fires? (fn [{:keys [lhs vars]} x] (some? (rw/match-term lhs x vars)))]
    (boolean
      (or (some (fn [{:keys [lhs rhs vars] :as rule}]
                  (some (fn [x]
                          (if (and (vector? x) (= ::rw/nat (first x)))
                            ;; proved-nat?, at an atom of a linear form
                            (and (= [:lit true] rhs) (= :call (head lhs)) (= '<= (second lhs))
                                 (= 4 (count lhs))
                                 (some? (rw/match-term (nth lhs 3) (second x) vars)))
                            (fires? rule x)))
                        terms))
                (remove rw/inert-rule? rules))
          (and no-recursion (reaches-recursion? defs rules []))))))

(defn lemmas-matter?
  "Could lemmas fresh, added to those of a search that failed, have
  changed it?  asked is what the search noted (prove-law's :asked).  A
  lemma is a rewrite rule, tried on the terms the search rewrote: one
  whose left side matches none of them was never more than tried, so the
  search with it is the search without it.  A rule naming a fn that
  recurses could also have opened an induction on a loop, when the
  search looked for one and found none; and a lemma's types give
  recognizers the search would read.  args are prove-law's, with fresh
  among their :lemmas."
  [asked fresh {:keys [tenv own lemmas] :as args}]
  (let [{:keys [terms no-recursion]} asked]
    (or (nil? asked)
        (contains? terms ::rw/too-many)
        (try
          (let [{:keys [defs recs]} (law-setup args)
                before (law-setup (assoc args :lemmas (vec (remove (set fresh) lemmas))))]
            (or (not= recs (:recs before))
                (lemma-fires? terms no-recursion defs (mapcat #(lemma-rules % defs tenv own) fresh))))
          (catch Throwable _ true)))))

(defn- law-type
  "A case variable's type as a law writes it: a tail of elements is a
  list of them."
  [ty]
  (if (and (map? ty) (:writ/elems ty)) (list 'List (:writ/elems ty)) ty))

(defn lemma-candidates
  "Lemmas that would close a stuck goal, to be tested and proved before
  anyone sees them: the goal under the facts that share its variables,
  with each call of a signed fn that the goal and a fact both make taken
  as a variable of its return type (the call the induction hypothesis is
  about, as (isort xs-t) in insert's lemma), and once as it is.  Each is
  {:bindings [[x type] ...] :hyps [form ...] :goal form}; nil for a goal
  that names what no law can, such as a loop the prover made up."
  [stuck rets]
  (distinct
    (for [{:keys [goal facts types]} stuck
          generalize? [true false]
          :let [fact-terms (for [[f v] (t/sort-printed key (filter (comp boolean? val) facts))]
                             (if v f [:call 'not f]))
                calls (when generalize?
                        (distinct (for [x (t/subterms goal)
                                        :when (and (= :app (head x)) (contains? rets (second x))
                                                   (some (fn [f] (some #{x} (t/subterms f))) fact-terms))]
                                    x)))
                gen (zipmap calls (map #(symbol (str "r" %)) (range)))
                sub (fn [x] (reduce (fn [x [c v]] (replace-term x c v)) x gen))
                g (sub goal)
                vs (t/vars g)
                hyps (vec (for [f (map sub fact-terms)
                                :when (and (some vs (t/vars f)) (not= f g))]
                            f))
                all-vs (sort-by str (reduce into vs (map t/vars hyps)))
                ty (fn [v] (if-let [c (some (fn [[c x]] (when (= x v) c)) gen)]
                             (get rets (second c))
                             (law-type (get types v))))
                forms (binding [t/*full-names* true] (mapv t/show (cons g hyps)))]
          :when (and (or (not generalize?) (seq calls))
                     (every? ty all-vs)
                     ;; a name the prover made up is no one's to state
                     (not-any? (fn [x] (and (symbol? x)
                                           (or (str/includes? (name x) "$loop")
                                               (= "writ.prove.types" (namespace x)))))
                               (tree-seq coll? seq forms)))]
      {:bindings (mapv (fn [v] [v (ty v)]) all-vs)
       :hyps (vec (rest forms))
       :goal (first forms)})))

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
                        ;; a bound the code climbs to goes first: rewriting
                        ;; would unroll the loop a split at a time, the goal
                        ;; doubling at each test it cannot decide.  Each
                        ;; attempt on its own fuel, so one that runs out
                        ;; leaves the next its turn
                        trace (or (first (for [p ps
                                               :when (contains? '#{Nat Int} (plain (types p)))
                                               e (or (fuelled #(climbing-bounds opts (:goals g) p)) [])
                                               :let [r (fuelled #(by-climbing opts g p (types p) e))]
                                               :when r]
                                           r))
                                  (fuelled #(some->> (prove-all opts g) (hash-map :by :cases :proofs)))
                                  (first (keep (fn [p] (fuelled #(by-induction opts g p (types p)))) ps)))]
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

(defn contract-rules
  "The contracts of fns whose signatures are taken as given, not proved:
  a spec's assumptions about code writ does not check.  On arguments of
  its parameter types, each returns a value of its return type, as the
  lemma rules prove-contracts makes: an Int is (integer? call), a Nat
  that and (<= 0 call), and any other type with a recognizer the
  recognizer of the call."
  [tenv sigs]
  (let [recs (sc/recognizers tenv (types-of [] [] sigs))]
    (vec (for [[f {:keys [params ret]}] (sort-by key sigs)
               :let [ret (plain ret)
                     c (get-in recs [:checks ret])
                     ps (mapv #(symbol (str "?c%" %)) (range (count params)))
                     pat (into [:app f] ps)
                     rule (fn [nm check]
                            {:name (symbol (str (name f) nm))
                             :vars (set ps)
                             :types (zipmap ps (map plain params))
                             :lhs (t/subst check {'%x pat})
                             :rhs [:lit true]})]
               r (cond
                   (contains? '#{Int Nat} ret)
                   (cond-> [(rule "%contract" [:call 'integer? '%x])]
                     (= 'Nat ret) (conj (rule "%nonneg%contract" [:call '<= [:lit 0] '%x])))
                   (and (vector? c) (contains? #{:app :call} (head c)))
                   [(rule "%contract" c)]
                   :else [])]
           r))))

(defn definitions
  "Translate the defns of the target and the spec: [defs own].  pairs is
  [[ns-sym forms] ...] or [[ns-sym forms refers] ...]; each ns reads its
  own plain names first, then the plain names in refers, name ->
  qualified name.  sigs, {qualified-name {:params :ret}}, tell the
  translation which parameters are vectors."
  ([pairs] (definitions pairs {}))
  ([pairs sigs]
  (let [qualified (into {} (for [[k v] (tr/own-names (map #(take 2 %) pairs)) :when (namespace k)] [k v]))
        defs (into {}
                   (for [[ns-sym forms refers] pairs]
                     (let [own (merge qualified refers
                                      (into {} (for [[k v] (tr/own-names [[ns-sym forms]])
                                                     :when (nil? (namespace k))]
                                                 [k v])))]
                       (tr/defs-of (assoc (tr/context own) :sigs sigs) ns-sym forms))))]
    [defs qualified])))
