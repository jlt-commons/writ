(ns writ.speed-test
  "What a check costs, and the changes that make it cost less without
  changing what it finds."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.generators]
            [writ.spec :as spec]))

;; --- timings ----------------------------------------------------------------------

(deftest a-report-says-where-its-time-went
  (let [r (spec/check 'writ.spec-demo.gap-spec {:seed 1})
        t (:timings r)]
    (is (:ok r) (:message r))
    (is (= #{:static :tests :prover :more-trials :adequacy :graphs :total} (set (keys t))))
    (is (every? #(and (number? %) (>= % 0)) (vals t)))
    (is (>= (:total t) (reduce + (vals (dissoc t :total)))))))

(deftest each-tested-law-says-what-its-trials-cost
  (let [r (spec/check 'writ.spec-demo.gap-spec {:seed 1 :adequacy false})]
    (is (seq (:laws r)))
    (is (every? #(number? (:test-ms %)) (remove #(= :vacuous (:status %)) (:laws r))))))

;; --- generators sized by what their keys can be -----------------------------------

(def ^:private domain-size @#'spec/domain-size)

(deftest a-key-type-with-few-values-says-how-many
  (let [tenv (spec/type-env 'writ.spec-demo.racks-spec)]
    (is (= 3 (domain-size 'Slot tenv)))
    (is (= 4 (domain-size 'Who tenv)))
    (is (= 2 (domain-size 'Bool tenv)))
    (is (nil? (domain-size 'Nat tenv)))
    (is (nil? (domain-size 'Keyword tenv)))))

(deftest a-collection-inside-a-collection-is-smaller-but-its-scalars-are-not
  (let [tenv (spec/type-env 'writ.spec-demo.racks-spec)
        g (spec/type->gen 'Racks tenv)
        vs (for [i (range 200)] (clojure.test.check.generators/generate g 50 i))
        qs (mapcat (comp vals :queues) vs)
        ns (map :n (mapcat (comp vals :items) vs))]
    (is (every? #(<= (count %) 4) qs))
    (is (some #(>= (count %) 3) qs))
    (is (some #(> % 20) ns))
    (is (every? #(<= (count (:items %)) 3) vs))
    (is (some #(= 3 (count (:items %))) vs))
    (is (some #(= 3 (count (:queues %))) vs))))

(deftest a-check-of-few-valued-keys-passes
  (let [r (spec/check 'writ.spec-demo.racks-spec {:seed 1})]
    (is (:ok r) (:message r))))

(deftest a-vector-in-a-map-gets-the-root-of-the-size
  (let [tenv (spec/type-env 'writ.spec-demo.racks-spec)
        g (spec/type->gen '(Map Slot (Vec Nat)) tenv)
        vs (for [i (range 200)] (clojure.test.check.generators/generate g 50 i))
        qs (mapcat vals vs)]
    (is (every? #(<= (count %) 3) vs))
    (is (every? #(<= (count %) 7) qs))
    (is (some #(>= (count %) 5) qs))
    (is (some #(> % 20) (apply concat qs)))))

;; --- draws made with a fixed seed are made once ----------------------------------

(def ^:private draw @#'spec/draw)

(deftest a-draw-with-the-same-type-size-and-seed-is-made-once
  (let [tenv (spec/type-env 'writ.spec-demo.racks-spec)
        ctx {:tenv tenv :draws (atom {})}
        a (draw ctx 'Racks 30 7)]
    (is (identical? a (draw ctx 'Racks 30 7)))
    (is (= a (draw {:tenv tenv} 'Racks 30 7)))
    (is (not= a (draw ctx 'Racks 30 8)))))

(deftest a-nested-quantifier-draws-the-same-values-each-time
  (let [ctx {:tenv {} :vars [] :ev (fn [vars term env] (apply (eval (list 'fn (vec vars) term)) (map env vars)))}
        p '(forall [x Nat] (< x 3))
        runs (repeatedly 5 #(spec/holds ctx p {}))]
    (is (= :fail (:result (first runs))))
    (is (apply = runs))))

;; --- laws run in parallel ---------------------------------------------------------

(def ^:private par-map @#'spec/par-map)

(deftest a-parallel-map-keeps-order-and-rethrows
  (is (= (map inc (range 100)) (par-map inc (range 100))))
  (is (= [] (par-map inc [])))
  (is (thrown-with-msg? Exception #"boom"
        (par-map #(if (= 7 %) (throw (ex-info "boom" {})) %) (range 20)))))

(deftest laws-checked-in-parallel-come-out-as-they-do-one-at-a-time
  (doseq [s '[writ.spec-demo.sort-spec writ.spec-demo.total-spec writ.spec-demo.gap-spec]]
    (let [view (fn [r] [(:ok r) (mapv #(select-keys % [:law :status :lemmas :proof :counterexample]) (:laws r))
                        (:gaps r)])
          par (spec/check s {:seed 42 :cache false})
          one (spec/check s {:seed 42 :cache false :parallel false})]
      (is (:ok par) (:message par))
      (is (= (view one) (view par)) (str s)))))

(deftest stand-ins-judged-in-parallel-come-out-as-they-do-one-at-a-time
  (doseq [s '[writ.spec-demo.sort-spec writ.spec-demo.racks-spec writ.spec-demo.bulk-weak-spec]]
    (let [view (fn [r] [(:gaps r) (:rejected r) (:silent r)])
          real (do (require 'writ.spec-demo.racks) @(resolve 'writ.spec-demo.racks/put))
          par (spec/check s {:seed 42 :adequacy :mutants})
          one (spec/check s {:seed 42 :adequacy :mutants :parallel false})]
      (is (= (view one) (view par)) (str s))
      (is (identical? real @(resolve 'writ.spec-demo.racks/put)) "the target's fns are restored"))))

;; --- refinements built to fit ---------------------------------------------------

(def ^:private fitting @#'spec/fitting)

(deftest a-refinement-sets-the-fields-its-predicate-pins
  (let [tenv (spec/type-env 'writ.spec-demo.parcel-spec)
        r #(get-in tenv [:writ.spec/refines %])
        o {:status :shipped :total 7 :paid 3 :refunded 2}]
    (is (= {:status :placed :total 7 :paid 0 :refunded 0} ((fitting (r 'Placed) tenv) o)))
    (testing "a field equal to another takes its value"
      (is (= {:status :paid :total 7 :paid 7 :refunded 0} ((fitting (r 'Paid) tenv) o))))
    (testing "a tuple's positions"
      (is (= [:open 4] ((fitting (r 'Ticket) tenv) [:x 4]))))
    (testing "nothing to set"
      (is (nil? (fitting (r 'Parcel) tenv))))))

(deftest values-built-to-fit-are-of-their-refinement
  (let [tenv (spec/type-env 'writ.spec-demo.parcel-spec)]
    (doseq [t '[Placed Paid Ticket]]
      (let [vs (for [i (range 100)] (clojure.test.check.generators/generate (spec/type->gen t tenv) (mod i 30) i))]
        (is (every? #(spec/conforms? t % tenv) vs) (str t))
        (is (< 5 (count (distinct vs))) (str t))))))

(deftest a-spec-of-fitted-states-passes
  (let [r (spec/check 'writ.spec-demo.parcel-spec {:seed 1})]
    (is (:ok r) (:message r))))

;; --- the prover inducts where the code recurses -----------------------------------

(deftest no-induction-on-a-number-no-code-recurses-on
  (let [r (spec/check 'writ.spec-demo.racks-spec {:seed 1 :cache false :explain true :adequacy false})
        names (set (mapcat #(map :name (:attempts %)) (:laws r)))]
    (is (seq names))
    (is (not-any? #(and (vector? %) (#{:induct :climb} (first %)) (#{'s 'n} (second %))) names) (pr-str names))))

(deftest induction-on-a-number-a-loop-counts-down-is-still-tried
  (let [r (spec/check 'writ.spec-demo.climb-spec {:seed 1 :cache false})]
    (is (:ok r) (:message r))))

;; --- cache files written whole -----------------------------------------------------

(def ^:private spit-whole! @#'spec/spit-whole!)

(deftest a-file-written-at-once-by-many-checks-is-one-of-them-whole
  (let [dir (java.io.File. (str (System/getProperty "java.io.tmpdir") "/writ-spit-" (System/nanoTime)))
        f (java.io.File. dir "c.edn")
        texts (vec (for [i (range 8)] (pr-str {:i i :pad (vec (range 2000))})))]
    (.mkdirs dir)
    (run! deref (doall (for [t texts] (future (dotimes [_ 20] (spit-whole! f t))))))
    (is (contains? (set texts) (slurp f)))
    (is (= ["c.edn"] (vec (.list dir))) "no temporary file is left")))

;; --- a refinement that starved says so at once after ------------------------------

(def ^:private filtered @#'spec/filtered)
(def ^:private such-that-opts @#'spec/such-that-opts)
(def ^:private remembering-starved @#'spec/remembering-starved)

(deftest a-filter-that-meets-few-sizable-values-starves
  (let [g (filtered #(= 7 %) clojure.test.check.generators/large-integer (such-that-opts 'Zero))
        msg (some #(try (clojure.test.check.generators/generate g 30 %) nil
                        (catch Exception e (ex-message e)))
                  (range 2000))]
    (is (re-find #"could not generate a value of refinement `Zero`" (str msg)))
    (is (re-find #"candidates of size 20 or more" (str msg)))
    (is (re-find #"\{:build f\}" (str msg)))))

(deftest a-refinement-that-starved-fails-its-next-draw-at-once
  (let [g (remembering-starved (filtered #(= 7 %) clojure.test.check.generators/large-integer (such-that-opts 'Zero)))
        draw! #(try (clojure.test.check.generators/generate g 30 %) nil
                    (catch Exception e (ex-message e)))
        first-msg (some draw! (range 2000))
        t0 (System/currentTimeMillis)
        again (draw! 5000)]
    (is first-msg)
    (is (= first-msg again))
    (is (< (- (System/currentTimeMillis) t0) 100))))

(deftest a-filtered-value-is-never-drawn-past-the-largest-size
  (let [g (filtered #(> (count %) 150) (clojure.test.check.generators/vector clojure.test.check.generators/nat)
                    {:max-tries 5000 :ex-fn (fn [_] (ex-info "none" {}))})
        v (clojure.test.check.generators/generate g 0 1)]
    (is (<= 151 (count v) 200))))
