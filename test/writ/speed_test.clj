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
