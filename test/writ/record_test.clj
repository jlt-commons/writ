(ns writ.record-test
  "Records: a map with named keys is a type, each key with its own type,
  and (Opt T) marks a key that may be absent or nil."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]
            [writ.kind :as kind]
            [writ.types :as types]
            [writ.prove.rewrite :as rw]
            [writ.prove.check :as chk]
            [writ.prove]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]))

(defn- has? [r s] (str/includes? (:message r) s))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(deftest a-record-generates-maps-with-its-keys
  (let [vs (spec/sample '{:id Nat, :email String} {} 50)]
    (is (every? map? vs))
    (is (every? #(nat-int? (:id %)) vs))
    (is (every? #(string? (:email %)) vs))
    (is (every? #(= #{:id :email} (set (keys %))) vs))))

(deftest an-opt-key-is-sometimes-absent-sometimes-nil-sometimes-set
  (let [vs (spec/sample '{:id Nat, :nick (Opt String)} {} 200)]
    (is (some #(not (contains? % :nick)) vs))
    (is (some #(and (contains? % :nick) (nil? (:nick %))) vs))
    (is (some #(string? (:nick %)) vs))
    (is (every? #(or (nil? (:nick %)) (string? (:nick %))) vs))))

(deftest opt-alone-is-a-value-or-nil
  (let [vs (spec/sample '(Opt Nat) {} 100)]
    (is (some nil? vs))
    (is (some nat-int? vs))))

(deftest a-record-conforms-by-key
  (let [t '{:id Nat, :nick (Opt String)}]
    (is (spec/conforms? t {:id 1} {}))
    (is (spec/conforms? t {:id 1 :nick nil} {}))
    (is (spec/conforms? t {:id 1 :nick "x"} {}))
    (testing "other keys are allowed: a map is open"
      (is (spec/conforms? t {:id 1 :extra [1 2]} {})))
    (is (not (spec/conforms? t {:nick "x"} {})) "a required key is missing")
    (is (not (spec/conforms? t {:id -1} {})) "a key's value is the wrong type")
    (is (not (spec/conforms? t {:id 1 :nick 5} {})))
    (is (not (spec/conforms? t [1] {})))))

(deftest a-record-is-a-well-formed-type
  (is (kind/check-type '{:id Nat, :tags (List Keyword), :nick (Opt String)} {} #{}))
  (is (thrown-with-msg? Exception #"`Foo` is not a type"
        (kind/check-type '{:id Foo} {} #{})))
  (is (thrown-with-msg? Exception #"a record's keys are keywords"
        (kind/check-type '{id Nat} {} #{})))
  (is (thrown-with-msg? Exception #"`Opt` takes 1 type argument"
        (kind/check-type '(Opt Nat String) {} #{}))))

(deftest a-spec-over-records-passes
  (let [r (spec/check 'writ.spec-demo.member-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (empty? (:gaps r)))))

(deftest a-record-missing-a-key-is-caught-where-it-is-made
  (let [r (spec/check 'writ.spec-demo.member-spec {:seed 42 :target 'writ.spec-demo.member-lossy})]
    (is (not (:ok r)))
    (is (has? r "`join` returns Member"))))

;; --- the prover's map rules -------------------------------------------------------

(defn- norm [types x] (rw/normalize (rw/context {:types types}) x))

(defn- run-term
  "The value of a map term, with env giving its variables."
  [env x]
  (cond
    (symbol? x) (get env x)
    :else
    (case (first x)
      :lit (second x)
      :nil nil
      :if (if (run-term env (nth x 1)) (run-term env (nth x 2)) (run-term env (nth x 3)))
      :call (apply (case (second x) get get, assoc assoc, dissoc dissoc, contains? contains?,
                     hash-map hash-map, = =)
                   (map #(run-term env %) (drop 2 x))))))

(def ^:private map-gen
  (gen/one-of [(gen/return nil)
               (gen/map (gen/elements [:a :b :c]) gen/small-integer)]))

(def ^:private op-gen
  "A term over map m and values v, w: gets, assocs, dissocs and contains?
  on literal keys, nested."
  (let [k (gen/fmap #(vector :lit %) (gen/elements [:a :b :c]))
        mterm (gen/recursive-gen
                (fn [inner]
                  (gen/one-of [(gen/fmap (fn [[m k v]] [:call 'assoc m k v]) (gen/tuple inner k (gen/elements '[v w])))
                               (gen/fmap (fn [[m k]] [:call 'dissoc m k]) (gen/tuple inner k))]))
                (gen/elements '[m [:nil] [:call hash-map [:lit :a] v]]))]
    (gen/one-of [(gen/fmap (fn [[m k]] [:call 'get m k]) (gen/tuple mterm k))
                 (gen/fmap (fn [[m k]] [:call 'get m k [:lit :none]]) (gen/tuple mterm k))
                 (gen/fmap (fn [[m k]] [:call 'contains? m k]) (gen/tuple mterm k))
                 mterm])))

(deftest the-map-rules-agree-with-the-runtime
  (let [r (tc/quick-check 500
            (prop/for-all [x op-gen, m map-gen, v gen/small-integer, w gen/small-integer]
              (let [env {'m m 'v v 'w w}]
                ;; m is a map only when it is not nil
                (= (run-term env x) (run-term env (norm (if m '{m {:a Int}} {}) x)))))
            :seed 42)]
    (is (:pass? r) (pr-str (:shrunk r)))))

(deftest a-lookup-sees-through-assoc-and-dissoc
  (is (= 'v (norm {} [:call 'get [:call 'assoc 'm [:lit :a] 'v] [:lit :a]])))
  (is (= [:call 'get 'm [:lit :b]] (norm {} [:call 'get [:call 'assoc 'm [:lit :a] 'v] [:lit :b]])))
  (is (= [:nil] (norm {} [:call 'get [:call 'dissoc 'm [:lit :a]] [:lit :a]])))
  (is (= [:call 'dissoc 'm [:lit :a]] (norm '{m {:a Int}} [:call 'dissoc [:call 'assoc 'm [:lit :a] 'v] [:lit :a]])))
  (testing "on nil the assoc leaves {}, not nil, so m must be a map"
    (is (= :call (first (norm {} [:call 'dissoc [:call 'assoc 'm [:lit :a] 'v] [:lit :a]])))))
  (is (= [:lit true] (norm {} [:call 'contains? [:call 'assoc 'm [:lit :a] 'v] [:lit :a]]))))

(deftest laws-over-records-are-proved
  (let [r (spec/check 'writ.spec-demo.member-spec {:seed 42})]
    (is (:ok r) (:message r))
    (doseq [l '[award-adds award-touches-only-points the-nick-when-set the-email-otherwise
                membership:fresh:award membership:active:award]]
      (is (= :proved (:status (law-result r l))) (str l ": " (:unproved (law-result r l)))))))

(deftest a-record-is-never-split-as-a-list
  (testing "the search does not take a record binder for a list of elements"
    (is (= 'xs (#'writ.prove/elems-var {:types '{m {:a Nat} xs {:writ/elems Nat}}}
                                       [:call '= 'm 'xs]))))
  (testing "the checker refuses a proof that splits one"
    (let [r (chk/check-proof {:types '{m {:a Nat}}}
                             {:hyps [] :goals [[:call 'map? 'm]]}
                             {:by :cases :proofs [{:by :list-cases :on 'm
                                                   :empty {:by :rewriting} :cons {:by :rewriting}}]})]
      (is (not (:ok r)))
      (is (str/includes? (str (:reason r)) "is not a list of elements")))))

;; --- the static check -------------------------------------------------------------

(defn- static-error [target]
  (let [r (spec/check 'writ.spec-demo.member-spec {:seed 42 :target target})]
    (is (not (:ok r)))
    (is (not (:ok (:static r))) (:message r))
    (:message r)))

(deftest reading-a-key-the-record-does-not-have-fails
  (let [m (static-error 'writ.spec-demo.member-typo)]
    (is (str/includes? m "`award`"))
    (is (str/includes? m "has no key :point"))
    (is (str/includes? m ":email, :id, :nick, :points"))))

(deftest a-record-missing-a-required-key-fails
  (let [m (static-error 'writ.spec-demo.member-partial)]
    (is (str/includes? m "`join`"))
    (is (str/includes? m "leaves out :points"))))

(deftest an-opt-key-is-not-its-type
  (let [m (static-error 'writ.spec-demo.member-nil)]
    (is (str/includes? m "`nickname` returns String but its body has type (Opt String)"))))

(deftest a-key-of-the-wrong-type-fails
  (let [m (static-error 'writ.spec-demo.member-badtype)]
    (is (str/includes? m "`join`"))
    (is (str/includes? m ":points is Nat, but the body gives String"))))

(deftest destructured-keys-are-typed-and-proved
  (let [r (spec/check 'writ.spec-demo.member-spec {:seed 42 :target 'writ.spec-demo.member-destructure})]
    (is (:ok r) (:message r))
    (is (every? #(#{:proved :witnessed :evaluated} (:status %)) (:laws r))
        (pr-str (map (juxt :law :status) (:laws r))))))

(deftest a-datatype-can-hold-a-record-of-itself
  (let [tenv (#'writ.spec/tenv-of '[(data Tree (Leaf) (Node {:left Tree, :v Nat, :right Tree}))])
        vs (spec/sample 'Tree tenv 30)]
    (is (some #(= [:Leaf] %) vs))
    (is (some #(= :Node (first %)) vs))
    (is (every? #(spec/conforms? 'Tree % tenv) vs))
    (testing "the record's field is seen to recurse: at size 0 only a leaf"
      (is (every? #(= [:Leaf] %) (repeatedly 40 #(gen/generate (spec/type->gen 'Tree tenv) 0)))))))

(deftest a-record-literal-fits-a-map-type
  (is (types/compat? '(Map Keyword Nat) '{:a Nat, :b Nat} {}))
  (is (not (types/compat? '(Map Keyword Nat) '{:a Nat, :b String} {})))
  (is (not (types/compat? '(Map String Nat) '{:a Nat} {}))))

;; --- symbolic evaluation of records -----------------------------------------------

(deftest edges-on-records-are-proved-never-to-throw
  (let [r (spec/check 'writ.spec-demo.member-spec {:seed 42 :cache false})]
    (is (:ok r) (:message r))
    (is (str/includes? (:message r) "law `membership:fresh:award` proved by symbolic evaluation, with the solver, and it never throws")
        (:message r))))

(deftest a-law-true-only-of-exact-maps-is-not-proved
  (let [r (spec/check 'writ.spec-demo.exact-spec {:seed 42 :adequacy false :cache false})]
    (is (= :tested (:status (law-result r 'an-award-has-its-keys-and-no-more))) (:message r))
    (is (= :tested (:status (law-result r 'an-award-is-its-keys))) (:message r))))

(deftest the-solver-finds-a-record-no-test-does
  (let [r (spec/check 'writ.spec-demo.member-spec {:seed 42 :target 'writ.spec-demo.member-big :cache false})]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "found by the solver") (:message r))
    (is (re-find #":points 10\d\d" (:message r)))))
