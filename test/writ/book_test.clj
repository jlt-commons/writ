(ns writ.book-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [writ.core :as wc]
            [writ.book :as bk]
            [writ.defn :as w]
            [writ.norm :as norm]))

(defn- book-err [forms]
  (try (wc/check-book forms) nil
       (catch Throwable ex (.getMessage ex))))

;; --- data, match, defn through the macros --------------------------------

(w/data MaybeInt Nothing (Just Int))

(w/defn from-maybe [m :- MaybeInt]
  (w/match m :- MaybeInt
    (Nothing 0)
    ((Just x) x)))

(deftest match-macro-expands-to-a-working-fn
  (is (= 0 (from-maybe :Nothing)))
  (is (= 5 (from-maybe [:Just 5]))))

(deftest well-formed-book-passes
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/data MaybeInt Nothing (Just Int))
             (writ.defn/defn from-maybe [m :- MaybeInt]
               (writ.defn/match m :- MaybeInt
                 (Nothing 0)
                 ((Just x) x)))
             (writ.defn/defn add-one [x :- Nat] :- Nat (inc x))
             (writ.defn/law add-zero (forall [n Nat] (= (+ n 0) n)))
             (writ.defn/proof add-zero-refl add-zero (fn [n] refl))]))))

;; --- match discipline ----------------------------------------------------

(deftest non-exhaustive-match-is-rejected
  (let [m (book-err '[(writ.defn/data MaybeInt Nothing (Just Int))
                      (writ.defn/defn f [m :- MaybeInt]
                        (writ.defn/match m :- MaybeInt (Nothing 0)))])]
    (is (some? m))
    (is (re-find #"not exhaustive" m))))

(deftest repeated-constructor-is-rejected
  (let [m (book-err '[(writ.defn/data MaybeInt Nothing (Just Int))
                      (writ.defn/defn f [m :- MaybeInt]
                        (writ.defn/match m :- MaybeInt
                          (Nothing 0) (Nothing 1) ((Just x) x)))])]
    (is (some? m))
    (is (re-find #"repeats a constructor" m))))

(deftest unknown-constructor-is-rejected
  (let [m (book-err '[(writ.defn/data MaybeInt Nothing (Just Int))
                      (writ.defn/defn f [m :- MaybeInt]
                        (writ.defn/match m :- MaybeInt
                          (Nope 0) ((Just x) x)))])]
    (is (some? m))
    (is (re-find #"not a constructor" m))))

(deftest pattern-arity-is-checked
  (let [m (book-err '[(writ.defn/data MaybeInt Nothing (Just Int))
                      (writ.defn/defn f [m :- MaybeInt]
                        (writ.defn/match m :- MaybeInt
                          (Nothing 0) ((Just x y) x)))])]
    (is (some? m))
    (is (re-find #"field" m))))

;; --- live / dead demand --------------------------------------------------

(deftest erased-binders-may-appear-in-types
  (testing "types are checked dead (BendTT 2.4), so an erased binder may
            appear in one; a live use of it is still refused"
    (is (nil? (book-err '[(writ.defn/defn f [^:zero x] :- x 0)])))
    (is (re-find #"erased" (book-err '[(writ.defn/defn f [^:zero x] :- x x)])))))

;; --- kind lattice --------------------------------------------------------

(deftest bare-arity-zero-type-is-accepted
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/data MaybeInt Nothing (Just Int))
             (writ.defn/defn f [^:zero m :- MaybeInt] :- Nat 0)]))))

(deftest wrong-type-arity-is-rejected
  (let [m (book-err '[(writ.defn/data Box [a] (Wrap a))
                      (writ.defn/defn f [x :- (Box Int Int)] :- Int 0)])]
    (is (some? m))
    (is (re-find #"takes 1 type argument" m))))

(deftest constructor-used-as-a-type-is-rejected
  (let [m (book-err '[(writ.defn/data Box [a] (Wrap a))
                      (writ.defn/defn f [x :- (Wrap Int)] :- Int 0)])]
    (is (some? m))
    (is (re-find #"not a declared type" m))))

;; --- conversion / normalisation ------------------------------------------

(deftest convertibility
  (is (binding [norm/*numeric* #{'x}] (norm/convertible? '(+ x 0) 'x)))
  (is (not (norm/convertible? '(+ x 0) 'x)) "an untyped x may not be a number")
  (is (norm/convertible? '(+ 1 2) 3))
  (is (not (norm/convertible? '(+ x 0) '(inc x)))))

;; --- law / proof gate ----------------------------------------------------

(deftest unfilled-law-is-rejected
  (let [m (book-err '[(writ.defn/law foo (= a b))])]
    (is (some? m))
    (is (re-find #"is not filled" m))))

(deftest proof-of-unknown-law-is-rejected
  (let [m (book-err '[(writ.defn/proof p missing refl)])]
    (is (some? m))
    (is (re-find #"discharges no law" m))))

(deftest non-convertible-refl-is-rejected
  (let [m (book-err '[(writ.defn/law foo (= (+ x 0) (inc x)))
                      (writ.defn/proof p foo refl)])]
    (is (some? m))
    (is (re-find #"not convertible" m))))

(deftest convertible-refl-passes
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/law add-zero (forall [n Nat] (= (+ n 0) n)))
             (writ.defn/proof add-zero-refl add-zero (fn [n] refl))]))))

;; --- richer propositions and proof terms ---------------------------------

(deftest implication-reuses-a-hypothesis
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/law refl-imp (=> (= a b) (= a b)))
             (writ.defn/proof refl-imp-p refl-imp (fn [h] h))]))))

(deftest implication-cannot-conclude-something-else
  (let [m (book-err '[(writ.defn/law bad (=> (= a b) (= a c)))
                      (writ.defn/proof p bad (fn [h] h))])]
    (is (some? m))
    (is (re-find #"not `" m))))

(deftest conjunction-is-proved-by-pair
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/law both (and (= a a) (= b b)))
             (writ.defn/proof both-p both (pair refl refl))])))
  (let [m (book-err '[(writ.defn/law one (and (= a a) (= b b)))
                      (writ.defn/proof p one (pair refl))])]
    (is (some? m))
    (is (re-find #"proposition" m))))

(deftest conjunction-is-not-proved-by-refl
  (let [m (book-err '[(writ.defn/law both (and (= a a) (= b b)))
                      (writ.defn/proof p both refl)])]
    (is (some? m))
    (is (re-find #"pair" m))))

(deftest universal-is-proved-by-a-fn
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/law add-zero-all (forall [x Nat] (= (+ x 0) x)))
             (writ.defn/proof p add-zero-all (fn [x] refl))]))))

(deftest existential-is-proved-by-a-witness
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/law some-zero (exists [x Nat] (= (+ x 0) x)))
             (writ.defn/proof p some-zero (witness 5 refl))]))))

(deftest a-law-may-be-cited-as-a-lemma
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/law base (= a a))
             (writ.defn/proof base-p base refl)
             (writ.defn/law reuse (= a a))
             (writ.defn/proof reuse-p reuse base)]))))

(deftest universal-without-a-fn-is-rejected
  (let [m (book-err '[(writ.defn/law all-nat (forall [x Nat] (= (+ x 0) x)))
                      (writ.defn/proof p all-nat refl)])]
    (is (some? m))
    (is (re-find #"a universal is proved by" m))))

(deftest existential-without-a-witness-is-rejected
  (let [m (book-err '[(writ.defn/law some-nat (exists [x Nat] (= (+ x 0) x)))
                      (writ.defn/proof p some-nat refl)])]
    (is (some? m))
    (is (re-find #"an existential is proved by" m))))

(deftest witness-must-supply-a-proof
  (let [m (book-err '[(writ.defn/law some-nat (exists [x Nat] (= (+ x 0) (inc x))))
                      (writ.defn/proof p some-nat (witness 5 refl))])]
    (is (some? m))
    (is (re-find #"not convertible" m))))

(deftest implication-without-a-fn-is-rejected
  (let [m (book-err '[(writ.defn/law imp (=> (= a b) (= a b)))
                      (writ.defn/proof p imp refl)])]
    (is (some? m))
    (is (re-find #"an implication is proved by" m))))

;; --- reader and malformed input ------------------------------------------

(deftest malformed-match-is-a-writ-error
  (testing "a short match form fails with a Writ: message, not an index error"
    (let [m (book-err '[(writ.defn/defn f [x] (writ.defn/match x))])]
      (is (some? m))
      (is (re-find #"^Writ: a `match` needs" m)))))

(deftest read-forms-tolerates-stray-brackets
  (testing "a stray ] or ) inside a docstring or comment does not break reading"
    (let [p (str (System/getProperty "java.io.tmpdir") "/writ-read-forms-test.clj")]
      (spit p "(ns t \"docstring with a stray ] and ) bracket\")\n;; comment ] )\n(def x 1)\n(def y [1 2 3])\n")
      (try
        (is (= 3 (count (bk/read-forms p))))
        (finally (io/delete-file p true))))))
