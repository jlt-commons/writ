(ns writ.check-test
  (:require [clojure.test :refer [deftest is testing]]
            [writ.check :as ck]
            [writ.defn :as w]))

(w/defn inc-annotated [x :- Nat] (inc x))

(defn- check-err [form]
  (try (ck/check-defn form) nil
       (catch Exception ex (.getMessage ex))))

(deftest affine-used-once-passes
  (is (ck/check-defn '(defn id [x] x))))

(deftest affine-used-twice-is-rejected
  (testing "a plain parameter is affine and may not be duplicated"
    (let [m (check-err '(defn dup [x] (+ x x)))]
      (is (some? m))
      (is (re-find #"used more than once" m)))))

(deftest reusable-parameter-may-be-copied
  (is (ck/check-defn '(defn dup [^:many ^Nat x] (+ x x)))))

(deftest erased-parameter-must-be-dropped
  (testing "an erased parameter may not be used at runtime"
    (let [m (check-err '(defn f [^:zero x] (inc x)))]
      (is (some? m))
      (is (re-find #"used once but is declared erased" m)))))

(deftest branches-join
  (testing "a use in each arm of an if is one use per path"
    (is (ck/check-defn '(defn pick [c x] (if c x x))))))

(deftest sequential-uses-add
  (testing "using a name on both sides of a let is two uses"
    (let [m (check-err '(defn f [x] (let [y x] (+ x y))))]
      (is (some? m)))))

(deftest descent-accepted-when-structurally-smaller
  (is (ck/check-defn
        '(defn add {:writ/descend true} [^:many ^Nat a b]
           (if (zero? a) b (add (dec a) b))))))

(deftest descent-allows-unchanged-leading-argument
  (testing "a recursive call may pass an earlier argument through unchanged"
    (is (ck/check-defn
          '(defn walk {:writ/descend true} [^:many ^Nat x ^:many ^{:writ/type (List Nat)} xs]
             (if (seq xs) (let [t (rest xs)] (walk x t)) x))))))

(deftest non-descending-recursion-is-rejected
  (testing "a marked def must shrink on every recursive call"
    (let [m (check-err '(defn f {:writ/descend true} [a] (f a)))]
      (is (some? m))
      (is (re-find #"does not descend" m)))))

(deftest w-defn-macro-checks-and-expands
  (testing "the macro runs the checker at compile time and yields a real fn"
    (is (= 2 (inc-annotated 1)))))

(deftest w-defn-quantity-signature
  (testing ":- annotations feed the same checker"
    (is (w/check 'add '[^Nat a :- :omega b :- Nat]
                  '((if (zero? a) b (+ a b))))))
  (testing "a bad :- quantity is rejected"
    (let [m (try (w/check 'bad '[x :- :zero] '(inc x)) nil
                 (catch Exception ex (.getMessage ex)))]
      (is (some? m))
      (is (re-find #"erased" m)))))

(deftest w-defn-expands-to-plain-defn
  (let [form (w/build 'inc2 '[x :- Nat] '((inc x)))]
    (is (= 'clojure.core/defn (first form)))
    (is (= 'inc2 (second form)))))

(defn- check-msg [nm params body]
  (try (w/check nm params body) nil
       (catch Exception ex (.getMessage ex))))

(deftest reusable-binder-needs-data-kind
  (testing "a reusable binder over a ground type is fine"
    (is (w/check 'dup '[^:many x :- Nat] '((+ x x)))))
  (testing "a reusable binder over a function type is rejected"
    (let [m (check-msg 'twice '[^:many g :- (-> Nat Nat)] '((g (g 1))))]
      (is (some? m))
      (is (re-find #"is not Data" m)))))

(w/data NatBox (NatBox Nat))
(w/data FnBox (FnBox (-> Nat Nat)))

(deftest reusable-binder-kind-is-transitive
  (testing "a datatype of data fields may be reused"
    (is (w/check 'unbox '[^:many b :- NatBox] '(b))))
  (testing "a datatype with a function field has kind Type, so may not be reused"
    (let [m (check-msg 'hold '[^:many b :- FnBox] '(b))]
      (is (some? m))
      (is (re-find #"is not Data" m)))))

(deftest builtin-type-constructors
  (testing "List, Tuple and & are well-kinded at the right arity"
    (is (w/check 'f '[x :- (List Nat)] '(x)))
    (is (w/check 'g '[p :- (Tuple Nat Bool)] '(p)))
    (is (w/check 'h2 '[p :- (List (-> Nat Nat))] '(p))))
  (testing "a bare constructor needs its arguments"
    (let [m (check-msg 'f '[x :- List] '(x))]
      (is (some? m))
      (is (re-find #"type constructor" m))))
  (testing "the wrong number of arguments is rejected"
    (let [m (check-msg 'f '[x :- (List Nat Bool)] '(x))]
      (is (some? m))
      (is (re-find #"1 type argument" m)))))

(deftest multi-value-return-is-a-product
  (is (w/check 'split '[x :- Nat] '(:- (& Nat Nat) [x 0])))
  (testing "a reusable binder over a tuple of data is fine"
    (is (w/check 'dup-t '[^:many p :- (Tuple Nat Nat)] '((p p)))))
  (testing "a reusable binder over a tuple containing a function is not"
    (let [m (check-msg 'bad '[^:many p :- (Tuple Nat (-> Nat Nat))] '(p))]
      (is (some? m))
      (is (re-find #"is not Data" m)))))

(w/data FnLeaf (FnLeaf (-> Nat Nat)))
(w/data FnHolder (FnHolder FnLeaf))
(w/data DataLeaf (DataLeaf Nat))
(w/data DataHolder (DataHolder DataLeaf))

(deftest reusable-binder-kind-is-transitive-at-depth
  (testing "a datatype whose field is itself of kind Data stays reusable"
    (is (w/check 'deep-ok '[^:many b :- DataHolder] '(b))))
  (testing "a function field reaches :Type two levels down"
    (let [m (check-msg 'deep-bad '[^:many b :- FnHolder] '(b))]
      (is (some? m))
      (is (re-find #"is not Data" m)))))

(deftest multi-value-return-arity-edges
  (testing "& and Tuple take one or more type arguments"
    (is (w/check 'one '[x :- (& Nat)] '(x)))
    (is (w/check 'two '[p :- (Tuple Nat)] '(p))))
  (testing "a bare & is a type constructor, not a type"
    (let [m (check-msg 'bare '[x :- &] '(x))]
      (is (some? m))
      (is (re-find #"type constructor" m))))
  (testing "List needs exactly one argument"
    (let [m (check-msg 'none '[x :- (List)] '(x))]
      (is (some? m))
      (is (re-find #"takes 1 type argument" m)))))

(deftest empty-list-literal-is-a-value
  ;; `()` evaluates to the empty list; it is not a call with a nil head
  (is (= {:ok true} (ck/check-defn '(defn f [xs] ()))))
  (is (= {:ok true} (ck/check-defn '(defn f [] ()))))
  (is (= {:ok true} (ck/check-defn '(defn f [x] (if x 1 ()))))))
