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

(deftest a-guard-inside-and-or-proves-descent
  (testing "each conjunct of an `and` holds in its then branch"
    (is (ck/check-defn
          '(defn digits {:writ/descend true} [^:many ^Nat fuel ^:many ^Nat n]
             (if (and (pos? fuel) (pos? n)) (digits (dec fuel) (quot n 10)) n)))))
  (testing "each disjunct of an `or` fails in its else branch"
    (is (ck/check-defn
          '(defn digits {:writ/descend true} [^:many ^Nat fuel ^:many ^Nat n]
             (if (or (zero? n) (not (pos? fuel))) n (digits (dec fuel) (quot n 10)))))))
  (testing "an `or` proves nothing in its then branch"
    (is (re-find #"does not descend"
                 (check-err '(defn f {:writ/descend true} [^:many ^Nat a ^:many ^Bool b]
                               (if (or (pos? a) b) (f (dec a) b) b)))))))

(deftest a-counter-climbing-to-a-bound-descends
  (testing "(inc i) under (< i n), n fixed and an integer: n - i shrinks"
    (is (ck/check-defn
          '(defn find-at {:writ/descend true} [^:many ^{:writ/type (Vec Nat)} xs ^:many ^Nat start]
             (let [n (count xs)]
               (loop [^:many i start]
                 (if (< i n)
                   (if (zero? (nth xs i)) i (recur (inc i)))
                   nil))))))
    (is (ck/check-defn
          '(defn up {:writ/descend true} [^:many ^Nat i ^:many ^Nat n]
             (if (>= i n) i (up (inc i) n)))))
    (is (ck/check-defn
          '(defn up-count {:writ/descend true} [^:many ^{:writ/type (Vec Nat)} xs ^:many ^Nat i]
             (if (< i (count xs)) (up-count xs (+ i 1)) i)))))
  (testing "a bound that moves with the counter does not"
    (is (re-find #"does not descend"
                 (check-err '(defn chase {:writ/descend true} [^:many ^Nat i ^:many ^Nat n]
                               (if (< i n) (chase (inc i) (inc n)) i))))))
  (testing "a bound that is not an integer does not: it may be ##Inf"
    (is (re-find #"does not descend"
                 (check-err '(defn to-x {:writ/descend true} [^:many ^Nat i ^:many x]
                               (if (< i x) (to-x (inc i) x) i))))))
  (testing "a counter that is not an integer does not"
    (is (re-find #"does not descend"
                 (check-err '(defn from-x {:writ/descend true} [^:many i ^:many ^Nat n]
                               (if (< i n) (from-x (inc i) n) i)))))))

(deftest a-loop-over-a-sorted-view-of-a-records-map-descends
  ;; (vals (:lots s)) of a typed record is finite, and so is what sort-by
  ;; and filter make of it, bound by a let before the loop rebinds it
  (binding [ck/*affine* false ck/*descend-all* true]
    (is (ck/check-defn
          '(defn plan [^{:writ/type {:lots (Map Nat {:id Nat :qty Nat :expires Nat}) :next-id Nat}} s
                       ^Nat n]
             (let [lots (sort-by :expires (filter #(pos? (:qty %)) (vals (:lots s))))]
               (loop [lots lots need n out []]
                 (cond
                   (zero? need) out
                   (empty? lots) nil
                   :else (let [l (first lots) k (min need (:qty l))]
                           (recur (rest lots) (- need k) (conj out [(:id l) k]))))))))))
  (testing "an untyped one may be a lazy seq that never runs out"
    (binding [ck/*affine* false ck/*descend-all* true]
      (is (re-find #"must be a finite collection"
                   (check-err '(defn walk-on [xs]
                                 (let [ys (filter odd? xs)]
                                   (loop [ys ys] (if (empty? ys) nil (recur (rest ys))))))))))))
