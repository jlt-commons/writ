(ns writ.gaps-test
  "Tests for the gaps found in the BendTT-parity review.
  Each block names the gap: lowering, weakening, local quantities,
  descent sources, recur, mandatory marking, parametric kinds,
  match provenance/parametric/binders, law-gate citations, book ordering."
  (:require [clojure.test :refer [deftest is testing]]
            [writ.check :as ck]
            [writ.defn :as w]
            [writ.core :as wc]))

(defn- err-msg [form]
  (try (ck/check-defn form) nil
       (catch Throwable t (.getMessage t))))

(defn- check-msg [nm params body]
  (try (w/check nm params body) nil
       (catch Throwable t (.getMessage t))))

(defn- book-err [forms]
  (try (wc/check-book forms) nil
       (catch Throwable t (.getMessage t))))

;; --- G1: nameless fn bodies must not vanish from the AST ------------------

(deftest nameless-fn-body-is-lowered
  (testing "an erased param used inside a nameless fn is caught"
    (let [m (check-msg 'bad '[^:zero x :- Nat] '((count ((fn [y] (+ x y))))))]
      (is (some? m))
      (is (re-find #"erased" m))))
  (testing "an affine param used twice inside a nameless fn is caught"
    (let [m (check-msg 'bad '[x :- Nat] '((count ((fn [y] (+ x x))))))]
      (is (some? m))
      (is (re-find #"more than once" m)))))

;; --- G2: weakening (BendTT: pi(x) <= q, so 0 uses is legal) ---------------

(deftest unused-affine-param-is-weakening
  (is (ck/check-defn '(defn konst [x] 0)))
  (is (ck/check-defn '(defn f [_ x] x))))

;; --- G3: local binders carry quantities too -------------------------------

(deftest local-used-twice-is-rejected
  (testing "a plain let binding is affine"
    (let [m (err-msg '(defn f [x] (let [y (inc x)] (+ y y))))]
      (is (some? m))
      (is (re-find #"more than once" m))))
  (testing "^:many on the local fixes it"
    (is (ck/check-defn '(defn f [x] (let [^:many y (inc x)] (+ y y))))))
  (testing "an erased local may not be used"
    (let [m (err-msg '(defn f [x] (let [^:zero y (inc x)] y)))]
      (is (some? m))
      (is (re-find #"erased" m))))
  (testing "a local may not shadow a parameter"
    (let [m (err-msg '(defn f [x] (let [x 1] x)))]
      (is (some? m))
      (is (re-find #"shadow" m)))))

;; --- G4: descent accepts only parameter-derived shrinkers -----------------

(deftest descent-rejects-computed-locals
  (testing "a constant let local is not smaller"
    (let [m (err-msg '(defn f {:writ/descend true} [a] (let [t 3] (f t))))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "dec of an unrelated local is not smaller"
    (let [m (err-msg '(defn f {:writ/descend true} [a] (let [z 5] (f (dec z)))))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "a local that grows the parameter is not smaller"
    (let [m (err-msg '(defn f {:writ/descend true} [a] (let [t (conj a 1)] (f t))))]
      (is (some? m))
      (is (re-find #"does not descend" m)))))

;; --- G5: recur is termination like any self-call --------------------------

(deftest recur-needs-a-descend-mark-and-must-shrink
  (testing "an unmarked loop/recur is unbounded recursion"
    (let [m (err-msg '(defn spin [x] (loop [y x] (recur y))))]
      (is (some? m))
      (is (re-find #"writ/descend" m))))
  (testing "a marked recur must still shrink"
    (let [m (err-msg '(defn f {:writ/descend true} [a]
                        (loop [^:many y a] (if (zero? y) 0 (recur (inc y))))))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "a marked shrinking recur passes"
    (is (ck/check-defn '(defn f {:writ/descend true} [^Nat a]
                          (loop [^:many y a] (if (zero? y) 0 (recur (dec y)))))))))

;; --- G6: self-recursion must be marked (termination is mandatory) ---------

(deftest unmarked-self-recursion-is-rejected
  (let [m (err-msg '(defn spin [x] (spin x)))]
    (is (some? m))
    (is (re-find #"writ/descend" m))))

;; --- G7: kind flows through type parameters -------------------------------

(w/data ParamBox [a] (Wrap a))

(deftest parametric-kind-propagates
  (testing "Box of a data type is Data, so it may be reused"
    (is (w/check 'ok '[^:many b :- (ParamBox Nat)] '(b))))
  (testing "Box of a function type is Type, so it may not be reused"
    (let [m (check-msg 'bad '[^:many b :- (ParamBox (-> Nat Nat))] '(b))]
      (is (some? m))
      (is (re-find #"is not Data" m)))))

;; --- G8: match provenance, parametric types, binder quantities ------------

(deftest scrutinee-must-be-param-or-pattern-binder
  (testing "a computed let local is not a legal scrutinee"
    (let [m (book-err '[(writ.defn/data MaybeInt Nothing (Just Int))
                        (writ.defn/defn g [m :- MaybeInt]
                          (let [copy (inc m)]
                            (writ.defn/match copy :- MaybeInt
                              (Nothing 0)
                              ((Just x) x))))])]
      (is (some? m))
      (is (re-find #"scrutinee" m)))))

(deftest match-on-a-parametric-type
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/data ParamBox [a] (Wrap a))
             (writ.defn/defn unbox [b :- (ParamBox Nat)] :- Nat
               (writ.defn/match b :- (ParamBox Nat)
                 ((Wrap v) v)))]))))

(deftest pattern-binders-carry-quantities
  (testing "an affine field binder used twice is rejected"
    (let [m (book-err '[(writ.defn/data NatTree (Leaf) (Node Nat NatTree NatTree))
                        (writ.defn/defn sum2 [t :- NatTree] :- Nat
                          (writ.defn/match t :- NatTree
                            (Leaf 0)
                            ((Node v l r) (+ v v))))])]
      (is (some? m))
      (is (re-find #"more than once" m))))
  (testing "^:many on the binder fixes it"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/data NatTree (Leaf) (Node Nat NatTree NatTree))
               (writ.defn/defn sum2 [t :- NatTree] :- Nat
                 (writ.defn/match t :- NatTree
                   (Leaf 0)
                   ((Node ^:many v l r) (+ v v))))])))))

;; --- G9: the law gate: order, proofs-are-not-citable, no duplicates -------

(deftest circular-law-citations-are-rejected
  (testing "two laws citing each other prove nothing"
    (let [m (book-err '[(writ.defn/law loopy-a (= (+ x 0) (inc x)))
                        (writ.defn/law loopy-b (= (+ x 0) (inc x)))
                        (writ.defn/proof pa loopy-a loopy-b)
                        (writ.defn/proof pb loopy-b loopy-a)])]
      (is (some? m))
      (is (re-find #"before it is proved" m)))))

(deftest self-citation-is-rejected
  (let [m (book-err '[(writ.defn/law bad (= (+ x 0) (inc x)))
                      (writ.defn/proof p bad bad)])]
    (is (some? m))
    (is (re-find #"before it is proved" m))))

(deftest nested-forward-citation-is-rejected
  (testing "a law cited inside a proof term must already be proved"
    (let [m (book-err '[(writ.defn/law one (= (+ 0 1) 1))
                        (writ.defn/law two (= 1 (+ 1 0)))
                        (writ.defn/law both (and (= (+ 0 1) 1) (= 1 (+ 1 0))))
                        (writ.defn/proof pb both (pair two refl))
                        (writ.defn/proof p1 one refl)
                        (writ.defn/proof p2 two refl)])]
      (is (some? m))
      (is (re-find #"before it is proved" m)))))

(deftest a-proof-is-not-a-citable-law
  (let [m (book-err '[(writ.defn/law one (= (+ 1 0) 1))
                      (writ.defn/proof p1 one refl)
                      (writ.defn/law two (= (+ x 1) (+ x 1)))
                      (writ.defn/proof p2 two p1)])]
    (is (some? m))
    (is (re-find #"proved by `refl`" m))))

(deftest a-later-law-is-not-yet-proved
  (let [m (book-err '[(writ.defn/law early (= (+ x 0) x))
                      (writ.defn/law late (= (+ x 0) x))
                      (writ.defn/proof p early late)])]
    (is (some? m))
    (is (re-find #"before it is proved" m))))

(deftest duplicate-law-names-are-rejected
  (let [m (book-err '[(writ.defn/law one (= (+ x 0) x))
                      (writ.defn/law one (= (+ x 1) (+ x 1)))
                      (writ.defn/proof p one refl)])]
    (is (some? m))
    (is (re-find #"duplicate law" m))))

(deftest duplicate-proof-of-one-law-is-rejected
  (testing "a law is discharged once; a second proof is redundant"
    (let [m (book-err '[(writ.defn/law one (= (+ 1 0) 1))
                        (writ.defn/proof p1 one refl)
                        (writ.defn/proof p2 one refl)])]
      (is (some? m))
      (is (re-find #"discharged once" m)))))

;; --- G10: defs reference only earlier defs ---------------------------------

(deftest forward-reference-is-rejected
  (let [m (book-err '[(writ.defn/defn a [x :- Nat] (b x))
                      (writ.defn/defn b [x :- Nat] (x))])]
    (is (some? m))
    (is (re-find #"defined later" m))))

(deftest mutual-recursion-is-rejected
  (let [m (book-err '[(writ.defn/defn a [x :- Nat] (b x))
                      (writ.defn/defn b [x :- Nat] (a x))])]
    (is (some? m))
    (is (re-find #"defined later" m))))

(deftest earlier-reference-is-fine
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/defn b [x :- Nat] x)
             (writ.defn/defn a [x :- Nat] (b x))]))))

(deftest referred-names-are-not-unknown
  (testing "an unqualified :refer'd name is external, not a forward reference"
    (is (= {:ok true}
           (wc/check-book
             '[(ns some.book (:require [clojure.string :refer [upper-case]]))
               (writ.defn/defn shout [s :- String] :- String
                 (upper-case s))])))))

(deftest duplicate-binder-in-one-pattern-is-rejected
  (testing "binding one name for two fields loses a value"
    (let [m (book-err '[(writ.defn/data NatTree (Leaf) (Node Nat NatTree NatTree))
                        (writ.defn/defn bad [t :- NatTree] :- Nat
                          (writ.defn/match t :- NatTree
                            (Leaf 0)
                            ((Node v v v) v)))])]
      (is (some? m))
      (is (re-find #"duplicate binder" m)))))

;; --- G11: + never forms over a function type (BendTT 3.1: Omega dies at the counter)

(deftest omega-through-a-reusable-fn-param-is-rejected
  (testing "the paper's Omega combinator must die at the counter"
    (let [m (err-msg '(defn om [] ((fn [^:many f] (f f)) (fn [^:many x] (x x)))))]
      (is (some? m))
      (is (re-find #"cannot be reus" m)))))

(deftest reusable-fn-valued-local-is-rejected
  (testing "a ^:many let bound to an fn value cannot be reused"
    (let [m (err-msg '(defn dup [^:many n] (let [^:many g (fn [x] (inc x))] (+ (g n) (g n)))))]
      (is (some? m))
      (is (re-find #"cannot be reus" m)))))

(deftest reusable-fn-typed-pattern-binder-is-rejected
  (testing "a ^:many field binder over a function-typed field cannot be reused"
    (let [m (book-err '[(writ.defn/data FnBox (FnBox (-> Nat Nat)))
                        (writ.defn/data Boxd (Wrap FnBox))
                        (writ.defn/defn bad [b :- Boxd] :- Nat
                          (writ.defn/match b :- Boxd
                            ((Wrap ^:many f) (+ (f 1) (f 2)))))])]
      (is (some? m))
      (is (re-find #"cannot be reus" m)))))

(deftest an-affine-fn-param-is-still-fine
  (is (ck/check-defn '(defn ok [] ((fn [f] (f 1)) (fn [x] x))))))

(deftest a-reusable-alias-of-a-function-is-rejected
  (testing "a ^:many local aliasing a fn param cannot be applied twice"
    (let [m (err-msg '(defn d [f] (let [^:many g f] (+ (g 1) (g 2)))))]
      (is (some? m))
      (is (re-find #"cannot be reus" m))))
  (testing "the same through a typed fn param, book path"
    (let [m (book-err '[(writ.defn/defn d [g :- (-> Nat Nat)] :- Nat
                         (let [^:many h g] (+ (h 1) (h 2))))])]
      (is (some? m))
      (is (re-find #"cannot be reus" m)))))

(deftest reusable-parametric-fn-field-binder-is-rejected
  (testing "the field type is substituted before the kind gate"
    (let [m (book-err '[(writ.defn/data PBox [a] (PW a))
                        (writ.defn/defn bad [b :- (PBox (-> Nat Nat))] :- Nat
                          (writ.defn/match b :- (PBox (-> Nat Nat))
                            ((PW ^:many f) (+ (f 1) (f 2)))))])]
      (is (some? m))
      (is (re-find #"cannot be reus" m)))))

;; --- G12: an identity alias is not a descent (BendTT 2.5: strict subterm) --

(deftest identity-alias-is-not-a-descent
  (testing "a local bound to the parameter itself is not smaller"
    (let [m (err-msg '(defn f {:writ/descend true} [^:many a] (let [^:many t a] (f t))))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "a chain of identity aliases is not smaller either"
    (let [m (err-msg '(defn f {:writ/descend true} [^:many a] (let [^:many t a ^:many u t] (f u))))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "an unchanged alias in recur position is not a descent"
    (let [m (err-msg '(defn f {:writ/descend true} [^:many a] (loop [^:many y a] (recur y))))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "the paper sees through lets: a leading arg may arrive through an alias"
    (is (ck/check-defn '(defn g {:writ/descend true} [^:many ^Nat x ^:many ^{:writ/type (List Nat)} xs]
                          (if (seq xs) (let [^:many y x] (g y (rest xs))) x)))))
  (testing "a field taken by a pattern still counts as smaller"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/data NatList (Nil) (Cons Nat NatList))
               (writ.defn/defn ^{:writ/descend true} suml [^:many xs :- NatList] :- Nat
                 (writ.defn/match xs :- NatList
                   ((Nil) 0)
                   ((Cons h t) (+ h (suml t)))))])))))

;; --- G13: types are visible only after their declaration; names are unique -

(deftest forward-type-reference-is-rejected
  (testing "a type annotation may not name a datatype declared later"
    (let [m (book-err '[(writ.defn/defn f [x :- (Box Nat)] :- Nat 0)
                        (writ.defn/data Box [a] (Wrap a))])]
      (is (some? m))
      (is (re-find #"not a declared type" m)))))

(deftest duplicate-data-name-is-rejected
  (let [m (book-err '[(writ.defn/data Dup (D0))
                      (writ.defn/data Dup (D1))])]
    (is (some? m))
    (is (re-find #"more than once" m))))

(deftest duplicate-constructor-is-rejected
  (let [m (book-err '[(writ.defn/data A (C0))
                      (writ.defn/data B (C0))])]
    (is (some? m))
    (is (re-find #"declared by two types" m))))

(deftest duplicate-defn-name-is-rejected
  (let [m (book-err '[(writ.defn/defn a [x :- Nat] x)
                      (writ.defn/defn a [y :- Nat] y)])]
    (is (some? m))
    (is (re-find #"more than once" m))))

(deftest def-and-defn-may-not-share-a-name
  (let [m (book-err '[(def a 1)
                      (writ.defn/defn a [x :- Nat] x)])]
    (is (some? m))
    (is (re-find #"more than once" m))))

;; --- G15: a `def` value obeys every rule (a def is a definition too) ------

(deftest def-omega-is-rejected
  (testing "the paper's Omega hidden in a def value"
    (let [m (book-err '[(def om (fn [^:many f] (f f)))])]
      (is (some? m))
      (is (re-find #"cannot be reus" m)))))

(deftest def-affine-violation-is-rejected
  (testing "an affine fn param inside a def value"
    (let [m (book-err '[(def d (fn [x] (+ x x)))])]
      (is (some? m))
      (is (re-find #"more than once" m)))))

(deftest def-named-fn-spin-is-rejected
  (testing "a divergent named fn inside a def value"
    (let [m (book-err '[(def spin (fn g [x] (g x)))])]
      (is (some? m))
      (is (re-find #"does not descend" m)))))

(deftest def-forward-reference-is-rejected
  (testing "a def value may only reference earlier names"
    (let [m (book-err '[(def a (fn [x] (b x)))
                        (def b (fn [x] x))])]
      (is (some? m))
      (is (re-find #"defined later or is not a known name" m)))))

(deftest an-ordinary-fn-def-is-still-fine
  (is (= {:ok true} (wc/check-book '[(def konst (fn [x] 0))]))))

(deftest an-ordinary-non-fn-def-value-is-still-fine
  (is (= {:ok true} (wc/check-book '[(def size (+ 1 2))]))))

(deftest def-value-affine-local-is-rejected
  (testing "a def value's locals carry quantities too"
    (let [m (book-err '[(def bad (let [y (inc 0)] (+ y y)))])]
      (is (some? m))
      (is (re-find #"more than once" m)))))

;; --- G16: a named local fn's self-calls must descend -----------------------

(deftest named-fn-self-call-must-descend
  (testing "a growing self-call inside a local fn"
    (let [m (err-msg '(defn wrap2 [] ((fn g [x] (g (inc x))) 0)))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "an unchanged self-call spins"
    (let [m (err-msg '(defn wrap [] ((fn g [x] (g x)) 0)))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "a destructured field is smaller, and the fn stays affine"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/data NatList (Nil) (Cons Nat NatList))
               (writ.defn/defn run [] :- Nat
                 ((fn g [xs] (writ.defn/match xs :- NatList
                    (Nil 0)
                    ((Cons h t) (g t)))) [:Nil]))])))))

;; --- G17: letfn binders are visible to the rules ---------------------------

(deftest letfn-affine-is-checked
  (testing "an affine param double-used inside a letfn arm"
    (let [m (err-msg '(defn f [x] (letfn [(g [y] (+ x x))] (g 1))))]
      (is (some? m))
      (is (re-find #"more than once" m)))))

(deftest letfn-omega-is-rejected
  (testing "Omega through a letfn binder"
    (let [m (err-msg '(defn f [] (letfn [(g [^:many h] (h h))] (g g))))]
      (is (some? m))
      (is (re-find #"cannot be reus|more than once" m)))))

(deftest an-ordinary-letfn-is-still-fine
  (is (ck/check-defn '(defn f [x] (letfn [(g [y] (inc y))] (g x))))))

(deftest named-fn-descent-uses-its-own-params
  (testing "dec of an outer defn param does not shrink the fn's own binder"
    (let [m (err-msg '(defn f {:writ/descend true} [^:many a]
                        ((fn g [x] (g (dec a))) 0)))]
      (is (some? m))
      (is (re-find #"does not descend" m)))))

(deftest letfn-named-fn-spin-is-rejected
  (testing "a letfn-bound fn's self-call must descend"
    (let [m (err-msg '(defn f [] (letfn [(g [x] (g x))] (g 1))))]
      (is (some? m))
      (is (re-find #"does not descend|more than once" m)))))

;; --- G18: match discipline reaches letfn arms and def-of-fn values ---------

(deftest match-on-a-letfn-spec-param-is-accepted
  (testing "a letfn spec's param is a binder, so it may be matched"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/data MaybeInt (Nothing) (Just Int))
               (writ.defn/defn f [m :- MaybeInt] :- Nat
                 (letfn [(g [v] (writ.defn/match v :- MaybeInt
                                  (Nothing 0)
                                  ((Just x) x)))]
                   (g m)))])))))

(deftest match-discipline-inside-a-def-value-is-checked
  (testing "a good match inside a def of an fn is accepted"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/data MaybeInt (Nothing) (Just Int))
               (def good (fn [m] (writ.defn/match m :- MaybeInt
                                   (Nothing 0)
                                   ((Just x) x))))]))))
  (testing "a non-exhaustive match inside a def of an fn is rejected"
    (let [m (book-err '[(writ.defn/data MaybeInt (Nothing) (Just Int))
                        (def bad (fn [mm] (writ.defn/match mm :- MaybeInt
                                              (Nothing 0))))])]
      (is (some? m))
      (is (re-find #"not exhaustive" m)))))

;; --- G19: multi-arity is rejected cleanly, not mis-checked or crashed -------

(deftest multi-arity-defn-is-rejected
  (testing "a multi-arity plain defn is not silently mis-checked"
    (let [m (err-msg '(defn f ([x] x) ([x y] y)))]
      (is (some? m))
      (is (re-find #"multi-arity" m))))
  (testing "a multi-arity w/defn is a Writ error, not a crash"
    (let [m (book-err '[(writ.defn/defn f ([x :- Nat] x) ([x :- Nat y :- Nat] y))])]
      (is (some? m))
      (is (re-find #"multi-arity" m))))
  (testing "a multi-arity fn value too"
    (let [m (err-msg '(defn h [] ((fn ([a] a) ([a b] b)) 1)))]
      (is (some? m))
      (is (re-find #"multi-arity" m)))))

;; --- G20: try/catch arms join, because only one path runs ------------------

(deftest try-catch-arms-join
  (testing "a use in the body and a use in the catch is one use per path"
    (is (ck/check-defn '(defn f [x] (try (inc x) (catch Throwable e (dec x)))))))
  (testing "finally always runs, so a use there adds"
    (let [m (err-msg '(defn f [x] (try (inc x) (finally (dec x)))))]
      (is (some? m))
      (is (re-find #"more than once" m))))
  (testing "the catch binder carries a quantity"
    (let [m (err-msg '(defn f [] (try 1 (catch Throwable e (+ e e)))))]
      (is (some? m))
      (is (re-find #"more than once" m)))))

;; --- G21: refl reaches case under a let, and the integer builtins ----------

(deftest case-under-a-let-is-convertible
  (testing "subst must walk a case arm"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law case-lit (= (let [x 1] (case x 1 2 3)) 2))
               (writ.defn/proof case-lit-pf case-lit refl)]))))
  (testing "with a default arm"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law cd (= (let [x 9] (case x 1 2 7)) 7))
               (writ.defn/proof cd-pf cd refl)])))))

(deftest integer-builtins-are-literal-folded
  (testing "quot, rem, mod, max and min on literals all fold"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law q7 (= (quot 7 2) 3))
               (writ.defn/proof q7-pf q7 refl)])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law r7 (= (rem 7 2) 1))
               (writ.defn/proof r7-pf r7 refl)])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law m3 (= (mod -7 2) 1))
               (writ.defn/proof m3-pf m3 refl)])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law mx (= (max 1 2) 2))
               (writ.defn/proof mx-pf mx refl)])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law mn (= (min 1 2) 1))
               (writ.defn/proof mn-pf mn refl)])))))

;; --- G14: field quantity = field quantity x scrutinee quantity (BendTT 2.3)

(deftest a-reusable-scrutinee-makes-plain-fields-reusable
  (testing "a + scrutinee hands its plain fields out reusable, unmarked"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/data NatBox (NatBox Nat))
               (writ.defn/data Boxd (Wrap NatBox))
               (writ.defn/defn ok [^:many b :- Boxd] :- Nat
                 (writ.defn/match b :- Boxd
                   ((Wrap v) (+ (writ.defn/match v :- NatBox ((NatBox m) m))
                                (writ.defn/match v :- NatBox ((NatBox m) m))))))]))))
  (testing "an affine scrutinee keeps its fields affine"
    (let [m (book-err '[(writ.defn/data NatBox (NatBox Nat))
                        (writ.defn/data Boxd (Wrap NatBox))
                        (writ.defn/defn bad [b :- Boxd] :- Nat
                          (writ.defn/match b :- Boxd
                            ((Wrap v) (+ (writ.defn/match v :- NatBox ((NatBox m) m))
                                         (writ.defn/match v :- NatBox ((NatBox m) m))))))])]
      (is (some? m))
      (is (re-find #"more than once" m)))))

;; --- G22: collection literals are expressions, not opaque literals ----------

(deftest collection-literals-carry-uses
  (testing "a vector literal is walked: a double use inside is seen"
    (let [m (err-msg '(defn dup [x] [x x]))]
      (is (some? m))
      (is (re-find #"more than once" m))))
  (testing "map and set literals are walked too"
    (let [m (err-msg '(defn dup [x] {x x}))]
      (is (some? m))
      (is (re-find #"more than once" m)))
    (let [m (err-msg '(defn dup [x] #{(inc x) (dec x)}))]
      (is (some? m))
      (is (re-find #"more than once" m))))
  (testing "a single use inside a collection is fine"
    (is (= {:ok true} (ck/check-defn '(defn one [x] [x])))))
  (testing "ordering sees invocations inside a collection literal"
    (let [m (book-err '[(writ.defn/defn a [] :- (List Nat) [(later)])
                        (writ.defn/defn later [] :- Nat 0)])]
      (is (some? m))
      (is (re-find #"defined later or is not a known name" m)))))

;; --- G23: sibling binders with the same name are separate scopes ------------

(deftest sibling-binders-do-not-collide
  (testing "two sibling fns may reuse a parameter name"
    (is (= {:ok true}
           (ck/check-defn '(defn f [x y]
                             (let [g (fn [t] t) h (fn [t] (inc t))]
                               (+ (g x) (h y))))))))
  (testing "sequential lets may reuse a name"
    (is (= {:ok true}
           (ck/check-defn '(defn f [] (+ (let [t 1] t) (let [t 2] t)))))))
  (testing "each binder still answers for its own uses"
    (let [m (err-msg '(defn f [] (let [g (fn [t] (+ t t))] (g 1))))]
      (is (some? m))
      (is (re-find #"more than once" m)))))

;; --- G24: :as in map destructuring is a binder; & is not --------------------

(deftest destructure-binders-are-complete
  (testing "the :as alias carries a quantity"
    (let [m (err-msg '(defn f [m] (let [{:keys [a] :as all} m]
                                    (+ (count all) (count all)))))]
      (is (some? m))
      (is (re-find #"more than once" m))))
  (testing "the rest binder after & is an ordinary binder"
    (is (= {:ok true}
           (ck/check-defn '(defn f [v] (let [[a & r] v] (+ a (count r)))))))))

;; --- G25: case groups and unevaluated test constants ------------------------

(deftest case-groups-and-quoted-tests-are-faithful
  (testing "a group test matches any of its constants"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law g1 (= (case 1 (1 2) :hit :miss) :hit))
               (writ.defn/proof g1-pf g1 refl)])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law g2 (= (case 2 (1 2) :hit :miss) :hit))
               (writ.defn/proof g2-pf g2 refl)])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law g3 (= (case 3 (1 2) :hit :miss) :miss))
               (writ.defn/proof g3-pf g3 refl)]))))
  (testing "an unevaluated quoted test is a group of its own members, as in Clojure"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law g4 (= (case 'a 'a 1 2) 1))
               (writ.defn/proof g4-pf g4 refl)])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/law g5 (= (case 'quote 'a 1 2) 1))
               (writ.defn/proof g5-pf g5 refl)])))))

;; --- G27: only one case branch runs, so branch uses join ---------------------

(deftest case-branches-join-not-add
  (testing "a use in each of two branches is one use per path"
    (is (= {:ok true}
           (ck/check-defn '(defn f [x] (case 1 1 (inc x) 2 (dec x))))))))

;; --- G28: a defn body is an implicit loop, so its recur must descend ---------
;;
;; Like loop/recur, a defn-level recur rebinds the params each iteration, so
;; a param that both feeds the test and rides into the recur carries ^:many.

(deftest defn-level-recur-descends
  (testing "an unmarked defn-level recur is rejected like loop/recur"
    (let [m (err-msg '(defn f [^:many x] (if (zero? x) 0 (recur (dec x)))))]
      (is (some? m))
      (is (re-find #"mark it" m))))
  (testing "a marked defn-level recur must pass a smaller argument"
    (let [m (err-msg '(defn f {:writ/descend true} [^:many x] (recur x)))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "a descending defn-level recur is accepted"
    (is (= {:ok true}
           (ck/check-defn '(defn f {:writ/descend true} [^:many ^Nat x]
                             (if (zero? x) 0 (recur (dec x)))))))))

;; --- G26: recur must be in tail position -------------------------------------

(deftest recur-must-be-in-tail-position
  (testing "a recur as an argument or statement is rejected, as in Clojure"
    (let [m (err-msg '(defn f {:writ/descend true} [a]
                        (loop [x a] (do (recur (dec x)) 0))))]
      (is (some? m))
      (is (re-find #"tail" m)))
    (let [m (err-msg '(defn f {:writ/descend true} [a]
                        (loop [x a] (inc (recur (dec x))))))]
      (is (some? m))
      (is (re-find #"tail" m))))
  (testing "a tail recur still checks descent"
    (let [m (err-msg '(defn f {:writ/descend true} [a]
                        (loop [x a] (recur x))))]
      (is (some? m))
      (is (re-find #"does not descend" m)))))

;; --- G29: the ordering rule covers value references, not just calls ---------

(deftest value-references-respect-book-order
  (testing "a forward VALUE reference is rejected like a forward call"
    (let [m (book-err '[(writ.defn/defn f [] :- Nat x)
                        (def x 1)])]
      (is (some? m))
      (is (re-find #"defined later or is not a known name" m))))
  (testing "an earlier def in value position is fine"
    (is (= {:ok true}
           (wc/check-book '[(def x 1)
                            (writ.defn/defn f [] :- Nat x)])))))

;; --- G30: def-like top-level forms are rejected, not silently skipped --------

(deftest def-like-forms-are-rejected
  (doseq [form ['(declare later)
                '(defonce x 1)
                '(defmulti mm :val)
                '(defprotocol P (pm [x]))
                '(defrecord R [a])
                '(deftype T [a])]]
    (testing (str form)
      (let [m (book-err [form])]
        (is (some? m))
        (is (re-find #"not supported in a book" m))))))

;; --- G31: compiler gensyms from if-let/when-let are not the programmer's -----

(deftest if-let-gensyms-are-exempt
  (testing "if-let with destructuring does not falsely reject"
    (is (= {:ok true}
           (ck/check-defn '(defn f [m] (if-let [{:keys [a]} m] a 0)))))
    (is (= {:ok true}
           (ck/check-defn '(defn f [m] (when-let [{:keys [a]} m] a)))))))

;; --- G32: seq is a size-preserving coercion, so seq-loops can descend -------

(deftest seq-loops-descend-through-next
  (testing "loop over (seq xs) with (next s) is accepted"
    (is (= {:ok true}
           (ck/check-defn '(defn f {:writ/descend true} [^{:writ/type (List Nat)} xs]
                             (loop [^:many s (seq xs)]
                               (when s (recur (next s)))))))))
  (testing "but recur on (seq s) alone is a spin and stays rejected"
    (let [m (err-msg '(defn f {:writ/descend true} [xs]
                       (loop [^:many s (seq xs)]
                         (when s (recur (seq s))))))]
      (is (some? m))
      (is (re-find #"does not descend" m)))))

;; --- G33: var reads as a name; set! says what it is --------------------------

(deftest var-and-set-messages
  (testing "(var x) is a value reference and obeys ordering"
    (let [m (try (wc/check-book
                   '[(writ.defn/defn f [] :- Nat (var x))
                     (def x 1)])
                 (catch Throwable t (.getMessage t)))]
      (is (some? m))
      (is (re-find #"defined later or is not a known name" m))))
  (testing "set! is named for what it is"
    (let [m (try (wc/check-book
                   '[(def ^:dynamic *x* 1)
                     (defn f [] (set! *x* 3))])
                 (catch Throwable t (.getMessage t)))]
      (is (some? m))
      (is (re-find #"mutates a var" m)))))

;; --- G34: a recursion over nothing cannot descend ----------------------------

(deftest zero-binder-recur-is-a-spin
  (testing "a marked zero-binder loop is rejected: nothing can shrink"
    (let [m (err-msg '(defn f {:writ/descend true} [] (loop [] (recur))))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "while lowers to a zero-binder loop, so it is rejected too"
    (let [m (err-msg '(defn f {:writ/descend true} [x] (while (< x 10) 1)))]
      (is (some? m))
      (is (re-find #"does not descend" m))))
  (testing "a self-spinning zero-arg fn likewise"
    (let [m (err-msg '(defn f {:writ/descend true} [] ((fn [] (recur)))))]
      (is (some? m))
      (is (re-find #"does not descend" m)))))

;; --- G35: recur rebinds exactly its frame's slots ----------------------------

(deftest recur-arity-must-match-its-frame
  (testing "fewer args than the loop rebinds"
    (let [m (err-msg '(defn f {:writ/descend true} [a b] (loop [x a y b] (recur (dec x)))))]
      (is (some? m))
      (is (re-find #"rebinds 2 value" m))))
  (testing "more args than the loop rebinds"
    (let [m (err-msg '(defn f {:writ/descend true} [a] (loop [x a] (recur (dec x) 2))))]
      (is (some? m))
      (is (re-find #"rebinds 1 value" m))))
  (testing "a defn-level recur rebinds the parameters"
    (let [m (err-msg '(defn f {:writ/descend true} [x] (recur)))]
      (is (some? m))
      (is (re-find #"rebinds 1 value" m)))))

;; --- G36: host interop and effect forms say what they are --------------------

(deftest host-and-effect-forms-are-named
  (testing "throw"
    (let [m (book-err '[(writ.defn/defn g [] :- Any (throw (ex-info "x" {})))])]
      (is (some? m))
      (is (re-find #"host interop or effect" m))))
  (testing "new"
    (let [m (book-err '[(writ.defn/defn g [] :- Any (new String "x"))])]
      (is (some? m))
      (is (re-find #"host interop or effect" m))))
  (testing "instance interop"
    (let [m (book-err '[(writ.defn/defn g [x :- Any] :- Any (.foo x))])]
      (is (some? m))
      (is (re-find #"host interop or effect" m)))))

;; --- G37: duplicate case test constants (a compile error in Clojure; a book
;; is never compiled, so writ owns the contract) -------------------------------

(deftest duplicate-case-constants-are-rejected
  (testing "the same constant twice"
    (let [m (err-msg '(defn f [x] (case x 1 :a 1 :b)))]
      (is (some? m))
      (is (re-find #"duplicate case test constant" m))))
  (testing "a constant overlapping a group"
    (let [m (err-msg '(defn f [x] (case x (1 2) :a 2 :b)))]
      (is (some? m))
      (is (re-find #"duplicate case test constant" m))))
  (testing "a duplicate inside one group"
    (let [m (err-msg '(defn f [x] (case x (1 1) :a)))]
      (is (some? m))
      (is (re-find #"duplicate case test constant" m))))
  (testing "distinct constants still pass"
    (is (nil? (err-msg '(defn f [x] (case x 1 :a 2 :b :c)))))))

;; --- G38: a definition inside a body (Clojure allows it at runtime; a book
;; is never evaluated, so the name would escape every rule) --------------------

(deftest nested-definitions-are-rejected
  (testing "def inside a body"
    (let [m (err-msg '(defn f [] (do (def x 1) x)))]
      (is (some? m))
      (is (re-find #"inside a body" m))))
  (testing "defn inside a body"
    (let [m (err-msg '(defn f [] (do (defn g [] 1) (g))))]
      (is (some? m))
      (is (re-find #"inside a body" m)))))

;; --- G39: the direct `.` interop form (round 8 named `.foo` heads; the bare
;; dot form must not slip through the standalone path) --------------------------

(deftest direct-dot-form-is-rejected
  (let [m (err-msg '(defn f [x] (. x foo)))]
    (is (some? m))
    (is (re-find #"host interop or effect" m))))

;; --- G40: unknown top-level forms are rejected, not silently skipped ---------

(deftest unknown-top-level-forms-are-rejected
  (testing "a bare require is not a book form"
    (let [m (book-err '[(ns book)
                        (require (quote other))
                        (writ.defn/defn f [] :- Nat 1)])]
      (is (some? m))
      (is (re-find #"not supported in a book" m))))
  (testing "an ns header is fine"
    (is (= {:ok true}
           (wc/check-book
             '[(ns book)
               (writ.defn/defn f [] :- Nat 1)]))))
  (testing "comment is fine"
    (is (= {:ok true}
           (wc/check-book
             '[(comment (scratch))
               (writ.defn/defn f [] :- Nat 1)])))))

;; --- G41: duplicate parameters (locals get a duplicate-binder check; params
;; are binders too, and uniquify hides dup fn params downstream) ---------------

(deftest duplicate-parameters-are-rejected
  (testing "duplicate defn params"
    (let [m (err-msg '(defn f [x x] x))]
      (is (some? m))
      (is (re-find #"duplicate parameter" m))))
  (testing "duplicate nested fn params"
    (let [m (err-msg '(defn f [] ((fn [y y] y) 1 2)))]
      (is (some? m))
      (is (re-find #"duplicate parameter" m))))
  (testing "distinct params still pass"
    (is (nil? (err-msg '(defn f [x y] x))))))

;; --- G42: a valueless def smuggles an unbound name into the known set ---------

(deftest valueless-def-is-rejected
  (testing "bare def"
    (let [m (book-err '[(def x)
                        (writ.defn/defn f [] :- Nat (inc x))])]
      (is (some? m))
      (is (re-find #"must carry a value" m))))
  (testing "an explicit nil value is a real def"
    (is (= {:ok true}
           (wc/check-book
             '[(def x nil)
               (writ.defn/defn f [] :- Nat 1)])))))

;; --- G43: case tests must be compile-time constants (Clojure rejects bare
;; symbols at compile time; a book is never compiled, so writ owns it) ---------

(deftest bare-symbol-case-tests-are-rejected
  (testing "a bare symbol test"
    (let [m (err-msg '(defn f [x] (case x foo :a)))]
      (is (some? m))
      (is (re-find #"compile-time constant" m))))
  (testing "a bare symbol inside a group"
    (let [m (err-msg '(defn f [x] (case x (a b) :c)))]
      (is (some? m))
      (is (re-find #"compile-time constant" m))))
  (testing "quoted symbols, groups and literals still pass"
    (is (nil? (err-msg '(defn f [x] (case x (quote foo) :a 2 :b)))))
    (is (nil? (err-msg '(defn f [x] (case x (1 2) :a :b)))))))

;; --- G44: data type/constructor names collide with book defs unchecked -------

(deftest data-names-collide-with-defs
  (testing "a defn reusing a constructor name"
    (let [m (book-err '[(w/data MaybeInt Nothing (Just Int))
                        (writ.defn/defn Just [v :- Int] :- Int v)])]
      (is (some? m))
      (is (re-find #"declared more than once" m))))
  (testing "a defn reusing a type name"
    (let [m (book-err '[(w/data MaybeInt Nothing (Just Int))
                        (writ.defn/defn MaybeInt [] :- Int 1)])]
      (is (some? m))
      (is (re-find #"declared more than once" m))))
  (testing "a def reusing a constructor name"
    (let [m (book-err '[(w/data MaybeInt Nothing (Just Int))
                        (def Nothing 1)])]
      (is (some? m))
      (is (re-find #"declared more than once" m))))
  (testing "distinct data and defn names still pass"
    (is (= {:ok true}
           (wc/check-book
             '[(w/data MaybeInt Nothing (Just Int))
               (writ.defn/defn f [] :- Int 1)])))))

;; --- G45: a book is one namespace, so book-level names shadow clojure.core ----

(deftest book-names-shadow-core
  (testing "forward reference to a later defn named like a core fn"
    (let [m (book-err '[(writ.defn/defn f [] :- Nat (map inc [1 2]))
                        (writ.defn/defn map [g xs] :- Nat 0)])]
      (is (some? m))
      (is (re-find #"defined later" m))))
  (testing "forward reference to a later def named like a core fn"
    (let [m (book-err '[(writ.defn/defn f [] :- Nat (inc 1))
                        (def inc 1)])]
      (is (some? m))
      (is (re-find #"defined later" m))))
  (testing "declared earlier, the book's own name is used"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/defn map [g xs] :- Nat 0)
               (writ.defn/defn f [] :- Nat (map inc [1 2]))]))))
  (testing "a core fn the book never shadows still resolves to core"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/defn f [] :- Nat (inc 1))])))))

;; --- G46: recur cannot cross a try (Clojure: "Cannot recur across try") ------

(deftest recur-cannot-cross-try
  (testing "a loop outside the try"
    (let [m (err-msg '(defn f {:writ/descend true} [x]
                       (loop [y x] (try (recur (dec y)) (catch Throwable e e)))))]
      (is (some? m))
      (is (re-find #"cannot cross" m))))
  (testing "a defn-level recur inside a try"
    (let [m (err-msg '(defn f {:writ/descend true} [x]
                       (try (recur (dec x)) (catch Throwable t t))))]
      (is (some? m))
      (is (re-find #"cannot cross" m))))
  (testing "a loop inside the try recurs fine"
    (is (nil? (err-msg '(defn f {:writ/descend true} [^Nat x]
                         (try (loop [^:many y x] (if (zero? y) 0 (recur (dec y))))
                              (catch Throwable t t))))))))

;; --- G47: malformed rest parameters -------------------------------------------

(deftest malformed-rest-params-are-rejected
  (testing "a bare & with no rest name (defn)"
    (let [m (err-msg '(defn f [x &] x))]
      (is (some? m))
      (is (re-find #"rest parameter" m))))
  (testing "a bare & with no rest name (fn)"
    (let [m (err-msg '(defn f [] ((fn [x &] x) 1)))]
      (is (some? m))
      (is (re-find #"rest parameter" m))))
  (testing "two params after &"
    (let [m (err-msg '(defn f [& a b] a))]
      (is (some? m))
      (is (re-find #"rest parameter" m))))
  (testing "a well-formed variadic defn still passes"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/defn f [x & xs] :- Nat (count xs))])))))

;; --- case arms join per path (pinning the rule; the scrutinee use adds) ------

(deftest case-arms-join-per-path
  (testing "one use per arm is one use per path"
    (is (nil? (err-msg '(defn f [x] (case 1 1 x 2 x))))))
  (testing "twice in one arm is still twice"
    (let [m (err-msg '(defn f [x] (case 1 1 (+ x x) 2 0)))]
      (is (some? m))
      (is (re-find #"more than once" m)))))

;; --- G49: call arity for book fns (host: runtime ArityException; t.c.:
;; static "wrong number of args"; a book is never evaluated) ------------------

(deftest book-fn-call-arity-is-checked
  (testing "too few arguments"
    (let [m (book-err '[(writ.defn/defn f [x y] :- Nat 0)
                        (writ.defn/defn g [] :- Nat (f 1))])]
      (is (some? m))
      (is (re-find #"takes 2 argument" m))))
  (testing "too many arguments"
    (let [m (book-err '[(writ.defn/defn f [x] :- Nat 0)
                        (writ.defn/defn g [] :- Nat (f 1 2))])]
      (is (some? m))
      (is (re-find #"takes 1 argument" m))))
  (testing "a variadic fn's minimum"
    (let [m (book-err '[(writ.defn/defn f [x & xs] :- Nat 0)
                        (writ.defn/defn g [] :- Nat (f))])]
      (is (some? m))
      (is (re-find #"takes at least 1 argument" m))))
  (testing "a def of a fn carries its arity"
    (let [m (book-err '[(def f (fn [x] x))
                        (writ.defn/defn g [] :- Nat (f 1 2))])]
      (is (some? m))
      (is (re-find #"takes 1 argument" m))))
  (testing "exact and variadic calls still pass"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/defn f [x y] :- Nat 0)
               (writ.defn/defn h [] :- Nat (f 1 2))])))
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/defn f [x & xs] :- Nat (count xs))
               (writ.defn/defn h [] :- Nat (f 1 2 3))])))))

;; --- G50: constructors exist only in patterns (round 33 decision) ---------
;;
;; w/data declares a type for the checker only: it defines no constructor
;; fns, so (Just 1) fails at runtime.  A book builds no data values; it
;; takes apart data built elsewhere, so a constructor outside a pattern is
;; rejected (this replaces the round-12 arity check on ctor calls).

(deftest ctor-calls-are-rejected
  (doseq [body ['(Just 1 2) '(Nothing 1) '(Just 1) 'Nothing '[Nothing]]]
    (is (re-find #"constructor.*only in a `match` pattern"
                 (book-err [(list 'w/data 'MaybeInt 'Nothing '(Just Int))
                            (list 'writ.defn/defn 'g [] body)])))))

;; --- G51: defn's attr-map position is honored, not silently dropped ---------

(deftest attr-map-position-is-honored
  (testing "the attr-map spelling of the descend marker"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/defn f {:writ/descend true} [^:many x :- Nat] :- Nat
                (if (zero? x) 0 (f (dec x))))]))))
  (testing "the name-meta spelling still works"
    (is (= {:ok true}
           (wc/check-book
             '[(writ.defn/defn ^{:writ/descend true} f [^:many x :- Nat] :- Nat
                (if (zero? x) 0 (f (dec x))))])))))

;; --- G52: a keyword or set call needs its collection (both hosts throw on a
;; zero-argument lookup; writ owns the contract because a book never runs) ----

(deftest keyword-and-set-calls-need-arguments
  (testing "a keyword called with no arguments"
    (let [m (err-msg '(defn f [] (:k)))]
      (is (some? m))
      (is (re-find #"called with no arguments" m))))
  (testing "a set called with no arguments"
    (let [m (err-msg '(defn f [] (#{1})))]
      (is (some? m))
      (is (re-find #"called with no arguments" m))))
  (testing "one- and two-argument keyword calls still pass"
    (is (nil? (err-msg '(defn f [] (:k {:k 1})))))
    (is (nil? (err-msg '(defn f [m] (:k m 0)))))
    (is (nil? (err-msg '(defn f [] (#{1} 1)))))))

;; --- G53: mutual recursion through local fns (Bend: defs reference earlier
;; names only, so a cycle has no checkable descent) ----------------------------

(deftest local-fn-cycles-are-rejected
  (testing "the defn recursing through a local helper"
    (let [m (err-msg '(defn f {:writ/descend true} [^:many x]
                       (letfn [(g [y] (f (dec x)))] (g x))))]
      (is (some? m))
      (is (re-find #"mutually recursive" m))))
  (testing "a dead letfn cycle"
    (let [m (err-msg '(defn f [] (letfn [(a [q] (b q)) (b [q] (a q))] 1)))]
      (is (some? m))
      (is (re-find #"mutually recursive" m))))
  (testing "a helper with no back edge still passes"
    (is (nil? (err-msg '(defn f [^:many ^Nat x] (letfn [(g [y] (dec y))] (g x)))))))
  (testing "a letfn forward reference is not a cycle"
    (is (nil? (err-msg '(defn f [x] (letfn [(g [y] (h y)) (h [y] y)] (g x)))))))
  (testing "a descending letfn self-recursion is not a cycle"
    (is (nil? (err-msg '(defn f [^Nat x]
                          (letfn [(g [^:many ^Nat y] (if (zero? y) 0 (g (dec y))))] (g x))))))))

;; ---------------------------------------------------------------------------
;; G54: try/catch/finally clause shapes. Clojure rejects these at compile
;; time ("Unable to parse catch clause", "finally clause must be last"); a
;; book is never compiled, so writ owns the shapes.
;; ---------------------------------------------------------------------------

(deftest try-clause-shapes-are-validated
  (testing "a catch clause needs a class, a binder and a body"
    (is (re-find #"a catch clause must be"
                 (err-msg '(defn f [] (try 1 (catch))))))
    (is (re-find #"a catch clause must be"
                 (err-msg '(defn f [] (try 1 (catch Throwable)))))))
  (testing "the catch binder must be a simple symbol"
    (is (re-find #"a catch clause must be"
                 (err-msg '(defn f [] (try 1 (catch Throwable [x] x)))))))
  (testing "the catch class must be a symbol"
    (is (re-find #"a catch clause must be"
                 (err-msg '(defn f [] (try 1 (catch 5 e e)))))))
  (testing "finally must be the last clause"
    (is (re-find #"finally. clause must be last"
                 (err-msg '(defn f [] (try 1 (finally 2) (catch Throwable t 3)))))))
  (testing "a body form cannot follow a catch clause"
    (is (re-find #"can follow a catch"
                 (err-msg '(defn f [] (try 1 (catch Throwable t 3) 2))))))
  (testing "well-formed try/catch/finally still passes"
    (is (nil? (err-msg '(defn f [] (try 1 (catch Throwable t t) (finally 2))))))
    (is (nil? (err-msg '(defn f [] (try 1 (catch Throwable t))))))
    (is (nil? (err-msg '(defn f [] (try 1 (finally 2))))))))

;; ---------------------------------------------------------------------------
;; G55: letfn spec shapes. A bare symbol as the spec list or a spec without
;; a params vector used to crash with a raw host IllegalArgumentException
;; or the misleading "multi-arity fn" message.
;; ---------------------------------------------------------------------------

(deftest letfn-spec-shapes-are-validated
  (testing "the specs must be a vector"
    (is (re-find #"requires a vector of fn specs"
                 (err-msg '(defn f [] (letfn f 1))))))
  (testing "a non-seq spec is rejected"
    (is (re-find #"a .letfn. spec must be"
                 (err-msg '(defn f [] (letfn [f] 1))))))
  (testing "a spec needs a params vector"
    (is (re-find #"a .letfn. spec must be"
                 (err-msg '(defn f [] (letfn [(f)] 1))))))
  (testing "a well-formed letfn still passes"
    (is (nil? (err-msg '(defn f [x] (letfn [(g [y] (dec y))] (g x))))))))

;; ---------------------------------------------------------------------------
;; G57: if arity. t.c. parse-if rejects any count but 3 or 4 ("Wrong number
;; of args to if, had: N"); writ used to leak a raw index error on too few
;; and silently DROP the extra branch on too many.
;; ---------------------------------------------------------------------------

(deftest if-arity-is-checked
  (testing "too few args to if"
    (is (re-find #"Wrong number of args to if, had: 0"
                 (err-msg '(defn f [] (if)))))
    (is (re-find #"Wrong number of args to if, had: 1"
                 (err-msg '(defn f [] (if 1))))))
  (testing "a fourth branch is not silently dropped"
    (is (re-find #"Wrong number of args to if, had: 4"
                 (err-msg '(defn f [x] (if x 1 2 3))))))
  (testing "two- and three-branch if still pass"
    (is (nil? (err-msg '(defn f [x] (if x 1 2)))))))

;; ---------------------------------------------------------------------------
;; G58: var shape. t.c. parse-var requires exactly one symbol argument.
;; ---------------------------------------------------------------------------

(deftest var-shape-is-checked
  (testing "var with no argument"
    (is (re-find #"Wrong number of args to var, had: 0"
                 (err-msg '(defn f [] (var))))))
  (testing "var with two arguments"
    (is (re-find #"Wrong number of args to var, had: 2"
                 (err-msg '(defn f [] (var a b))))))
  (testing "var of a non-symbol"
    (is (re-find #"argument to .var. must be a symbol"
                 (err-msg '(defn f [] (var 5)))))))

;; ---------------------------------------------------------------------------
;; G59: binding symbols must be simple (t.c. valid-binding-symbol?: no
;; namespace, no dots) -- a JVM compiler contract writ's lax host skips.
;; ---------------------------------------------------------------------------

(deftest binders-must-be-simple-symbols
  (testing "qualified params"
    (is (re-find #"Bad binding form"
                 (err-msg '(defn f [foo/bar] 1)))))
  (testing "dotted params"
    (is (re-find #"Bad binding form"
                 (err-msg '(defn f [a.b] 1)))))
  (testing "qualified and dotted let binders"
    (is (re-find #"Bad binding form"
                 (err-msg '(defn f [] (let [foo/x 1] foo/x)))))
    (is (re-find #"Bad binding form"
                 (err-msg '(defn f [] (let [a.b 1] a.b))))))
  (testing "a qualified catch binder"
    (is (re-find #"Bad binding form"
                 (err-msg '(defn f [] (try 1 (catch Throwable foo/bar 1)))))))
  (testing "a qualified letfn name"
    (is (re-find #"Bad binding form"
                 (err-msg '(defn f [] (letfn [(foo/bar [x] x)] 1))))))
  (testing "simple binders still pass"
    (is (nil? (err-msg '(defn f [x] (let [y (inc x)] y)))))))

;; ---------------------------------------------------------------------------
;; G60: def tail shapes (t.c. parse-def). The docstring position used to
;; shadow the real value: (def x "doc" (omega-fn)) bypassed every check.
;; ---------------------------------------------------------------------------

(deftest def-tail-shapes-are-checked
  (testing "a non-symbol def name"
    (is (re-find #"First argument to def must be a symbol"
                 (book-err '[(def 5 1)]))))
  (testing "a qualified def name"
    (is (re-find #"Cannot def namespace qualified symbol"
                 (book-err '[(def foo/bar 1)]))))
  (testing "the value behind a docstring is checked"
    (is (re-find #"cannot be reusable"
                 (book-err '[(def x "doc" (fn [^:many y] (y y)))]))))
  (testing "extra forms after the value"
    (is (re-find #"Too many arguments to def"
                 (book-err '[(def x 1 2)]))))
  (testing "docstring defs still pass"
    (is (nil? (book-err '[(def x "doc")])))
    (is (nil? (book-err '[(def x "doc" (fn [y] (dec y)))])))))

;; ---------------------------------------------------------------------------
;; G61: a params declaration must be a vector (host: "Parameter declaration
;; should be a vector"). (defn f x 1) and (fn (x) x) used to report the
;; misleading "multi-arity" message.
;; ---------------------------------------------------------------------------

(deftest params-declaration-must-be-a-vector
  (testing "a defn whose params are a bare symbol"
    (is (re-find #"requires a vector of parameters"
                 (err-msg '(defn f x 1)))))
  (testing "an fn whose params are a list"
    (is (re-find #"requires a vector of parameters"
                 (err-msg '(defn f [] ((fn (x) x) 1))))))
  (testing "true multi-arity keeps its own message"
    (is (re-find #"multi-arity"
                 (err-msg '(defn f ([x] x) ([x y] y)))))))

;; ---------------------------------------------------------------------------
;; G62: local fn call arity. The host throws Wrong number of args (N) for
;; calls to letfn fns, let-bound fns and anonymous fns; R12's gate exempted
;; locals, so writ accepted them silently.
;; ---------------------------------------------------------------------------

(deftest local-fn-call-arity-is-checked
  (testing "a letfn fn called below arity"
    (is (re-find #"`g` takes 2 argument\(s\) but is passed 1"
                 (err-msg '(defn f [x] (letfn [(g [a b] a)] (g x)))))))
  (testing "a variadic letfn called under its minimum"
    (is (re-find #"`g` takes at least 1 argument\(s\) but is passed 0"
                 (err-msg '(defn f [x] (letfn [(g [a & bs] a)] (g)))))))
  (testing "a let-bound fn called below arity"
    (is (re-find #"`g` takes 2 argument\(s\) but is passed 1"
                 (err-msg '(defn f [x] (let [g (fn [a b] a)] (g x)))))))
  (testing "an anonymous fn called directly below arity"
    (is (re-find #"an anonymous fn takes 2 argument\(s\) but is passed 1"
                 (err-msg '(defn f [x] ((fn [a b] a) x)))))
    (is (re-find #"an anonymous fn takes at least 1 argument\(s\) but is passed 0"
                 (err-msg '(defn f [x] ((fn [a & bs] a)))))))
  (testing "a call inside another local fn's body"
    (is (re-find #"`g` takes 1 argument\(s\) but is passed 2"
                 (err-msg '(defn f [x y]
                             (letfn [(g [a] a)
                                     (h [b c] (g b c))]
                               (h x y)))))))
  (testing "correct calls still pass"
    (is (nil? (err-msg '(defn f [x y] (letfn [(g [a b] a)] (g x y))))))
    (is (nil? (err-msg '(defn f [x] (letfn [(g [a & bs] a)] (g x))))))
    (is (nil? (err-msg '(defn f [x] (let [g (fn [a b] a)] (g 1 2)))))))
  (testing "unknown arities stay exempt"
    (is (nil? (err-msg '(defn f [g] (g 1 2 3)))))
    (is (nil? (err-msg '(defn f [x] (letfn [(g [a b] a)]
                                       ((fn [g] (g x)) g))))))
    (is (nil? (err-msg '(defn f [xs] (letfn [(g [a b] a)] (count (map g xs)))))))))

;; ---------------------------------------------------------------------------
;; G63: case shapes. (case) is a macro-arity error on the host; (case x)
;; has no clause and no default, so it can only ever throw No matching
;; clause at runtime.
;; ---------------------------------------------------------------------------

(deftest case-shapes-are-validated
  (testing "a case with no scrutinee"
    (is (re-find #"Wrong number of args to case, had: 0"
                 (err-msg '(defn f [] (case))))))
  (testing "a case with no clause and no default"
    (is (re-find #"requires at least one clause or a default"
                 (err-msg '(defn f [x] (case x))))))
  (testing "a default-only case and a clause case still pass"
    (is (nil? (err-msg '(defn f [x] (case x :d)))))
    (is (nil? (err-msg '(defn f [x] (case x 1 :one :other)))))))

;; ---------------------------------------------------------------------------
;; G64: let/loop bindings must be a vector (t.c. validate-bindings:
;; "let requires a vector for its bindings, had: ..."); writ used to leak
;; the raw host "count not supported on this type" crash.
;; ---------------------------------------------------------------------------

(deftest let-bindings-require-a-vector
  (testing "a non-vector let binding form"
    (is (re-find #"`let` requires a vector for its bindings"
                 (err-msg '(defn f [] (let 5 1))))))
  (testing "a non-vector loop binding form"
    (is (re-find #"`loop` requires a vector for its bindings"
                 (err-msg '(defn f [] (loop 5 (recur)))))))
  (testing "vector bindings still pass"
    (is (nil? (err-msg '(defn f [x] (let [y (inc x)] y)))))
    (is (nil? (err-msg '(defn f [x] (loop [y x] (dec y))))))))

;; ---------------------------------------------------------------------------
;; G65: core fn call arity. The host throws Wrong number of args (N) for
;; calls like (deref), (get m), (map); a book is never evaluated, so writ
;; owns the contract. Ported from typedclojure's stance (core fn arity
;; comes from the host's own declarations): the table is derived from
;; (ns-publics 'clojure.core) :arglists at load time, not hand-rolled.
;; ---------------------------------------------------------------------------

(deftest core-fn-call-arity-is-checked
  (testing "under-arity calls to fixed-arity core fns"
    (is (re-find #"`get` takes between 2 and 3 argument\(s\) but is passed 1"
                 (err-msg '(defn f [m] (get m)))))
    (is (re-find #"`map` takes at least 1 argument\(s\) but is passed 0"
                 (err-msg '(defn f [] (map))))))
  (testing "over-arity calls"
    (is (re-find #"`inc` takes 1 argument\(s\) but is passed 2"
                 (err-msg '(defn f [] (inc 1 2)))))
    (is (re-find #"`deref` takes between 1 and 3 argument\(s\) but is passed 4"
                 (err-msg '(defn f [] (deref 1 2 3 4))))))
  (testing "zero-arg call to a 1-arg core fn"
    (is (re-find #"`deref` takes between 1 and 3 argument\(s\) but is passed 0"
                 (err-msg '(defn f [a] (deref))))))
  (testing "correct calls still pass"
    (is (nil? (err-msg '(defn f [m k] (get m k)))))
    (is (nil? (err-msg '(defn f [a] (deref a)))))
    (is (nil? (err-msg '(defn f [a] (deref a 10 :d)))))
    (is (nil? (err-msg '(defn f [] (+)))))
    (is (nil? (err-msg '(defn f [] (map inc [1 2]))))))
  (testing "a book fn shadows a core name with its own arity"
    (is (re-find #"`deref` takes 2 argument\(s\) but is passed 1"
                 (book-err '[(defn deref [a b] a)
                              (defn g [] (deref 1))])))
    (is (nil? (book-err '[(defn deref [a b] a)
                          (defn g [] (deref 1 2))])))))

;; ---------------------------------------------------------------------------
;; G66: defn names. The host rejects (defn 5 ...) at expansion and a
;; qualified name can never be referenced inside a book (round 15's parse-def
;; port rejects (def foo/bar 1) already; defn must match).  Pinned non-gaps:
;; (defn f) / (defn f "doc") already reject via the R15 params-vector gate,
;; trailing docstrings/attr-maps after the body are legal on the host, and
;; duplicate constant keys in map/set literals are unreachable in writ --
;; jolt's reader throws "Duplicate key:" before writ ever sees the form.
;; ---------------------------------------------------------------------------

(deftest defn-names-are-validated
  (testing "a non-symbol defn name"
    (is (re-find #"First argument to defn must be a symbol"
                 (book-err '[(defn 5 [x] x)]))))
  (testing "a qualified defn name"
    (is (re-find #"namespace qualified"
                 (book-err '[(defn foo/bar [x] x)]))))
  (testing "a simple defn name still passes"
    (is (nil? (book-err '[(defn f [x] x) (defn g [] (f 1))])))))

;; ---------------------------------------------------------------------------
;; G67: collection literals in call position. A vector, map or quoted symbol
;; is a lookup fn like a keyword: both hosts reject the call with no
;; arguments (get needs its collection) and with more than a key and a
;; default.  Numbers, strings, chars, booleans and nil are not functions on
;; either host at any arity.  Keywords keep the round-13 minimum (jolt
;; accepts a keyword call with extra arguments, so only zero-arg is
;; enforced there).
;; ---------------------------------------------------------------------------

(deftest collection-literals-in-call-position-are-checked
  (testing "a vector called with no arguments"
    (is (re-find #"called with no arguments" (err-msg '(defn f [] ([1 2])))))
    (is (re-find #"called with no arguments" (err-msg '(defn f [] ((quote [1 2])))))))
  (testing "a map called with no arguments"
    (is (re-find #"called with no arguments" (err-msg '(defn f [] ({:a 1}))))))
  (testing "a quoted symbol called with no arguments"
    (is (re-find #"called with no arguments" (err-msg '(defn f [] ('foo))))))
  (testing "a lookup with more than a key and a default"
    (is (re-find #"at most the collection and a default"
                 (err-msg '(defn f [] ({:a 1} :a :d :x)))))
    (is (re-find #"at most the collection and a default"
                 (err-msg '(defn f [] ('foo {'foo 1} :d :x)))))
    (is (re-find #"at most the collection and a default"
                 (err-msg '(defn f [] ([1 2] 0 :d :x)))))
    (is (re-find #"at most the collection and a default"
                 (err-msg '(defn f [] (#{1} 1 2 3))))))
  (testing "never-callable literals"
    (doseq [call ['(1 2) '("ab" 0) '(true 1) '(nil 1) '(\a 0)]]
      (is (re-find #"is not a function"
                   (err-msg (list 'defn 'f [] call))))))
  (testing "legal lookups still pass"
    (is (nil? (err-msg '(defn f [] ([1 2] 0)))))
    (is (nil? (err-msg '(defn f [] ([1 2] 0 :d)))))
    (is (nil? (err-msg '(defn f [] ({:a 1} :a)))))
    (is (nil? (err-msg '(defn f [] ({:a 1} :b :d)))))
    (is (nil? (err-msg '(defn f [] ('foo {'foo 1})))))
    (is (nil? (err-msg '(defn f [] (#{1} 1)))))
    (is (nil? (err-msg '(defn f [] (#{1} 1 2)))))
    (is (nil? (err-msg '(defn f [m] (:k m :d)))))))

;; ---------------------------------------------------------------------------
;; G68: writ's own head shapes. (data) and (data 5) were silently accepted
;; and a non-symbol ctor name registered as one; malformed law/proof forms
;; fell through to the misleading "no proof discharges it" message.
;; ---------------------------------------------------------------------------

(deftest data-and-law-head-shapes-are-validated
  (testing "data shapes"
    (is (re-find #"requires a name" (book-err '[(data)])))
    (is (re-find #"must be a simple symbol" (book-err '[(data 5)])))
    (is (re-find #"must be a simple symbol" (book-err '[(data foo/Bar Nil)])))
    (is (re-find #"constructor name" (book-err '[(data Maybe (Just Maybe) (5 Maybe))])))
    (is (re-find #"constructor name" (book-err '[(data Maybe ([val] Maybe))])))
    (is (re-find #"constructor must be" (book-err '[(data Maybe 5)]))))
  (testing "law shapes"
    (is (re-find #"requires a name" (book-err '[(law)])))
    (is (re-find #"must carry a proposition" (book-err '[(law add-zero)])))
    (is (re-find #"must be a simple symbol" (book-err '[(law 5 (= x x))]))))
  (testing "proof shapes"
    (is (re-find #"requires a name" (book-err '[(proof)])))
    (is (re-find #"cite the law" (book-err '[(proof p)])))
    (is (re-find #"must be a simple symbol"
                 (book-err '[(proof 5 some-law (fn [] 1))]))))
  (testing "a well-formed bare data decl still passes"
    (is (nil? (book-err '[(data Maybe Nil)])))))

;; --- G69: a def with a docstring still registers its fn's arity (the host
;; reads the value from behind the docstring, so the arity table must too) ---

(deftest def-docstring-arity-is-checked
  (testing "an under-arity call through a 4-form def"
    (let [m (book-err '[(def f "doc" (fn [a b] a)) (defn g [] (f 1))])]
      (is (some? m))
      (is (re-find #"takes 2 argument" m))))
  (testing "a variadic minimum survives the docstring"
    (let [m (book-err '[(def f "doc" (fn [a & bs] a)) (defn g [] (f))])]
      (is (some? m))
      (is (re-find #"takes at least 1 argument" m))))
  (testing "a named fn behind a docstring"
    (let [m (book-err '[(def f "doc" (fn h [a b] a)) (defn g [] (f 1))])]
      (is (some? m))
      (is (re-find #"takes 2 argument" m))))
  (testing "a well-arity'd call still passes"
    (is (nil? (book-err '[(def f "doc" (fn [a b] a)) (defn g [] (f 1 2))])))))

;; --- G70: a def bound to a never-callable constant cannot be called ------

(deftest def-literal-calls-are-rejected
  (testing "calling a number-valued def"
    (let [m (book-err '[(def x 5) (defn g [] (x 1))])]
      (is (some? m))
      (is (re-find #"is not a function" m))))
  (testing "with no arguments it is the same error"
    (let [m (book-err '[(def x 5) (defn g [] (x))])]
      (is (some? m))
      (is (re-find #"is not a function" m))))
  (testing "a quoted fn is data, not a callable"
    (let [m (book-err '[(def f (quote (fn [a b] a))) (defn g [] (f 1 2))])]
      (is (some? m))
      (is (re-find #"is not a function" m)))))

;; --- G71: data type parameters are distinct -------------------------------

(deftest data-dup-type-params-are-rejected
  (testing "the same type parameter twice"
    (let [m (book-err '[(writ.defn/data P [a a] (Mk a a))])]
      (is (some? m))
      (is (re-find #"duplicate type parameter" m))))
  (testing "distinct type parameters still pass"
    (is (nil? (book-err '[(writ.defn/data P [a b] (Mk a b))])))))

;; --- G72: recur arity is a shape error, checked before semantic rules --------
;;
;; t.c.'s parse-recur validates tail position and arity at parse time, before
;; any analysis.  In writ the arity gate lived inside the termination walk,
;; which runs after the quantity pass, so a wrong-arity recur was masked by
;; an affinity error (a doubled argument is also a double use) or, on an
;; unmarked fn, by the marking message.  The frame contract is a parse-shape
;; contract (the host rejects it at compile time regardless), so it wins.

(deftest recur-arity-precedes-quantity-and-marking
  (testing "more args than the frame, doubled (was masked by affinity)"
    (let [m (err-msg '(defn f {:writ/descend true} [x] (recur x x)))]
      (is (some? m))
      (is (re-find #"rebinds 1 value" m))))
  (testing "fewer args on an unmarked fn (was masked by the marking message)"
    (let [m (err-msg '(defn f [x y] (recur x)))]
      (is (some? m))
      (is (re-find #"rebinds 2 value\(s\) but is passed 1" m))))
  (testing "a loop that both doubles and over-args (was masked by affinity)"
    (let [m (err-msg '(defn f {:writ/descend true} [x] (loop [y 1] (recur x y y))))]
      (is (some? m))
      (is (re-find #"rebinds 1 value\(s\) but is passed 3" m))))
  (testing "an inner fn's arity is not masked by the outer fn's affinity"
    (let [m (err-msg '(defn f {:writ/descend true} [x] ((fn [a b] (recur a)) x x)))]
      (is (some? m))
      (is (re-find #"rebinds 2 value\(s\) but is passed 1" m))))
  (testing "tail position is still the first shape error"
    (let [m (err-msg '(defn f {:writ/descend true} [x] (+ 1 (recur x))))]
      (is (some? m))
      (is (re-find #"must be in tail position" m)))))

;; --- G73: cond takes an even number of forms ---------------------------------
;;
;; clojure.core/cond throws IllegalArgumentException("cond requires an even
;; number of forms") at macroexpansion; jolt's cond crashes with a raw
;; "index out of bounds" instead, and writ leaked that crash through the
;; macroexpand fallback.  cond-> / cond->> assert the same evenness (jolt
;; crashes the same way), so the family gets one writ-owned guard.

(deftest cond-evenness-is-checked
  (testing "an odd tail of clauses"
    (let [m (err-msg '(defn f [] (cond 1)))]
      (is (some? m))
      (is (re-find #"cond requires an even number of forms" m))))
  (testing "cond-> with an odd tail of clauses"
    (let [m (err-msg '(defn f [x] (cond-> x 1)))]
      (is (some? m))
      (is (re-find #"even number of forms" m))))
  (testing "cond->> with an odd tail of clauses"
    (let [m (err-msg '(defn f [x] (cond->> x 1)))]
      (is (some? m))
      (is (re-find #"even number of forms" m))))
  (testing "empty and even cond forms still pass"
    (is (nil? (err-msg '(defn f [] (cond)))))
    (is (nil? (err-msg '(defn f [] (cond :else 1)))))))

;; --- G74: a dangling `:-` is a shape error, not a silent drop ---------------
;;
;; `(defn f [x] :-)` read the arrow as absent (nil ret) and `(defn f [x :-] x)`
;; consumed the arrow with (nth toks 2) past the end, silently unannotating x.

(deftest dangling-annotation-arrows-are-rejected
  (testing "a trailing :- with no return type"
    (let [m (err-msg '(defn f [x] :-))]
      (is (some? m))
      (is (re-find #"`:-` in `f` must be followed by a return type" m))))
  (testing "a :- inside the parameter vector with no type"
    (let [m (err-msg '(defn f [x :-] x))]
      (is (some? m))
      (is (re-find #"`:-` in `f` must be followed by a type" m))))
  (testing "annotated forms still pass"
    (is (nil? (err-msg '(defn f [x] x))))
    (is (nil? (book-err '[(writ.defn/defn f [x :- writ.kind/Nat] :- writ.kind/Nat x)])))))

;; --- G75: ns :use refers satisfy the ordering gate ---------------------------
;;
;; A book's ns may refer names with (:use [ns :only [syms]]) exactly as with
;; (:require [ns :refer [syms]]); writ's ordering gate read :require clauses
;; only, so a :use-referred name read as "defined later or not a known name".

(deftest ns-use-refers-are-known-names
  (testing ":use :only refers the listed names"
    (is (nil? (book-err '[(ns m (:use [clojure.set :only [union]]))
                          (writ.defn/defn f [] :- writ.kind/Nat (union #{} #{}))]))))
  (testing ":use :refer refers the listed names"
    (is (nil? (book-err '[(ns m (:use [clojure.set :refer [union]]))
                          (writ.defn/defn f [] :- writ.kind/Nat (union #{} #{}))]))))
  (testing ":require :refer keeps working"
    (is (nil? (book-err '[(ns m (:require [clojure.set :refer [union]]))
                          (writ.defn/defn f [] :- writ.kind/Nat (union #{} #{}))]))))
  (testing "a bare (:use ns) has no name list to read and still rejects"
    (let [m (book-err '[(ns m (:use clojure.set))
                        (writ.defn/defn f [] :- writ.kind/Nat (union #{} #{}))])]
      (is (some? m))
      (is (re-find #"defined later or is not a known name" m))))
  (testing "an unreferred name is still an ordering error"
    (let [m (book-err '[(ns m (:use [clojure.set :only [union]]))
                        (writ.defn/defn f [] :- writ.kind/Nat (difference #{} #{}))])]
      (is (some? m))
      (is (re-find #"defined later or is not a known name" m)))))

;; --- G76: a def whose value IS the docstring, or nil, is a constant -------
;;
;; The host reads (def x "doc") as x bound to the string and (def x nil) as
;; x bound to nil; both throw IFn casts when called.  writ's arity table
;; dropped both (the second-tail read nils out on a doc-only tail, and the
;; some?-test drops a literal nil value), so the call slipped through.

(deftest doc-only-and-nil-defs-are-constants
  (testing "a def whose value is the docstring"
    (let [m (book-err '[(def x "doc") (writ.defn/defn g [] :- writ.kind/Nat (x))])]
      (is (some? m))
      (is (re-find #"is not a function" m))))
  (testing "a def explicitly bound to nil"
    (let [m (book-err '[(def x nil) (writ.defn/defn g [] :- writ.kind/Nat (x))])]
      (is (some? m))
      (is (re-find #"is not a function" m))))
  (testing "value positions still pass"
    (is (nil? (book-err '[(def x "doc") (writ.defn/defn g [] :- writ.kind/Nat x)])))
    (is (nil? (book-err '[(def x nil) (writ.defn/defn g [] :- writ.kind/Nat x)]))))
  (testing "the round-20 arity read survives"
    (let [m (book-err '[(def f "doc" (fn [a b] a))
                        (writ.defn/defn g [] :- writ.kind/Nat (f 1))])]
      (is (some? m))
      (is (re-find #"takes 2 argument" m)))))

;; --- G77: quote takes exactly one form --------------------------------------
;;
;; typed.cljc.analyzer's parse-quote rejects any count other than two
;; ("Wrong number of args to quote, had: N") and the JVM compiler does the
;; same; jolt is lax (it evaluates (quote a b) and (quote) without
;; complaint), so writ owns the contract.  Until now (quote a b) silently
;; dropped b and (quote) silently read as nil.

(deftest quote-arity-is-checked
  (testing "two forms after quote"
    (let [m (err-msg '(defn f [] (quote a b)))]
      (is (some? m))
      (is (re-find #"Wrong number of args to quote, had: 2" m))))
  (testing "no form after quote"
    (let [m (err-msg '(defn f [] (quote)))]
      (is (some? m))
      (is (re-find #"Wrong number of args to quote, had: 0" m))))
  (testing "a proper quote still passes"
    (is (nil? (err-msg '(defn f [] (quote a)))))
    (is (nil? (err-msg '(defn f [] '[1 2]))))))

;; --- G78: match head and arm shapes ----------------------------------------
;;
;; The match gate owned the too-short form and the separator, but the arm
;; shapes were unchecked: a type-only match with no arms fell through to the
;; misleading "not exhaustive" message, a 1-element arm read as a nil body,
;; a 3-element arm silently dropped its extra element, and a non-seq arm
;; crashed the host ("Don't know how to create ISeq") through check-book.

(deftest match-head-and-arm-shapes-are-checked
  (let [book (fn [body]
               (list '(writ.defn/data Maybe Nil (Just Int))
                     (list 'writ.defn/defn 'f '[x :- Maybe] body)))]
    (testing "a match with no arms is a shape error, not a coverage error"
      (let [m (book-err (book '(writ.defn/match x :- Maybe)))]
        (is (some? m))
        (is (re-find #"needs a scrutinee, a type and at least one arm" m))))
    (testing "a 1-element arm has no result"
      (let [m (book-err (book '(writ.defn/match x :- Maybe (Nil))))]
        (is (some? m))
        (is (re-find #"a match arm must be `\(pattern result\)`" m))))
    (testing "a bare symbol is not an arm"
      (let [m (book-err (book '(writ.defn/match x :- Maybe Nil 0 Just 1)))]
        (is (some? m))
        (is (re-find #"a match arm must be `\(pattern result\)`" m))))
    (testing "a 3-element arm's extra element is not silently dropped"
      (let [m (book-err (book '(writ.defn/match x :- Maybe (Nil 0 extra))))]
        (is (some? m))
        (is (re-find #"a match arm must be `\(pattern result\)`" m))))
    (testing "well-formed matches still pass"
      (is (nil? (book-err '[(writ.defn/data Maybe Nil (Just Int))
                            (writ.defn/defn f [x :- Maybe] :- writ.kind/Nat
                              (writ.defn/match x :- Maybe (Nil 0) ((Just v) v)))])))
      (is (nil? (book-err '[(writ.defn/data Maybe Nil (Just Int))
                            (writ.defn/defn f [x :- Maybe] :- writ.kind/Nat
                              (writ.defn/match x :- Maybe (Nil 0) ((Just ^:many v) v)))]))))))

;; --- G79: bare unquote is unsupported; data type params are binders -------
;;
;; The host throws "Unsupported special form: unquote" (and -splicing) for a
;; unquote that survives reading: syntax-quote consumes its unquotes at read
;; time, so a bare (unquote x) in a lowered form is always an error.  writ's
;; macroexpand fallback treated it as an ordinary invoke with no arity entry
;; and accepted it.  A `data` type parameter is a binder (the R15 t.c.
;; valid-binding-symbol? port): [1 2], [foo/bar] and [a.b] were accepted.

(deftest bare-unquote-is-unsupported
  (testing "every spelling of a surviving unquote"
    (doseq [call ['(unquote x) '(clojure.core/unquote x)]]
      (is (re-find #"Unsupported special form: unquote"
                   (err-msg (list 'defn 'f '[x] call))))))
  (testing "every spelling of a surviving unquote-splicing"
    (doseq [call ['(unquote-splicing x) '(clojure.core/unquote-splicing x)]]
      (is (re-find #"Unsupported special form: unquote-splicing"
                   (err-msg (list 'defn 'f '[x] call))))))
  (testing "unquote inside syntax-quote stays legal"
    (is (nil? (err-msg '(defn f [x] `(a ~x)))))
    (is (nil? (err-msg '(defn f [x] `(a ~@[x])))))))

(deftest data-type-params-are-simple-symbols
  (testing "a non-symbol type parameter"
    (let [m (book-err '[(writ.defn/data P [1 2] Nil)])]
      (is (some? m))
      (is (re-find #"type parameter in `P` must be a simple symbol" m))))
  (testing "a qualified type parameter"
    (let [m (book-err '[(writ.defn/data P [foo/bar] Nil)])]
      (is (some? m))
      (is (re-find #"type parameter in `P` must be a simple symbol" m))))
  (testing "a dotted type parameter"
    (let [m (book-err '[(writ.defn/data P [a.b] Nil)])]
      (is (some? m))
      (is (re-find #"type parameter in `P` must be a simple symbol" m))))
  (testing "simple type parameters still pass"
    (is (nil? (book-err '[(writ.defn/data P [a] (Mk a))])))))

;; --- G80: a def's own name cannot be a call operand in its value ----------
;;
;; The host stores an unforced self-reference fine ((def v [1 v]) evaluates),
;; but a call forces the read while the name is still unbound and throws
;; Var$Unbound at load.  A self-reference inside a fn body is recursion and
;; stays legal (checked for descent separately); a bare collection element
;; only stores the unbound value and stays legal too.

(deftest def-value-self-reference
  (testing "the own name as a call argument"
    (let [m (book-err '[(def x (inc x))])]
      (is (some? m))
      (is (re-find #"reference earlier names only" m))))
  (testing "nested calls force the same way"
    (let [m (book-err '[(def y [1 (inc y)])])]
      (is (some? m))
      (is (re-find #"reference earlier names only" m))))
  (testing "stored self-references are refused too (Bend: type_level_recursion,
            a bare self-reference is an escaping value)"
    (is (re-find #"reference earlier names only" (book-err '[(def v [1 v])])))
    (is (re-find #"reference earlier names only" (book-err '[(def m {:a m})])))
    (is (re-find #"reference earlier names only" (book-err '[(def a a)]))))
  (testing "a self-reference as a value escapes (bend.ts: a self-reference never
            escapes as a value), but recursion inside a fn body stays legal"
    (is (re-find #"refers to itself as a value" (book-err '[(def h (fn [] h))])))
    (is (nil? (book-err '[(def ^{:writ/descend true} f
                            (fn [^:many ^Nat n] (if (zero? n) 0 (f (dec n)))))])))))

;; --- G81: effect-fn family rejects like throw/new ---------------------------
;;
;; throw, new and interop reject as effect code, but the same contract on a
;; plain core fn was unenforced: eval, the load family, namespace mutation
;; (require/import/intern), var mutation (alter-var-root/with-redefs), state
;; (atom/swap!/reset!/volatile!) and concurrency (future/promise/agent/dosync)
;; all passed silently -- and the clojure.core/qualified spelling escaped
;; every gate, since they sit behind the unqualified-only wrapper.  The hosts
;; run these fine (they are ordinary fns); writ owns the purity contract
;; statically, so a book's own defn of the same name shadows core and wins.

(deftest effect-fn-family-is-rejected
  (testing "the eval and load family"
    (doseq [call ['(eval x) '(clojure.core/eval x)
                  '(load "nope") '(load-file "nope")
                  '(load-string "x") '(load-reader nil)]]
      (is (re-find #"writ checks pure data-and-functions code only"
                   (err-msg (list 'defn 'f '[x] call))))))
  (testing "namespace and var mutation"
    (doseq [call ['(require 'clojure.set) '(use 'clojure.set)
                  '(import 'foo.Bar) '(refer 'clojure.set)
                  '(alter-var-root v inc) '(with-redefs [inc dec] 1)
                  '(intern 'user 'x 1)]]
      (is (re-find #"effect code"
                   (err-msg (list 'defn 'f '[v] call))))))
  (testing "state and concurrency"
    (doseq [call ['(atom 1) '(swap! a inc) '(reset! a 1)
                  '(volatile! 1) '(future 1) '(promise) '(dosync 1)
                  '(locking a 1) '(send a inc)]]
      (is (re-find #"effect code"
                   (err-msg (list 'defn 'f '[a] call))))))
  (testing "a book's own name shadows the core effect fn"
    (is (nil? (book-err '[(writ.defn/defn eval [e] :- writ.kind/Nat e)
                          (writ.defn/defn g [x] :- writ.kind/Nat (eval x))])))
    (is (nil? (book-err '[(writ.defn/defn future [] :- writ.kind/Nat 1)
                          (writ.defn/defn g [] :- writ.kind/Nat (future))]))))
  (testing "throw keeps its dedicated message"
    (is (re-find #"host interop or effect code"
                 (err-msg '(defn f [x] (throw x)))))))

;; --- G82: key/value pair parity --------------------------------------------
;;
;; assoc, hash-map and array-map are variadic, so the arity table cannot see
;; the JVM's pair contract: both hosts throw on an odd tail (assoc: an even
;; number of key/vals; hash-map/array-map: an odd number of map entries),
;; but writ accepted every odd shape.

(deftest pair-parity-is-checked
  (testing "assoc with an odd tail of key/vals"
    (is (re-find #"assoc.*even number of key/vals"
                 (err-msg '(defn f [m] (assoc m :a 1 :b)))))
    (is (re-find #"assoc.*even number of key/vals"
                 (err-msg '(defn f [m] (assoc m 0 :a 5))))))
  (testing "hash-map and array-map with an odd number of entries"
    (is (re-find #"odd number of map entries"
                 (err-msg '(defn f [] (hash-map :a)))))
    (is (re-find #"odd number of map entries"
                 (err-msg '(defn f [] (array-map :a))))))
  (testing "even pairs still pass"
    (is (nil? (err-msg '(defn f [m] (assoc m :a 1)))))
    (is (nil? (err-msg '(defn f [m] (assoc m 0 :a)))))
    (is (nil? (err-msg '(defn f [] (hash-map :a 1)))))
    (is (nil? (err-msg '(defn f [] (array-map :a 1))))))
  (testing "a book's own name shadows the core fn"
    (is (nil? (book-err '[(writ.defn/defn hash-map [k] :- writ.kind/Nat k)
                          (writ.defn/defn g [] :- writ.kind/Nat (hash-map :a))])))))

;; --- G83: locals and book names shadow macros ------------------------------
;;
;; typed.clj.analyzer's macroexpand-1 never expands a head bound as a local
;; ("locals shadow macros").  writ macroexpanded every non-special head, so
;; a local or book fn named like a core macro was checked as the macro.

(deftest locals-shadow-macros
  (testing "a letfn fn named like a macro is a call, arity-checked"
    (is (re-find #"`when` takes 2 argument\(s\) but is passed 1"
                 (err-msg '(defn f [] (letfn [(when [a b] a)] (when 1)))))))
  (testing "a correct call to the shadowing local passes"
    (is (nil? (err-msg '(defn f [] (letfn [(cond [a] a)] (cond 1)))))))
  (testing "a book fn named like a core macro shadows it"
    (is (re-find #"`future` takes 0 argument\(s\) but is passed 1"
                 (book-err '[(writ.defn/defn future [] :- writ.kind/Nat 1)
                             (writ.defn/defn g [] :- writ.kind/Nat (future 1))])))))

;; --- G84: effect family in value position, I/O, qualified core arity --------

(deftest effect-family-edges
  (testing "an effect fn passed as a value is still effect code"
    (is (re-find #"effect code" (err-msg '(defn f [xs] (map eval xs))))))
  (testing "console I/O, randomness, taps, resources and protocol extension"
    (doseq [call ['(println x) '(prn x) '(rand-int x) '(tap> x)
                  '(with-open [r x] 1) '(extend-type String P (g [y] 1))
                  '(requiring-resolve x) '(time x)]]
      (is (re-find #"effect code" (err-msg (list 'defn 'f '[x] call))))))
  (testing "a qualified core call is arity- and pair-checked"
    (is (re-find #"clojure.core/inc` takes 1 argument"
                 (err-msg '(defn f [] (clojure.core/inc 1 2)))))
    (is (re-find #"odd number of map entries"
                 (err-msg '(defn f [] (clojure.core/hash-map :a)))))
    (is (re-find #"odd number of map entries"
                 (err-msg '(defn f [c] (sorted-map-by c :a)))))))

;; --- G85: JVM special forms and class-building macros are interop ----------
;;
;; typed.clj.analyzer parses reify*, deftype*, case* and import* as JVM
;; specials; writ accepted the bare specials and rejected reify/proxy only
;; through a misleading multi-arity message.

(deftest jvm-specials-are-interop
  (doseq [call ['(reify Object (toString [_] "x"))
                '(reify* [Object] (toString [_] "x"))
                '(proxy [Object] [] (toString [] "x"))
                '(deftype* Foo Foo [a] :implements [])
                '(case* x 0 0 :d {} :compact :int)
                '(gen-class)]]
    (is (re-find #"host interop or effect code"
                 (err-msg (list 'defn 'f '[x] call))))))

;; --- G86: one finally per try (t.c. parse-try) ------------------------------

(deftest one-finally-per-try
  (is (re-find #"Only one finally clause allowed in try expression"
               (err-msg '(defn f [] (try 1 (finally 2) (finally 3))))))
  (is (re-find #"`finally` clause must be last"
               (err-msg '(defn f [] (try 1 (finally 2) (inc 1)))))))

;; --- G87: parametric substitution keeps function types (round 29) ----------
;;
;; kind/subst-param and match/subst rebuilt a substituted seq type with mapv,
;; so (-> a Nat) became the vector [-> a Nat]; function-type? missed it and
;; the kind fell through to Data.  A function field then licensed ^:many,
;; which is Omega through a negative datatype (Bend: negative_data_reuse,
;; data_phantom_function, BendTT 3.1).

(deftest substituted-function-types-stay-type
  (testing "a parametric fn field is not Data"
    (is (re-find #"not Data"
                 (book-err '[(writ.defn/data F [a] (MkF (-> a writ.kind/Nat)))
                             (writ.defn/defn k [^:many x :- (F writ.kind/Nat)] :- writ.kind/Nat 0)]))))
  (testing "a fn nested two datatypes deep is not Data"
    (is (re-find #"not Data"
                 (book-err '[(writ.defn/data Bx [a] (Wr a))
                             (writ.defn/data Wp [a] (MkW (Bx a)))
                             (writ.defn/defn k [^:many x :- (Wp (-> writ.kind/Nat writ.kind/Nat))]
                               :- writ.kind/Nat 0)]))))
  (testing "a ^:many pattern binder over a negative field is rejected"
    (is (re-find #"cannot be reusable"
                 (book-err '[(writ.defn/data Tn (Ln (-> Tn Tn)) (Vn writ.kind/Nat))
                             (writ.defn/defn ap [t :- Tn] :- writ.kind/Nat
                               (writ.defn/match t :- Tn
                                 ((Ln ^:many f) (f (Ln f)))
                                 ((Vn n) n)))]))))
  (testing "a data-only parametric instance stays reusable"
    (is (nil? (book-err '[(writ.defn/data Bx [a] (Wr a))
                          (writ.defn/defn k [^:many x :- (Bx writ.kind/Nat)] :- writ.kind/Nat 0)])))))

;; --- G88: Any and unknown type names are not Data --------------------------
;;
;; Only a declared ground or data type is provably Data (Bend: an opaque
;; T: Type never licenses +, cop_plain_domain_000).  Any, a type parameter
;; name and a parameter used as a type all fell through to Data, so
;; (defn om [^:many x :- Any] (x x)) was Omega.

(deftest opaque-types-are-not-data
  (is (re-find #"not Data"
               (book-err '[(writ.defn/defn om [^:many x :- Any] (x x))])))
  (is (re-find #"not Data"
               (book-err '[(writ.defn/defn tw [t :- writ.kind/Nat, ^:many x :- t] x)])))
  (is (nil? (book-err '[(writ.defn/defn ok [^:many x :- writ.kind/Nat] :- writ.kind/Nat (+ x x))]))))

;; --- G89: a closure passed to a core fn may run many times ------------------
;;
;; Bend's closures are affine and a template argument must be closed, so a
;; closure capturing an affine binder cannot be handed to a higher-order fn
;; that may call it repeatedly.  writ counted the body once, so
;; (map (fn [_] x) [1 2]) copied x -- Omega when x is a fn.  Core fns that
;; duplicate a plain argument (repeat, constantly, ...) copy it too.

(deftest closures-passed-to-core-fns-copy-their-captures
  (testing "an affine capture in a fn passed to a core HOF"
    (doseq [call ['(map (fn [_] x) [1 2]) '(mapv (fn [y] (+ x y)) [1 2])
                  '(reduce (fn [acc _] (conj acc x)) [] [1 2])
                  '(repeatedly 3 (fn [] x)) '(filter (fn [y] (= x y)) [1])]]
      (is (re-find #"`x`.*may be called more than once"
                   (err-msg (list 'defn 'f '[x] call))))))
  (testing "a closure bound to a local and then passed on"
    (is (re-find #"may be called more than once"
                 (err-msg '(defn f [x] (let [g (fn [_] x)] (map g [1 2])))))))
  (testing "core fns that duplicate a plain argument"
    (doseq [call ['(repeat 2 x) '(constantly x) '(iterate inc x) '(cycle x)]]
      (is (re-find #"`x`.*copies it"
                   (err-msg (list 'defn 'f '[x] call))))))
  (testing "reusable captures, closed fns and direct calls pass"
    (is (nil? (err-msg '(defn f [^:many ^Nat x] (map (fn [y] (+ x y)) [1 2])))))
    (is (nil? (err-msg '(defn f [xs] (map (fn [y] (inc y)) xs)))))
    (is (nil? (err-msg '(defn f [x] ((fn [y] (+ x y)) 1)))))
    (is (nil? (err-msg '(defn f [x] (let [g (fn [y] (+ x y))] (g 1))))))
    (is (nil? (book-err '[(defn ap [g] (g 1))
                          (defn f [x] (ap (fn [y] (+ x y))))])))))

;; --- G90: overlapping destructure copies its source -------------------------
;;
;; Destructuring consumes the source like a match: each binder takes a
;; distinct piece.  Two binders over the same key, or :as beside any field,
;; copy the value -- legal only when the source is reusable.  destructure's
;; G__ temps carry :w, so these copies were invisible.

(deftest overlapping-destructure-copies-the-source
  (doseq [form ['(defn f [m] (let [{a :a b :a} m] [a b]))
                '(defn f [m] (let [{:keys [a] :as all} m] [a all]))
                '(defn f [xs] (let [[a :as v] xs] [a v]))
                '(defn f [m] (let [{:keys [a] b :a} m] [a b]))]]
    (is (re-find #"overlapping binders" (err-msg form))))
  (testing "distinct pieces, or a reusable source, pass"
    (is (nil? (err-msg '(defn f [m] (let [{:keys [a b]} m] [a b])))))
    (is (nil? (err-msg '(defn f [xs] (let [[a b & r] xs] [a b r])))))
    (is (nil? (err-msg '(defn f [^:many ^{:writ/type (Map Keyword Nat)} m]
                          (let [{:keys [a] :as all} m] [a all])))))))

;; --- G91: + forms only over a proven Data type; annotations are checked ----
;;
;; Bend's `+x = v` needs v's type to be Data.  writ could not tell a number
;; from a function on an untyped binder, so (defn dup [^:many x] [x x]) and
;; (let [^:many w (identity (fn ...))] (w w)) reached Omega, and annotations
;; were trusted: (defn om [^:many f :- Nat] (f f)) passed.  A ^:many local
;; now needs an init whose type is inferred Data or a Data annotation; a
;; ^:many param needs a Data annotation (`:- T`, or ^T on a plain defn).
;; Calls, returns and applications are checked against the annotations.

(deftest reusable-binders-need-proven-data
  (testing "an untyped ^:many param must be annotated"
    (is (re-find #"`x` in `dup` is reusable.*no type"
                 (err-msg '(defn dup [^:many x] [x x]))))
    (is (re-find #"no type"
                 (book-err '[(defn dup [^:many x] [x x])
                             (defn om [f] (let [[a b] (dup f)] (a b)))]))))
  (testing "a typed ^:many param passes, as a plain ^tag or a w/defn :-"
    (is (nil? (err-msg '(defn dup [^:many ^Nat x] [x x]))))
    (is (nil? (book-err '[(writ.defn/defn dup [^:many x :- writ.kind/Nat] [x x])]))))
  (testing "a ^:many local over an inferred Data init passes"
    (is (nil? (err-msg '(defn f [x] (let [^:many y (inc x)] (+ y y))))))
    (is (nil? (err-msg '(defn f [] (loop [^:many i 10] (if (zero? i) 0 (+ i i))))))))
  (testing "a ^:many local over an unknown or function init is rejected"
    (doseq [init ['(identity (fn [x] x)) '(partial + 1) '(second t) '(g 1)]]
      (is (re-find #"reusable.*(no type|not Data)"
                   (err-msg (list 'defn 'f '[t g]
                                  (list 'let ['^:many w init] '[w w])))))))
  (testing "a typed value in call position must have a function type"
    (is (re-find #"`f` has type Nat.*not a function"
                 (book-err '[(writ.defn/defn om [^:many f :- writ.kind/Nat] (f f))]))))
  (testing "call arguments and returns are checked against annotations"
    (is (re-find #"`f` expects Nat.*String"
                 (book-err '[(writ.defn/defn f [x :- writ.kind/Nat] :- writ.kind/Nat x)
                             (writ.defn/defn g [] :- writ.kind/Nat (f "s"))])))
    (is (re-find #"`f` expects Nat.*Int"
                 (book-err '[(writ.defn/defn f [x :- writ.kind/Nat] :- writ.kind/Nat x)
                             (writ.defn/defn g [] :- writ.kind/Nat (f -1))])))
    (is (re-find #"`f` returns Bool.*Nat"
                 (book-err '[(writ.defn/defn f [x :- writ.kind/Nat] :- writ.kind/Bool x)])))
    (is (nil? (book-err '[(writ.defn/defn f [x :- writ.kind/Nat] :- writ.kind/Int (inc x))
                          (writ.defn/defn g [] :- writ.kind/Int (f 3))])))))

;; --- G92: descent is per column (round 30) ----------------------------------
;;
;; Bend reads a self-call's arguments left to right: each is passed unchanged
;; until one is a strict subterm of ITS OWN column (tests/halt
;; size_change_reject_000, joint_group_sum).  writ credited a shrink of any
;; parameter to whichever argument carried it.

(deftest descent-is-per-column
  (is (re-find #"does not descend"
               (err-msg '(defn f {:writ/descend true} [a ^:many ^Nat b]
                           (if (zero? b) 0 (f (dec b) (+ b 2)))))))
  (is (re-find #"does not descend"
               (err-msg '(defn g {:writ/descend true} [^:many ^Nat a ^:many ^Nat b]
                           (if (zero? a) 0 (g b (dec a)))))))
  (is (nil? (err-msg '(defn g {:writ/descend true} [^:many ^Nat a b]
                        (if (zero? a) b (g (dec a) (inc b))))))))

;; --- G93: a shrink needs a guard on its column (Nat or pos?) ----------------
;;
;; Bend: a column shrinks only in a match arm that refined it
;; (unguarded_decrement, wrong_param_descent).  (dec d) with no test on d,
;; or under a test on another parameter, loops forever.  Clojure integers
;; can be negative, so dec descends only on a Nat column under a zero test,
;; or on any integer under a pos?-style test.  rest/drop need a non-empty
;; test; next/butlast and element reads need the column to be non-nil.

(deftest shrinks-need-a-guard-on-their-column
  (testing "unguarded shrinks are refused"
    (doseq [form ['(defn f {:writ/descend true} [^Nat d] (f (dec d)))
                  '(defn f {:writ/descend true} [xs] (f (rest xs)))
                  '(defn f {:writ/descend true} [v] (f (next v)))
                  '(defn f {:writ/descend true} [v] (f (second v)))]]
      (is (re-find #"does not descend.*guard" (err-msg form)))))
  (testing "a guard on another parameter does not count"
    (is (re-find #"guard"
                 (err-msg '(defn f {:writ/descend true} [^:many ^Nat d ^:many ^Nat e]
                             (if (zero? e) 0 (f (dec d) e)))))))
  (testing "dec under zero? needs a Nat column; pos? works for any integer"
    (is (re-find #"guard"
                 (err-msg '(defn f {:writ/descend true} [^:many d]
                             (if (zero? d) 0 (f (dec d)))))))
    (is (nil? (err-msg '(defn f {:writ/descend true} [^:many ^Nat d]
                          (if (zero? d) 0 (f (dec d)))))))
    (is (nil? (err-msg '(defn f {:writ/descend true} [^:many ^Int d]
                          (if (pos? d) (f (dec d)) 0))))))
  (testing "rest needs a non-empty test; next and first need non-nil"
    (is (nil? (err-msg '(defn f {:writ/descend true} [^:many ^{:writ/type (List Nat)} xs]
                          (if (empty? xs) 0 (f (rest xs)))))))
    (is (nil? (err-msg '(defn f {:writ/descend true} [^:many ^{:writ/type (List Nat)} xs]
                          (if (seq xs) (f (rest xs)) 0)))))
    (is (re-find #"guard"
                 (err-msg '(defn f {:writ/descend true} [^:many ^{:writ/type (List Nat)} xs]
                             (if xs (f (rest xs)) 0)))))
    (is (nil? (err-msg '(defn f {:writ/descend true} [^:many ^{:writ/type (List Nat)} xs]
                          (if xs (f (next xs)) 0)))))
    (is (nil? (err-msg '(defn f {:writ/descend true} [^:many ^{:writ/type (Vec Nat)} t]
                          (if (vector? t) (f (nth t 1)) 0)))))))

;; --- G94: a self-reference is only ever a call head -------------------------
;;
;; Bend allows a def's own name only as the head of a call, where descent is
;; checked (ann_transparency, type_level_recursion).  writ let the name
;; escape as a value -- (apply f [x]), (let [g f] (g x)), ((var f) x),
;; (trampoline f x) -- even with no marker.

(deftest self-reference-must-be-a-call-head
  (doseq [form ['(defn f [x] (apply f [x]))
                '(defn f [x] (let [g f] (g x)))
                '(defn f [x] ((var f) x))
                '(defn f [x] (trampoline f x))
                '(defn f [x] (map f [x]))
                '(defn a {:writ/descend true} [] a)]]
    (is (re-find #"refers to itself as a value" (err-msg form))))
  (is (re-find #"refers to itself as a value"
               (err-msg '(defn f [xs] ((fn g [y] (map g y)) xs))))))

;; --- G95: recur is judged against its own frame -----------------------------

(deftest recur-descends-against-its-frame
  (doseq [form ['(defn f {:writ/descend true} [^Nat d] (loop [x (dec d)] (recur x)))
                '(defn f {:writ/descend true} [^:many ^Nat d]
                   (loop [i 0] (if (zero? d) 0 (recur (dec d)))))]]
    (is (re-find #"does not descend" (err-msg form))))
  (testing "a literal-seeded counter descends under its own guard"
    (is (nil? (err-msg '(defn f {:writ/descend true} []
                          (loop [^:many i 10] (if (zero? i) 0 (recur (dec i))))))))))

;; --- G96: projections with defaults and shadowed projections ----------------

(deftest forged-projections-do-not-descend
  (testing "a default argument can hand the value back unchanged"
    (is (re-find #"does not descend"
                 (err-msg '(defn f {:writ/descend true} [^:many m]
                             (if m (f (get m :k m)) 0)))))
    (is (re-find #"does not descend"
                 (err-msg '(defn f {:writ/descend true} [^:many xs]
                             (if xs (f (nth xs 9 xs)) 0))))))
  (testing "a book fn named like a projection is not a projection"
    (is (re-find #"does not descend"
                 (book-err '[(writ.defn/defn dec [x :- Nat] :- Nat x)
                             (defn f {:writ/descend true} [^:many ^Nat d]
                               (if (zero? d) 0 (f (dec d))))])))))

;; --- G97: literal refinement: a lexicographic phase column -----------------
;;
;; Bend: lexicographic_descent -- the first column stays, and the second is
;; a literal strictly below the literal it was refined to.

(deftest literal-phase-columns-descend
  (is (nil? (err-msg '(defn flip {:writ/descend true} [^:many ^Nat d ^:many ^Nat m]
                        (cond (zero? d) 0
                              (zero? m) (flip (dec d) 1)
                              (= m 1) (flip d 0)
                              :else 0)))))
  (is (re-find #"does not descend"
               (err-msg '(defn flip {:writ/descend true} [^:many ^Nat d ^:many ^Nat m]
                           (if (= m 1) (flip d 2) 0))))))

;; --- G98: refl is capture-avoiding and alpha-aware (round 31) --------------
;;
;; norm/subst never renamed binders, so a substituted free variable could be
;; captured and refl proved false laws (Bend: binder_name_capture;
;; conversion is up to alpha).  (= (let [y n] (let [n 2] y)) 2) was proved.

(defn- law-err [prop proof]
  (book-err [(list 'writ.defn/law 'l prop) (list 'writ.defn/proof 'p 'l proof)]))

(deftest refl-avoids-capture
  (is (re-find #"not convertible" (law-err '(= (let [y n] (let [n 2] y)) 2) 'refl)))
  (is (re-find #"not convertible" (law-err '(= (let [a b] (let [b 1] a)) 1) 'refl)))
  (testing "alpha-equivalent terms are convertible"
    (is (nil? (law-err '(= (let [x 1] [x 2]) (let [y 1] [y 2])) 'refl)))
    (is (nil? (law-err '(= (let [a 1 b 2] (+ a b)) 3) 'refl)))
    (is (nil? (law-err '(= ((fn [x] (inc x)) 1) 2) 'refl)))))

;; --- G99: exists, forall and => respect binders --------------------------

(deftest quantifiers-respect-binders
  (testing "a witness is not substituted under a binder that shadows it"
    (is (re-find #"not convertible"
                 (law-err '(exists [x Nat] (= (let [x 1] x) 5)) '(witness 5 refl))))
    (is (some? (law-err '(exists [x Nat] (forall [x Nat] (= x 5)))
                        '(witness 5 (fn [x] refl))))))
  (testing "a witness reaches inside collections"
    (is (nil? (law-err '(exists [x Nat] (= [x] [5])) '(witness 5 refl)))))
  (testing "a hypothesis about a shadowed name does not leak"
    (is (some? (law-err '(=> (= a 1) (forall [a Int] (= a 1)))
                        '(fn [h] (fn [a] h))))))
  (testing "a forall proof may rename its binder"
    (is (nil? (law-err '(forall [n Nat] (= (+ n 0) n)) '(fn [m] refl))))))

;; --- G100: propositions and proof terms have exact shapes -----------------

(deftest proposition-arity-is-exact
  (doseq [prop ['(= 1 1 2) '(=> (= 1 1) (= 2 2) (= 3 4))
                '(forall [x Nat] (= x x) (= 1 2)) '(forall [x] (= x x))]]
    (is (re-find #"Wrong number|must be|takes" (law-err prop '(fn [x] refl)))))
  (is (re-find #"Wrong number" (law-err '(= 1 1 2) 'refl)))
  (is (re-find #"implication is proved by `\(fn \[h\] body\)`"
               (law-err '(=> (= 1 1) (= 1 1)) '(fn h [x] x)))))

;; --- G101: reductions keep Clojure's strict evaluation --------------------

(deftest reductions-are-strict
  (testing "a throwing init or statement is not dropped"
    (is (some? (law-err '(= (let [y (quot 1 0)] 1) 1) 'refl)))
    (is (some? (law-err '(= (do (quot 1 0) 1) 1) 'refl))))
  (testing "a throwing term is not equal to itself"
    (is (re-find #"throws" (law-err '(= (quot 1 0) (quot 1 0)) 'refl)))
    (is (re-find #"throws" (law-err '(= (case 5 1 :a) (case 5 1 :a)) 'refl))))
  (testing "the identities need a number"
    (is (re-find #"not convertible" (law-err '(= (+ x 0) x) 'refl)))
    (is (nil? (law-err '(forall [x Nat] (= (+ x 0) x)) '(fn [x] refl))))
    (is (nil? (law-err '(forall [s Int] (= (* s 1) s)) '(fn [s] refl))))))

;; --- G102: folds are namespace- and binding-aware -------------------------

(deftest folds-respect-names
  (is (re-find #"not convertible" (law-err '(= (foo/+ 1 1) 2) 'refl)))
  (is (re-find #"not convertible"
               (book-err '[(writ.defn/defn inc [x :- writ.kind/Nat] :- writ.kind/Nat x)
                           (writ.defn/law l (= (inc 1) 2))
                           (writ.defn/proof p l refl)])))
  (is (nil? (law-err '(= (clojure.core/+ 1 1) 2) 'refl))))

;; --- G103: exists checks its domain; fns are never refl-equal -------------

(deftest witnesses-and-fn-equality
  (is (re-find #"witness.*Nat" (law-err '(exists [x Nat] (= x -1)) '(witness -1 refl))))
  (is (re-find #"witness.*Nat" (law-err '(exists [x Nat] (= x "s")) '(witness "s" refl))))
  (is (re-find #"not a type" (law-err '(exists [x Bogus] (= x 1)) '(witness 1 refl))))
  (testing "Clojure's = on fns is identity (Bend: no_funext_000)"
    (is (re-find #"fn" (law-err '(= (fn [x] x) (fn [x] x)) 'refl)))
    (is (re-find #"fn" (law-err '(= (fn [x] (+ x 0)) (fn [x] x)) 'refl)))))

;; --- G104: law and proof names are book names; law bodies are checked -----

(deftest laws-are-book-citizens
  (testing "a law or proof may not reuse a book name"
    (is (re-find #"more than once"
                 (book-err '[(writ.defn/defn f [x :- writ.kind/Nat] :- writ.kind/Nat x)
                             (writ.defn/law f (= 1 1)) (writ.defn/proof pf f refl)])))
    (is (re-find #"more than once"
                 (book-err '[(writ.defn/defn g [x :- writ.kind/Nat] :- writ.kind/Nat x)
                             (writ.defn/law l (= 1 1)) (writ.defn/proof g l refl)])))
    (is (re-find #"more than once"
                 (book-err '[(writ.defn/law l (= 1 1)) (writ.defn/proof l l refl)]))))
  (testing "law bodies obey the ordering, arity and effect rules"
    (is (re-find #"defined later|not a known name"
                 (law-err '(= (nope 1) (nope 1)) 'refl)))
    (is (re-find #"effect code" (law-err '(= (eval 1) (eval 1)) 'refl)))
    (is (re-find #"takes 1 argument"
                 (book-err '[(writ.defn/defn g [x :- writ.kind/Nat] :- writ.kind/Nat x)
                             (writ.defn/law l (= (g 1 2) (g 1 2)))
                             (writ.defn/proof p l refl)])))
    (is (re-find #"defined later"
                 (book-err '[(writ.defn/law l (= (g 1) (g 1)))
                             (writ.defn/proof p l refl)
                             (writ.defn/defn g [x :- writ.kind/Nat] :- writ.kind/Nat x)])))
    (is (re-find #"Duplicate|duplicate case"
                 (law-err '(= (case 1 1 :a 1 :b :c) :a) 'refl)))))

(deftest law-terms-and-order
  (testing "a law term cannot recur or loop"
    (is (re-find #"recur|loop" (law-err '(= (recur 1) (recur 1)) 'refl)))
    (is (re-find #"recur|loop" (law-err '(= (loop [x 1] x) 1) 'refl))))
  (testing "a proof comes after the law it discharges"
    (is (re-find #"declared later|before"
                 (book-err '[(writ.defn/proof p l refl) (writ.defn/law l (= 1 1))]))))
  (testing "laws and proofs are not values"
    (is (re-find #"not a value"
                 (book-err '[(writ.defn/law k (= 2 2)) (writ.defn/proof pk k refl)
                             (writ.defn/law l (= pk pk)) (writ.defn/proof p l refl)]))))
  (testing "an alpha-variant law may be cited"
    (is (nil? (book-err '[(writ.defn/law k (forall [x Nat] (= (+ x 0) x)))
                          (writ.defn/proof pk k (fn [x] refl))
                          (writ.defn/law l (forall [y Nat] (= (+ y 0) y)))
                          (writ.defn/proof p l k)])))))

;; --- G105: match discipline, round 32 --------------------------------------

(def ^:private mb '(writ.defn/data Mb Nth (Jst writ.kind/Nat)))
(def ^:private mb2 '(writ.defn/data M2 Nn (J2 writ.kind/Nat writ.kind/Nat)))

(deftest match-scope-drops-shadowed-names
  ;; Bend: computed_match_split -- a let/loop/destructure rebinding a
  ;; matchable name makes it a computed value
  (doseq [body ['(let [x (inc 1)] (writ.defn/match x :- Mb (Nth 0) ((Jst v) v)))
                '(loop [x 7] (writ.defn/match x :- Mb (Nth 0) ((Jst v) v)))
                '(let [[x] [5]] (writ.defn/match x :- Mb (Nth 0) ((Jst v) v)))
                '(when-let [x (inc 1)] (writ.defn/match x :- Mb (Nth 0) ((Jst v) v)))]]
    (is (re-find #"must be a parameter or a pattern binder"
                 (book-err [mb (list 'writ.defn/defn 'g '[x :- Mb] ':- 'writ.kind/Nat body)])))))

(deftest pattern-binders-are-symbols
  (doseq [arm ['((J2 [_ v] w) v) '((J2 {:keys [v]} w) v)]]
    (is (re-find #"pattern binder.*symbol"
                 (book-err [mb2 (list 'writ.defn/defn 'g '[m :- M2] ':- 'writ.kind/Nat
                                      (list 'writ.defn/match 'm ':- 'M2 '(Nn 0) arm))]))))
  (testing "nested and literal patterns get a Writ message, not a host error"
    (doseq [arm ['((J2 (Jst v) w) v) '((J2 5 w) w) '(0 0)]]
      (let [m (book-err [mb mb2 (list 'writ.defn/defn 'g '[m :- M2] ':- 'writ.kind/Nat
                                      (list 'writ.defn/match 'm ':- 'M2 '(Nn 0) arm))])]
        (is (re-find #"^Writ: " m))))))

(deftest match-type-is-the-scrutinee-type
  (is (re-find #"has type Nat.*Mb"
               (book-err [mb '(writ.defn/defn g [a :- writ.kind/Nat] :- writ.kind/Nat
                                (writ.defn/match a :- Mb (Nth 0) ((Jst v) v)))])))
  (is (re-find #"has type Nat.*Mb"
               (book-err [mb mb2 '(writ.defn/defn g [m :- M2] :- writ.kind/Nat
                                   (writ.defn/match m :- M2
                                     (Nn 0)
                                     ((J2 a b) (writ.defn/match a :- Mb (Nth 0) ((Jst v) v)))))]))))

(deftest data-shapes-round-32
  (is (re-find #"constructor `Kk` is declared twice"
               (book-err '[(writ.defn/data Aa Kk (Kk Aa))])))
  (is (re-find #"needs 1 type argument"
               (book-err '[(writ.defn/data Bx [a] (Wb Bx))])))
  (is (re-find #"qualified|not a constructor"
               (book-err [mb '(writ.defn/defn g [m :- Mb] :- writ.kind/Nat
                                (writ.defn/match m :- Mb (foo/Nth 0) ((Jst v) v)))]))))

(deftest match-forms-bend-accepts
  (testing "a repeated _ in one pattern"
    (is (nil? (book-err [mb2 '(writ.defn/defn g [m :- M2] :- writ.kind/Nat
                                (writ.defn/match m :- M2 (Nn 0) ((J2 _ _) 1)))]))))
  (testing "a catch-all arm covers the rest (plus_binder_split)"
    (is (nil? (book-err [mb '(writ.defn/defn g [m :- Mb] :- writ.kind/Nat
                              (writ.defn/match m :- Mb ((Jst v) v) (_ 0)))])))
    (is (nil? (book-err [mb '(writ.defn/defn g [m :- Mb] :- writ.kind/Nat
                              (writ.defn/match m :- Mb ((Jst v) v) (other 0)))]))))
  (testing "an empty datatype is matched with no arms (empty_datatype)"
    (is (nil? (book-err '[(writ.defn/data Void)
                          (writ.defn/defn absurd [v :- Void] :- writ.kind/Nat
                            (writ.defn/match v :- Void))]))))
  (testing "field quantities (cop_field_match)"
    (is (nil? (book-err '[(writ.defn/data P (MkP ^:many writ.kind/Nat))
                          (writ.defn/defn g [p :- P] :- writ.kind/Nat
                            (writ.defn/match p :- P ((MkP a) (+ a a))))])))
    (is (re-find #"erased"
                 (book-err '[(writ.defn/data P (MkP ^:zero writ.kind/Nat))
                             (writ.defn/defn g [p :- P] :- writ.kind/Nat
                               (writ.defn/match p :- P ((MkP a) a)))])))))

(deftest data-values-are-taken-apart-by-match
  (doseq [body ['(let [[_ v] m] v) '(nth m 1) '(second m) '(first m)]]
    (is (re-find #"take it apart with `match`"
                 (book-err [mb (list 'writ.defn/defn 'f '[m :- Mb] ':- 'writ.kind/Nat body)])))))

;; --- G106: the book's own namespace is not a way around book order ---------

(deftest own-namespace-is-book-local
  (is (re-find #"defined later"
               (book-err '[(ns a) (defn f [x] (a/g x)) (defn g [x] (f x))])))
  (is (re-find #"defined later"
               (book-err '[(ns a (:require [a :refer [g]])) (defn f [x] (g x)) (defn g [x] (f x))])))
  (is (re-find #"defined later"
               (book-err '[(ns a (:require [a :as self])) (defn f [x] (self/g x)) (defn g [x] (f x))])))
  (is (nil? (book-err '[(ns a) (defn g [x] x) (defn f [x] (a/g x))]))))

;; --- G107: aliases and reflection do not escape the effect gate -----------

(deftest aliases-and-reflection-are-effects
  (is (re-find #"effect code"
               (book-err '[(ns a (:require [clojure.core :as c])) (defn f [x] (c/eval x))])))
  (doseq [call ['((resolve (quote eval)) x) '((ns-resolve *ns* (quote eval)) x)
                '((get (ns-publics (quote clojure.core)) (quote eval)) x)
                '((find-var (quote clojure.core/eval)) x)]]
    (is (re-find #"effect code" (err-msg (list 'defn 'f '[x] call))))))

;; --- G108: the public check-defn runs the w/defn pipeline -------------------

(deftest public-check-defn-reads-annotations
  (is (= {:ok true} (wc/check-defn '(writ.defn/defn add [x :- Nat, y :- Nat] :- Nat (+ x y)))))
  (is (re-find #"not a type" (try (wc/check-defn '(writ.defn/defn f [x :- Bogus] x)) nil
                                  (catch Throwable t (.getMessage t)))))
  (is (re-find #"not Data" (try (wc/check-defn '(writ.defn/defn f [^:many x :- (-> Nat Nat)] x)) nil
                                (catch Throwable t (.getMessage t))))))

;; --- G109: `:-` inside fn params ------------------------------------------

(deftest fn-params-take-annotations
  (is (nil? (book-err '[(def f (fn [x :- writ.kind/Nat] x)) (defn g [] (f 1))])))
  (is (nil? (book-err '[(writ.defn/defn g [] :- writ.kind/Nat ((fn [x :- writ.kind/Nat] x) 1))])))
  (is (re-find #"not a type" (book-err '[(def f (fn [x :- Bogus] x))])))
  (is (re-find #"expects Nat" (book-err '[(def f (fn [x :- writ.kind/Nat] x)) (defn g [] (f "s"))]))))

;; --- G110: type names resolve strictly ------------------------------------

(deftest type-names-are-strict
  (doseq [sig ['[x :- foo/Nat] '[x :- bogus/M] '[x :- x] '[y :- x, x :- writ.kind/Nat]
               '[x :- (Tuple)] '[x :- (->)]]]
    (is (re-find #"not a type|needs|takes|earlier"
                 (book-err [(list 'writ.defn/defn 'f sig 0)]))))
  (is (nil? (book-err '[(writ.defn/defn f [n :- writ.kind/Nat, v :- (writ.kind/List n)] 0)]))))

(deftest type-names-and-refers-are-not-code
  (is (re-find #"is a type"
               (book-err '[(writ.defn/data M Nothing (Just Int)) (defn f [] M)])))
  (is (re-find #"is a type"
               (book-err '[(writ.defn/data M Nothing (Just Int)) (defn f [] (M 1))])))
  (is (re-find #"already refers"
               (book-err '[(ns a (:require [other :refer [g]])) (defn g [x] x)]))))

;; --- G111: erased type variables (round 34) --------------------------------
;;
;; Generic code in Bend takes its type as an erased parameter; writ declares
;; type variables in the defn attr-map, {:writ/forall [a, b :- Data]}, so
;; they cost no runtime argument.  A variable is kind Type unless declared
;; Data (BendTT: under a generic quantity + is refused until instantiation).

(deftest erased-type-variables
  (is (nil? (book-err '[(writ.defn/defn id {:writ/forall [a]} [x :- a] :- a x)
                        (writ.defn/defn g [] :- writ.kind/Nat (id 5))
                        (writ.defn/defn h [] :- writ.kind/String (id "s"))])))
  (is (re-find #"not Data"
               (book-err '[(writ.defn/defn dup {:writ/forall [a]} [^:many x :- a] [x x])])))
  (is (nil? (book-err '[(writ.defn/defn dup {:writ/forall [a :- Data]} [^:many x :- a] [x x])])))
  (is (nil? (book-err '[(writ.defn/defn len {:writ/forall [a]} [xs :- (List a)] :- writ.kind/Nat
                          (count xs))])))
  (is (re-find #"not a type"
               (book-err '[(writ.defn/defn f [x :- a] x)]))))

;; --- G112: dead code runs in Clojure ---------------------------------------
;;
;; Bend erases dead code before the runtime, so an erased let init or an
;; argument to an erased parameter is free there.  Clojure evaluates both
;; eagerly, so writ keeps counting them: (let [^:zero y (f f)] 0) really
;; applies f to itself.

(deftest dead-code-still-runs
  (is (re-find #"used more than once"
               (err-msg '(defn g [x f] (let [^:zero y (f (f x))] 0)))))
  (is (re-find #"used more than once"
               (book-err '[(writ.defn/defn e [^:zero x :- writ.kind/Nat] :- writ.kind/Nat 0)
                           (writ.defn/defn dupl [a :- writ.kind/Nat] [(e a) a])]))))

;; --- G113: messages name binders as written -------------------------------

(deftest messages-use-programmer-names
  (let [m (err-msg '(defn f [x] (let [y (inc x)] (+ y y))))]
    (is (re-find #"`y` in `f`" m))
    (is (not (re-find #"y__\d" m)))))
