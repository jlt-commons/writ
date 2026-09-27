(ns writ.spec-demo.verdict-spec
  (:require [writ.spec :refer [spec ann law graph refine calls]]))

(spec writ.spec-demo.verdict {:require :proved})

(ann restart? [Keyword Any -> Bool])
(ann keep-if [(Vec Nat) (-> Nat Bool) -> (Vec Nat)])
(ann payload [Any -> Any])
(ann with-reason [(Map Keyword Any) Any -> (Map Keyword Any)])
(ann reason-of [(Map Keyword Any) -> Any])
(ann count-tags [(List Any) -> Nat])
(ann tags [Any -> Nat])
(ann kind [Any -> Keyword])

(defn small? [n] (< n 10))

(refine Small [xs (Vec Nat)] (every? small? xs))

;; keep-if is handed the spec's own small?, since a fn cannot be generated;
;; the edge is marked tested, but the prover proves it, and the report says
;; the marker is stale
(graph keeping
  {:states {:all (Vec Nat), :small Small}
   :edges  {:all {[keep-if 'small?] #{:small}}}
   :tested {:all "a vector of unknown length is outside the prover"}})

;; proved over every value of any type, through a call into another namespace
(law permanent-always-restarts (forall [r Any] (restart? :permanent r)))
(law temporary-never-restarts (forall [r Any] (not (restart? :temporary r))))

;; a witness only the code's own literals lead to
(law some-exit-is-orderly (exists [r Any] (not (restart? :transient r))))

(law keep-if-keeps-the-small
  {:require :tested :because "filter by a fn argument is outside the prover"}
  (= (keep-if [1 20 3] small?) [1 3]))

(law transient-restarts-on-a-crash (restart? :transient :boom))

(law any-other-kind-restarts
  (forall [k Keyword, r Any]
    (=> (not (contains? #{:transient :temporary} k)) (restart? k r))))

;; the shell: a multi-arity fn, a qualified own fn, and a macro
(calls writ.spec-demo.verdict-shell/decide {:through [writ.spec-demo.verdict/restart?
                                                      writ.spec-demo.verdict-core/orderly?]})
(calls writ.spec-demo.verdict-shell/decide-all {:through [writ.spec-demo.verdict-shell/decide]})
(calls writ.spec-demo.verdict-shell/when-restart {:through [writ.spec-demo.verdict/restart?]})

;; a vector literal is known to be a vector, a list is known not to be
(law payload-of-an-ok-vector (forall [x Any] (= (payload [:ok x]) x)))
(law a-list-is-not-a-vector (forall [x Any] (= (payload (list :ok x)) :bad)))
(law anything-else-is-bad (forall [n Int] (= (payload n) :bad)))

;; maps: built, looked up and compared by their entries, whatever the order
(law a-reason-is-set (forall [r Any] (= (reason-of (with-reason {:x 1} r)) r)))
(law setting-a-reason-replaces-it (forall [r Any] (= (with-reason {:reason 1} r) {:reason r})))
(law map-equality-ignores-order (forall [a Any, b Any] (= (with-reason {:x a} b) {:reason b :x a})))
(law no-reason-is-none (= (reason-of {}) :none))

;; a recursion a literal drives is unrolled
(law no-tags-in-nothing (= (count-tags []) 0))
(law tags-of-a-known-vector
  (forall [a Any, b Any] (= (count-tags [:t a b]) (+ 1 (count-tags [a b])))))

;; the vector branch gives up on an opaque value, but the hypothesis rules it out
(law no-tags-outside-a-vector (forall [x Any] (=> (not (vector? x)) (= 0 (tags x)))))

;; a constant's kind is known
(law a-symbol-is-a-symbol (forall [s Symbol] (= :sym (kind s))))
(law any-keyword-is-a-keyword (forall [x Any] (=> (keyword? x) (= :kw (kind x)))))
