(ns writ.spec-demo.verdict-spec
  (:require [writ.spec :refer [spec ann law graph refine calls]]))

(spec writ.spec-demo.verdict {:require :proved})

(ann restart? [Keyword Any -> Bool])
(ann keep-if [(Vec Nat) (-> Nat Bool) -> (Vec Nat)])
(ann payload [Any -> Any])

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
