(ns writ.spec-demo.bank-overlap-spec
  "A step with two cases, each under its own guard: a withdrawal the
  balance covers pays out and changes only the balance; one it does not
  overdraws the account and changes only the status and the fee. The
  cases must not overlap: here they do, at a withdrawal of exactly the
  balance."
  (:require [writ.spec :refer [spec ann refine graph]]))

(spec writ.spec-demo.bank {:test false})

(refine Status [s Keyword] (contains? #{:open :overdrawn} s))
(refine Account [a {:status Status, :balance Nat, :fee Nat}] true)
(refine Open [a Account] (and (= :open (:status a)) (zero? (:fee a))))
(refine Overdrawn [a Account] (and (= :overdrawn (:status a)) (pos? (:fee a))))

(ann withdraw [Account Nat -> Account])

(defn covered? [a amt] (<= amt (:balance a)))
(defn short? [a amt] (<= (:balance a) amt))

(graph bank
  {:states {:open Open, :overdrawn Overdrawn}
   :edges  {:open {[withdraw Nat] [{:to #{:open} :when covered? :changes [:balance]}
                                   {:to #{:overdrawn} :when short? :changes [:status :fee]}]}}
   :final  [:overdrawn]})
