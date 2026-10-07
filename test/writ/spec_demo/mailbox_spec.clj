(ns writ.spec-demo.mailbox-spec
  "A scan over a mailbox: laws proved by induction on the scan's index,
  each step opening clause-of on the message at that index."
  (:require [writ.spec :refer [spec data ann law graph refine]]))

(spec writ.spec-demo.mailbox {:require :proved})

(data Hit (Hit Nat (Map Keyword Any)) (Miss))
(data Scan (Take Nat Nat (Map Keyword Any)) (None Nat))

(ann clause-of [(Vec Any) (-> Nat (Map Keyword Any) Bool) Any -> Hit])
(ann scan [(Vec Any) (Vec Any) (-> Nat (Map Keyword Any) Bool) Nat -> Scan])

(defn yes [_ _] true)

(refine Taken  [r Scan] (= :Take (first r)))
(refine Missed [r Scan] (= :None (first r)))

(graph receive
  {:states {:mailbox (Vec Any), :taken Taken, :missed Missed}
   :edges  {:mailbox {[scan (Vec Any) 'yes Nat] #{:taken :missed}}}})

;; no clauses: clause-of opens on its empty clause list, whatever the message
(law nothing-matches
  (forall [msgs (Vec Any), start Nat]
    (= (scan msgs [] yes start) [:None (max start (count msgs))])))

(law a-take-is-a-clause-taking-a-message
  (forall [msgs (Vec Any), pats (Vec Any), start Nat]
    (=> (= :Take (first (scan msgs pats yes start)))
        (let [i (second (scan msgs pats yes start))]
          (and (<= start i) (< i (count msgs))
               (= :Hit (first (clause-of pats yes (nth msgs i)))))))))

(law a-scan-that-takes-nothing-stops-at-the-end
  (forall [msgs (Vec Any), pats (Vec Any), start Nat]
    (=> (= :None (first (scan msgs pats yes start)))
        (= (second (scan msgs pats yes start)) (max start (count msgs))))))

