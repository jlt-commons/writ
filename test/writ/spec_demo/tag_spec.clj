(ns writ.spec-demo.tag-spec
  "Contracts whose own names are those of core fns and target fns: each
  name means what the contract's fn binds it to."
  (:require [writ.spec :refer [spec ann graph law]]))

(spec writ.spec-demo.tag)

(ann label [Keyword -> String] {:ensures (fn [k r] (= k (keyword r)))})
(ann total [(List Nat) -> Nat])
(ann add-item [(List Nat) Nat -> (List Nat)]
  {:ensures (fn [items x total] (= (count total) (inc (count items))))})

(graph tagging
  {:states {:k Keyword, :s String, :items (List Nat), :n Nat}
   :edges  {:k {[label] #{:s}}
            :items {[total] #{:n}, [add-item Nat] #{:items}}}})

(law total-counts (forall [xs (List Nat)] (= (count xs) (total xs))))
(law added-last (forall [xs (List Nat), x Nat] (= x (last (add-item xs x)))))
