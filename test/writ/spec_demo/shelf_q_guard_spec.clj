(ns writ.spec-demo.shelf-q-guard-spec
  "The guard of lend named once, lendable?, and used by the graph's edge
  and by the law alike."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.shelf-q {:test false})

(refine Status [s Keyword] (contains? #{:shelf :loaned} s))
(refine Copy [c {:id Nat, :status Status, :holder (Opt Nat)}] true)
(refine Member [m {:id Nat, :loans Nat}] true)

(defn lent-to [l m] (count (filter #(and (= :loaned (:status %)) (= m (:holder %))) (vals (:copies l)))))
(defn counted? [l] (every? (fn [m] (= (:loans m) (lent-to l (:id m)))) (vals (:members l))))
(defn shelved-free? [l] (every? (fn [c] (or (= :loaned (:status c)) (nil? (:holder c)))) (vals (:copies l))))
(defn consistent? [l] (and (shelved-free? l) (counted? l)))

(defn settle [l]
  (let [cs (into {} (for [[k c] (:copies l)]
                      [k (if (and (= :loaned (:status c)) (contains? (:members l) (:holder c)))
                           c (assoc c :status :shelf :holder nil))]))
        l (assoc l :copies cs)]
    (assoc l :members (into {} (for [[k m] (:members l)] [k (assoc m :loans (lent-to l k))])))))

(refine Lib [l {:copies (Index :id Copy), :members (Index :id Member)}] (consistent? l) {:build settle})

(ann lend [Lib Nat Nat -> Lib])

(defn lendable? [l m c] (and (contains? (:members l) m) (= :shelf (get-in l [:copies c :status]))))

(graph desk {:states {:lib Lib} :edges {:lib {[lend Nat Nat] {:to #{:lib} :when lendable?}}}})

(law lending-marks-the-copy
  (forall [l Lib, m Nat, c Nat]
    (=> (lendable? l m c)
        (= m (get-in (lend l m c) [:copies c :holder])))))
