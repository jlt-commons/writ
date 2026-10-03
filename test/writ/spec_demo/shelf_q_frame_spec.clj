(ns writ.spec-demo.shelf-q-frame-spec
  "lend touches only the copy it lends and the member it lends to: a frame
  of paths named by the step's own arguments, (arg 1) the member and
  (arg 2) the copy."
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

(graph desk {:states {:lib Lib}
             :edges {:lib {[lend Nat Nat] {:to #{:lib} :changes [[:copies (arg 2)] [:members (arg 1)]]}}}})

(law lending-marks-the-copy
  (forall [l Lib, m Nat, c Nat]
    (=> (and (contains? (:members l) m) (= :shelf (get-in l [:copies c :status])))
        (= m (get-in (lend l m c) [:copies c :holder])))))
