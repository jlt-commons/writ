(ns writ.spec-demo.ledger
  "Accounts by id, and tags: maps of any size.")

(defn deposit [l a n]
  (if (contains? (:accts l) a)
    (update-in l [:accts a :balance] + n)
    l))

(defn open-acct [l a]
  (if (contains? (:accts l) a)
    l
    (assoc-in l [:accts a] {:id a :balance 0})))

(defn close-acct [l a]
  (update l :accts dissoc a))

(defn tag [l k v]
  (assoc-in l [:tags k] v))

(defn balance [l a]
  (get-in l [:accts a :balance] 0))
