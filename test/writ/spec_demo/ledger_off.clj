(ns writ.spec-demo.ledger-off
  "The ledger, wrong: a deposit to an account it does not hold opens it,
  and a close leaves the account in place when it has money.")

(defn deposit [l a n]
  (update-in l [:accts a] (fn [x] {:id a :balance (+ n (:balance x 0))})))

(defn open-acct [l a]
  (if (contains? (:accts l) a)
    l
    (assoc-in l [:accts a] {:id a :balance 0})))

(defn close-acct [l a]
  (if (pos? (get-in l [:accts a :balance] 0))
    l
    (update l :accts dissoc a)))

(defn tag [l k v]
  (assoc-in l [:tags k] v))

(defn balance [l a]
  (get-in l [:accts a :balance] 0))
