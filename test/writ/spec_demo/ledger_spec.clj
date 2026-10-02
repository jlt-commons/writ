(ns writ.spec-demo.ledger-spec
  "Laws over maps of any size: an index of accounts and a map of tags. The
  prover reads such a map as a lookup the solver may choose, overwritten
  where the code assocs and dissocs."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.ledger)

(defn kept-by-id? [l] (every? (fn [[k x]] (= k (:id x))) (:accts l)))

(refine Ledger [l {:accts (Index :id {:id Nat, :balance Int}), :tags (Map Keyword Nat)}] (kept-by-id? l))

(ann deposit    [Ledger Nat Int -> Ledger])
(ann open-acct  [Ledger Nat -> Ledger])
(ann close-acct [Ledger Nat -> Ledger])
(ann tag        [Ledger Keyword Nat -> Ledger])
(ann balance    [Ledger Nat -> Int])
(ann withdraw   [Ledger Nat Int -> Ledger])

(defn solvent? [l] (every? (fn [x] (<= 0 (:balance x))) (vals (:accts l))))

(graph books {:states {:l Ledger}
              :edges {:l {[deposit Nat Int] #{:l} [open-acct Nat] #{:l}
                          [close-acct Nat] #{:l} [tag Keyword Nat] #{:l}
                          [withdraw Nat Int] #{:l}}}})

(law a-deposit-adds-to-the-balance
  (forall [l Ledger, a Nat, n Int]
    (=> (contains? (:accts l) a)
        (= (+ n (balance l a)) (balance (deposit l a n) a)))))

(law a-deposit-touches-only-that-account
  (forall [l Ledger, a Nat, n Int]
    (= (dissoc (:accts (deposit l a n)) a) (dissoc (:accts l) a))))

(law a-deposit-to-no-account-changes-nothing
  (forall [l Ledger, a Nat, n Int]
    (=> (not (contains? (:accts l) a)) (= l (deposit l a n)))))

(law an-opened-account-starts-empty
  (forall [l Ledger, a Nat]
    (=> (not (contains? (:accts l) a))
        (= {:id a :balance 0} (get (:accts (open-acct l a)) a)))))

(law opening-an-open-account-changes-nothing
  (forall [l Ledger, a Nat]
    (=> (contains? (:accts l) a) (= l (open-acct l a)))))

(law a-closed-account-is-gone
  (forall [l Ledger, a Nat]
    (not (contains? (:accts (close-acct l a)) a))))

(law closing-leaves-the-others
  (forall [l Ledger, a Nat, b Nat]
    (=> (not= a b) (= (get (:accts (close-acct l a)) b) (get (:accts l) b)))))

(law a-tag-reads-back
  (forall [l Ledger, k Keyword, v Nat]
    (= v (get (:tags (tag l k v)) k))))

(law a-deposit-keeps-the-account-under-its-id
  (forall [l Ledger, a Nat, n Int]
    (=> (contains? (:accts l) a) (= a (:id (get (:accts (deposit l a n)) a))))))

(law a-balance-is-the-accounts
  (forall [l Ledger, a Nat]
    (=> (contains? (:accts l) a) (= (:balance (get (:accts l) a)) (balance l a)))))

(law no-account-has-no-balance
  (forall [l Ledger, a Nat]
    (=> (not (contains? (:accts l) a)) (= 0 (balance l a)))))

(law a-withdrawal-keeps-every-balance-whole
  (forall [l Ledger, a Nat, n Int]
    (=> (solvent? l) (solvent? (withdraw l a n)))))

(law a-withdrawal-takes-from-the-balance
  (forall [l Ledger, a Nat, n Int]
    (=> (and (contains? (:accts l) a) (<= 0 n (balance l a)))
        (= (- (balance l a) n) (balance (withdraw l a n) a)))))

(law an-overdraft-changes-nothing
  (forall [l Ledger, a Nat, n Int]
    (=> (< (balance l a) n) (= l (withdraw l a n)))))

(law opening-adds-one-account
  (forall [l Ledger, a Nat]
    (=> (not (contains? (:accts l) a))
        (= (inc (count (:accts l))) (count (:accts (open-acct l a)))))))

(law closing-takes-one-account-away
  (forall [l Ledger, a Nat]
    (=> (contains? (:accts l) a)
        (= (dec (count (:accts l))) (count (:accts (close-acct l a)))))))

(law a-deposit-keeps-the-count-of-accounts-in-credit
  (forall [l Ledger, a Nat, n Nat]
    (=> (and (contains? (:accts l) a) (pos? (balance l a)))
        (= (count (filter #(pos? (:balance %)) (vals (:accts l))))
           (count (filter #(pos? (:balance %)) (vals (:accts (deposit l a n)))))))))

(law a-deposit-adds-to-the-total
  (forall [l Ledger, a Nat, n Int]
    (=> (contains? (:accts l) a)
        (= (+ n (reduce + 0 (map :balance (vals (:accts l)))))
           (reduce + 0 (map :balance (vals (:accts (deposit l a n)))))))))
