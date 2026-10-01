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

(graph books {:states {:l Ledger}
              :edges {:l {[deposit Nat Int] #{:l} [open-acct Nat] #{:l}
                          [close-acct Nat] #{:l} [tag Keyword Nat] #{:l}}}})

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
