(ns writ.spec-demo.registry-spec
  "A collection of records keyed by id, with a rule across all of them:
  no two members share an email."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.registry)

(refine Member [m {:id Nat, :email String}] true)
(refine Db [db (Index :id Member :unique [:email])] true)

(ann taken?   [Db Member -> Bool])
(ann register [Db Member -> Db])

(graph registry
  {:start  [:db {}]
   :states {:db Db}
   :edges  {:db {[register Member] #{:db}}}
   :final  [:db]
   :runs   20})

(law a-free-member-is-registered
  (forall [db Db, m Member]
    (=> (not (taken? db m)) (= m (get (register db m) (:id m))))))

(law a-taken-member-is-refused
  (forall [db Db, m Member]
    (=> (taken? db m) (= db (register db m)))))

(law an-email-in-use-is-taken
  (forall [db Db, m Member, n Nat]
    (=> (seq db) (taken? db (assoc m :email (:email (first (vals db))))))))

(law a-fresh-id-and-email-are-free
  (forall [db Db, m Member]
    (=> (and (not (contains? db (:id m)))
             (not-any? #(= (:email m) (:email %)) (vals db)))
        (not (taken? db m)))))
