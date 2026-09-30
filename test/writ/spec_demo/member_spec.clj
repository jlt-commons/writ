(ns writ.spec-demo.member-spec
  "A member is a map with named keys, typed per key; :nick may be absent."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.member)

(refine Member [m {:id Nat, :email String, :points Nat, :nick (Opt String)}] true)
(refine Fresh  [m Member] (zero? (:points m)))
(refine Active [m Member] (pos? (:points m)))
(refine Pos    [n Nat] (pos? n))

(ann join     [Nat String -> Member])
(ann award    [Member Nat -> Member])
(ann nickname [Member -> String])

(graph membership
  {:states {:fresh Fresh, :active Active}
   :edges  {:fresh  {[award Pos] #{:active}}
            :active {[award Nat] #{:active}}}})

(law join-starts-fresh
  (forall [id Nat, e String] (Fresh? (join id e))))

(law join-keeps-who
  (forall [id Nat, e String] (and (= id (:id (join id e))) (= e (:email (join id e))))))

(law award-adds
  (forall [m Member, n Nat] (= (:points (award m n)) (+ (:points m) n))))

(law award-touches-only-points
  (forall [m Member, n Nat] (= (dissoc (award m n) :points) (dissoc m :points))))

(law the-nick-when-set
  (forall [m Member, s String] (= s (nickname (assoc m :nick s)))))

(law the-email-otherwise
  (forall [m Member] (= (:email m) (nickname (dissoc m :nick)))))
