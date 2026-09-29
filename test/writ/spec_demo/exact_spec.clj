(ns writ.spec-demo.exact-spec
  "Laws that hold of every generated record, which carries only the keys
  the record names, but not of every record: a record is open, and a
  value may hold more keys.  No proof may claim them."
  (:require [writ.spec :refer [spec ann graph law]]))

(spec writ.spec-demo.member {:test false})

(ann join     [Nat String -> {:id Nat, :email String, :points Nat, :nick (Opt String)}])
(ann award    [{:id Nat, :email String, :points Nat, :nick (Opt String)} Nat -> {:id Nat, :email String, :points Nat, :nick (Opt String)}])
(ann nickname [{:id Nat, :email String, :points Nat, :nick (Opt String)} -> String])

(graph members {:states {:m {:id Nat, :email String, :points Nat, :nick (Opt String)}} :edges {}})

(law an-award-has-its-keys-and-no-more
  (forall [m {:id Nat, :email String, :points Nat, :nick (Opt String)}, n Nat] (<= 3 (count (award m n)) 4)))

(law an-award-is-its-keys
  (forall [m {:id Nat, :email String, :points Nat, :nick (Opt String)}, n Nat]
    (= (dissoc (award m n) :nick) {:id (:id m) :email (:email m) :points (+ n (:points m))})))
