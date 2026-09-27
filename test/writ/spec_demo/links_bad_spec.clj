(ns writ.spec-demo.links-bad-spec
  "The store goes around a loop: `add` returns the store with a code, and
  the store is taken back out of that result for the next add."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.links)

(ann add [(Map String String) String -> (Tuple (Map String String) String)])

(graph store
  {:start  [:links {}]
   :states {:links (Map String String), :added (Tuple (Map String String) String)}
   :edges  {:links {[add String] #{:added}}
            :added {[second] #{:links}}}})

(law add-keeps-the-url
  (forall [links (Map String String), url String]
    (let [[links2 code] (add links url)] (= url (get links2 code)))))

(law add-grows-the-store-by-one
  (forall [links (Map String String), url String]
    (=> (not (contains? links (str (count links))))
        (= (inc (count links)) (count (first (add links url)))))))
