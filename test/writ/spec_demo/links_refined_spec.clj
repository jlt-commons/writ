(ns writ.spec-demo.links-refined-spec
  "The loop of links-spec, its store a refinement: no empty url. What
  `add` returns is judged where the [first] edge takes the store back
  out, so an add of an empty url is caught."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.links {:test false})

(refine Links [m (Map String String)] (every? #(not= "" %) (vals m)))

(ann add [(Map String String) String -> (Tuple (Map String String) String)])

(graph store
  {:states {:links Links, :added (Tuple (Map String String) String)}
   :edges  {:links {[add String] #{:added}}
            :added {[first] #{:links}}}})

(law add-keeps-the-url
  (forall [links (Map String String), url String]
    (let [[links2 code] (add links url)] (= url (get links2 code)))))
