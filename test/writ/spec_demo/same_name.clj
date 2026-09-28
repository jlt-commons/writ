(ns writ.spec-demo.same-name
  "A shell with a fn of the same name as the core fn it calls."
  (:require [writ.spec-demo.pipeline :as p]))

(defn handle
  "This namespace's handle, which calls the pipeline's."
  [req]
  (p/handle req))

(defn respond-twice [req] [(p/respond req) (handle req)])
