(ns writ.spec-demo.shell
  "An effect shell over the pipeline: it prints, so writ does not check
  its code, but a spec can still say how it is wired."
  (:require [writ.spec-demo.pipeline :as p]))

(defn- show [r] (println (pr-str r)) r)

(defn serve [line]
  (show (p/handle line)))

(defn serve-raw [line]
  (show (p/respond line)))
