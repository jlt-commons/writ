(ns writ.spec-demo.links
  "A link store: adding a url hands back the grown store and the url's code.")

(defn add [links url]
  (let [code (str (count links))]
    [(assoc links code url) code]))
