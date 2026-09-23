(ns shortener.store
  "Where the links live between requests: an atom. Effects only; the
  logic is shortener.core.")

(def links (atom {}))

(defn transact!
  "Run pure `f` from links to [links reply] against the store, and return
  the reply. `f` is pure, so running it again on the links it was given
  reproduces the reply that swap! committed."
  [f]
  (let [[old _] (swap-vals! links #(first (f %)))]
    (second (f old))))

(defn remember! [code url]
  (swap! links assoc code url))
