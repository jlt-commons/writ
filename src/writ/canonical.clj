(ns writ.canonical
  "Deterministic, injective, sharing-aware encoding for proof evidence."
  (:require [writ.hash :as hash]))

(defn- tagged [tag value]
  [::tag tag value])

(defn- string-data [s]
  (tagged :string
          (vec (mapcat (fn [codepoint]
                         (if (> codepoint 0xFFFF)
                           (let [x (- codepoint 0x10000)]
                             [(+ 0xD800 (quot x 0x400))
                              (+ 0xDC00 (mod x 0x400))])
                           [codepoint]))
                       (map int s)))))

(defn- leaf [value]
  (cond
    (nil? value) (tagged :nil nil)
    (true? value) (tagged :boolean true)
    (false? value) (tagged :boolean false)
    (string? value) (string-data value)
    (keyword? value) (tagged :keyword [(some-> (namespace value) string-data)
                                      (string-data (name value))])
    (symbol? value) (tagged :symbol [(some-> (namespace value) string-data)
                                    (string-data (name value))])
    (char? value) (tagged :char (int value))
    (ratio? value) (tagged :ratio [(str (numerator value)) (str (denominator value))])
    (integer? value) (tagged :integer (str value))
    (= Float (class value)) (tagged :float32 (Float/floatToIntBits value))
    (= Double (class value)) (tagged :float64 (Double/doubleToLongBits value))
    :else (throw (ex-info "Unsupported value in canonical proof encoding"
                          {:value value :class (some-> value class str)}))))

(defn canonical [value]
  (let [memo (java.util.IdentityHashMap.)
        nodes (atom {})]
    (letfn [(walk [v]
              (or (.get memo v)
                  (if (coll? v)
                    (let [encoded (cond
                                    (vector? v) (tagged :vector (mapv walk v))
                                    (seq? v) (tagged :list (mapv walk v))
                                    (set? v) (tagged :set (vec (sort-by pr-str (map walk v))))
                                    (map? v) (tagged :map (vec (sort-by pr-str
                                                                  (map (fn [[k x]] [(walk k) (walk x)]) v))))
                                    :else (leaf v))
                          id (hash/sha256 (pr-str encoded))
                          reference (tagged :reference id)]
                      (swap! nodes assoc id encoded)
                      (.put memo v reference)
                      reference)
                    (let [encoded (leaf v)]
                      (.put memo v encoded)
                      encoded))))]
      {:root (walk value)
       :nodes (into (sorted-map) @nodes)})))

(defn encode [value]
  (pr-str (canonical value)))

(defn content-id [value]
  (hash/sha256 (encode value)))
