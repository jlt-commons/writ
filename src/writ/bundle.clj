(ns writ.bundle
  "Self-contained, replay-only Writ proof evidence."
  (:require [clojure.edn :as edn]
            [writ.canonical :as canonical]
            [writ.proposition :as proposition]
            [writ.prove :as prover]))

(def schema-version 1)

(defn artifact [evidence]
  (let [value (-> evidence
                  (select-keys [:spec :target :sources :context :contracts :dependencies
                                :laws :assumptions :runtime-evidence])
                  (assoc :writ.bundle/schema-version schema-version))]
    (assoc value :id (canonical/content-id value))))

(defn- failure [error detail]
  {:ok false :error error :detail detail})

(defn- verify-contracts [bundle]
  (let [evidence (:contracts bundle)
        inputs (merge (select-keys (:context bundle) [:defs :tenv :sigs])
                      (select-keys evidence [:traces]))
        result (prover/prove-contracts (assoc inputs :replay-only true))
        expected (set (keys (:traces evidence)))
        actual (set (keys (:traces result)))
        assumed-rules (prover/contract-rules (get-in bundle [:context :tenv])
                                             (get-in bundle [:assumptions :sigs]))]
    (if (or (seq (:replay-errors result)) (not= expected actual))
      (failure :contracts-rejected {:expected expected :actual actual
                                    :errors (:replay-errors result)})
      {:ok true :rules (into (:rules result) assumed-rules)
       :count (count (:rules result))})))

(defn- lemmas-allowed? [allowed lemmas]
  (every? (fn [{:keys [name prop]}]
            (when-let [earlier (get allowed name)]
              (= prop (:prop earlier))))
          lemmas))

(defn- law-entry? [entry]
  (and (map? entry)
       (symbol? (:law entry))
       (case (:kind entry)
         :proof (and (map? (:args entry)) (some? (:trace entry)))
         :alias (and (some? (:of entry)) (some? (:prop entry)))
         false)
       (vector? (:assumptions-used entry))))

(defn- valid-bundle? [bundle]
  (and (map? bundle)
       (= schema-version (:writ.bundle/schema-version bundle))
       (string? (:id bundle))
       (symbol? (:spec bundle))
       (symbol? (:target bundle))
       (map? (:context bundle))
       (every? #(map? (get-in bundle [:context %])) [:defs :tenv :own :sigs])
       (map? (:contracts bundle))
       (map? (get-in bundle [:contracts :traces]))
       (vector? (:dependencies bundle))
       (every? map? (:dependencies bundle))
       (vector? (:laws bundle))
       (every? law-entry? (:laws bundle))
       (= (count (:laws bundle)) (count (distinct (map :law (:laws bundle)))))
       (map? (:assumptions bundle))
       (map? (get-in bundle [:assumptions :sigs]))
       (vector? (get-in bundle [:assumptions :lemmas]))
       (every? #(and (map? %) (symbol? (:name %)) (some? (:prop %)))
               (get-in bundle [:assumptions :lemmas]))
       (or (nil? (:sources bundle)) (map? (:sources bundle)))
       (or (nil? (:runtime-evidence bundle)) (vector? (:runtime-evidence bundle)))))

(declare verify*)

(defn- verify-law [state entry]
  (let [{:keys [verified rules context]} state]
    (case (:kind entry)
      :alias
      (let [earlier (get verified (:of entry))]
        (cond
          (not (and earlier (proposition/alpha= (:prop entry) (:prop earlier))))
          (failure :alias-rejected {:law (:law entry) :of (:of entry)})

          (not= (set (:assumptions-used entry)) (set (:assumptions-used earlier)))
          (failure :assumptions-mismatch
                   {:law (:law entry)
                    :expected (:assumptions-used entry)
                    :actual (:assumptions-used earlier)})

          :else
          (assoc state :verified
                 (assoc verified (:law entry)
                        {:name (:law entry) :prop (:prop entry)
                         :assumptions-used (:assumptions-used earlier)}))))

      :proof
      (let [args (merge context (:args entry))
            lemmas (:lemmas args)]
        (if-not (lemmas-allowed? verified lemmas)
          (failure :unknown-lemma {:law (:law entry) :lemmas (mapv :name lemmas)})
          (let [result (prover/prove-law
                        (assoc args :contracts rules :replay (:trace entry)
                               :replay-only true :refutes? nil))
                assumptions (vec (sort (into (set (:assumptions-used result))
                                             (mapcat :assumptions-used
                                                     (keep verified (:lemmas result))))))]
            (cond
              (not (and (:proved result) (:replayed result)))
              (failure :law-rejected {:law (:law entry) :result result})

              (not= (set (:assumptions-used entry)) (set assumptions))
              (failure :assumptions-mismatch
                   {:law (:law entry)
                    :expected (:assumptions-used entry)
                    :actual assumptions})

              :else
              (-> state
                  (update :laws conj {:law (:law entry) :status :replayed})
                  (assoc :verified
                         (assoc verified (:law entry)
                                {:name (:law entry) :prop (:prop args)
                                 :assumptions-used assumptions})))))))

      (failure :unknown-law-kind {:law (:law entry) :kind (:kind entry)}))))

(defn- verify* [bundle]
  (if-not (and (valid-bundle? bundle)
               (= (:id bundle) (canonical/content-id (dissoc bundle :id))))
    (failure :invalid-bundle
             {:schema (:writ.bundle/schema-version bundle)
              :expected-id (canonical/content-id (dissoc bundle :id))
              :actual-id (:id bundle)})
    (let [dependencies (reduce (fn [state dependency]
                                 (let [result (verify* dependency)]
                                   (if-not (:ok result)
                                     (reduced result)
                                     (-> state
                                         (update :dependency-results conj result)
                                         (update :verified merge
                                                 (into {}
                                                       (map (fn [[name lemma]]
                                                              [(if (namespace name)
                                                                 name
                                                                 (symbol (str (:spec dependency)) (str name)))
                                                               lemma]))
                                                       (:verified result)))))))
                               {:ok true :dependency-results [] :verified {}}
                               (:dependencies bundle))
          assumptions (reduce (fn [m {:keys [name prop]}]
                                  (assoc m name {:name name :prop prop :assumption true
                                                 :assumptions-used
                                                 [(str "assume." (:spec bundle) "/" name)]}))
                              {}
                              (get-in bundle [:assumptions :lemmas]))
          context (assoc (:context bundle)
                         :spec-ns (:spec bundle)
                         :assumption-contracts
                         (into {}
                               (for [[q sig] (get-in bundle [:assumptions :sigs])
                                     r (prover/contract-rules (get-in bundle [:context :tenv]) {q sig})]
                                 [(:name r) q]))
                         :assumption-lemmas
                         (set (map :name (get-in bundle [:assumptions :lemmas]))))]
      (if-not (:ok dependencies)
        dependencies
        (let [contracts (verify-contracts bundle)]
          (if-not (:ok contracts)
            contracts
            (let [initial {:ok true :laws []
                           :verified (into (:verified dependencies) assumptions)
                           :rules (:rules contracts)
                           :context context}
                  result (reduce (fn [state entry]
                                   (if-not (:ok state)
                                     (reduced state)
                                     (verify-law state entry)))
                                 initial (:laws bundle))]
              (if (:ok result)
                (assoc result :contracts (:count contracts)
                       :assumptions (:assumptions bundle))
                result))))))))

(defn verify [path-or-bundle]
  (try
    (let [bundle (if (map? path-or-bundle)
                   path-or-bundle
                   (edn/read-string (slurp path-or-bundle)))
          result (verify* bundle)]
      (dissoc result :verified :rules :dependency-results))
    (catch Throwable e
      (failure :verification-error {:message (ex-message e)}))))
