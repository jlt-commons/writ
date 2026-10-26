(ns writ.reuse
  "Deterministic, assumption-aware retrieval of already proved lemmas.
   Retrieval is untrusted: every candidate still needs a checked proof."
  (:require [writ.prove.rewrite :as rw]
            [writ.prove.scheme :as sc]
            [writ.prove.term :as t]
            [writ.prove.translate :as tr]))

(defn- normalized [prop {:keys [defs tenv own]}]
  (let [[bs body] (sc/split-foralls prop)
        ren (into {} (map-indexed (fn [i [x _]] [x (symbol (str "?reuse" i))]) bs))
        vars (mapv first bs)
        goal (sc/goal (tr/context (or own {})) vars body)
        types (into {} (map (fn [[x ty]] [(ren x) ty]) bs))
        ctx (rw/context {:defs (or defs {}) :tenv (or tenv {}) :types types})
        normalize #(rw/normalize ctx (t/subst % ren))]
    {:bindings (mapv second bs)
     :hyps (mapv normalize (:hyps goal))
     :goals (mapv normalize (:goals goal))}))

(defn index [lemmas context]
  (let [classified (mapv (fn [lemma]
                           (when-not (contains? #{:tested :unproved :failed :vacuous}
                                                (:status lemma))
                             (try
                               {:entry (assoc lemma :reuse/normalized (normalized (:prop lemma) context)
                                              :assumptions-used (vec (:assumptions-used lemma)))}
                               (catch Throwable e
                                 {:quarantined {:name (:name lemma)
                                                :reason :normalization-failed
                                                :message (or (ex-message e) (str (class e)))}}))))
                         lemmas)
        entries (keep :entry classified)
        quarantined (keep :quarantined classified)]
    {:context context
     :entries (vec (sort-by #(str (:name %)) entries))
     :quarantined (vec (sort-by #(str (:name %)) quarantined))}))

(defn- dependencies [normalized]
  (into #{}
        (comp (mapcat #(t/subterms %))
              (keep (fn [term]
                      (when (and (vector? term) (contains? #{:app :call} (first term)))
                        (second term)))))
        (concat (:hyps normalized) (:goals normalized))))

(defn candidates
  ([index prop] (candidates index prop {}))
  ([index prop {:keys [allowed-assumptions limit] :or {limit 16}}]
   (let [allowed (or allowed-assumptions #{})
         target (try (normalized prop (:context index)) (catch Throwable _ nil))
         target-deps (dependencies target)
         eligible (fn [entry]
                    (every? allowed (:assumptions-used entry)))
         scored (into []
                      (comp (filter eligible)
                            (map (fn [entry]
                                   (let [exact (= target (:reuse/normalized entry))
                                         overlap (count (into #{}
                                                              (filter (dependencies (:reuse/normalized entry)))
                                                              target-deps))]
                                     (assoc entry :reuse/exact exact :reuse/score overlap))))
                            (filter #(or (:reuse/exact %) (pos? (:reuse/score %)))))
                      (:entries index))]
     (vec (take limit
                (sort-by (fn [entry]
                           [(if (:reuse/exact entry) 0 1)
                            (- (:reuse/score entry))
                            (count (:assumptions-used entry))
                            (str (:name entry))])
                         scored))))))
