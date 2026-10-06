(ns writ.bench
  "A benchmark of the prover over a corpus of specs: which laws it proves,
  by which strategy, and at what cost in rewrites and time.

  Prover changes are judged against it, the way a metric over a dataset
  judges a program: `run` checks each spec with the proof cache off and
  :explain on, and makes one row per law the prover tried; `summary`
  aggregates them; `compare` lists the laws a change gained, lost, sped
  up or slowed down against a saved baseline.  A bench never writes the
  proof cache and never changes a check's results.

  From a shell, in a project whose :bench alias runs this namespace:

      jolt -M:bench test/writ/spec_demo            every *_spec.clj there
      jolt -M:bench my.app-spec other.spec         named spec namespaces
      jolt -M:bench --save bench/baseline.edn DIR  save the rows
      jolt -M:bench --baseline bench/baseline.edn DIR
      jolt -M:bench --tune '[{:depth 6} {:fuel 10000}]' DIR --held-out DIR2
                                                   compare configs of the prover
      jolt -M:bench --jobs 1 DIR                   one spec at a time (the default
                                                   is one a processor)"
  (:refer-clojure :exclude [compare])
  (:require [clojure.string :as str]
            [jolt.fs :as fs]
            [writ.spec :as spec]))

(defn- attempt-name [a] (pr-str (:name a)))

(defn- row
  "One row for law result l of spec s."
  [s l]
  (let [as (:attempts l)
        win (first (filter #(= :proved (:outcome %)) as))]
    {:spec s :law (:law l) :status (:status l)
     :proved? (= :proved (:status l))
     :winner (some-> win attempt-name)
     :by (let [n (:name win)] (if (vector? n) (first n) n))
     :fuel (reduce + 0 (keep :fuel as))
     :ms (reduce + 0 (keep :ms as))
     :test-ms (or (:test-ms l) 0)
     :attempts (mapv #(select-keys % [:name :outcome :fuel :ms]) as)}))

(defn- spec-rows
  "The rows of one spec's check: opts over :seed 1, :adequacy false, and
  :cache false, :explain true."
  [s opts]
  (let [r (spec/check s (merge {:seed 1 :adequacy false} opts {:cache false :explain true}))]
    (vec (for [l (concat (:lemmas r) (:laws r))
               :when (seq (:attempts l))]
           (row s (cond-> l (:lemma l) (assoc :law (:lemma l))))))))

(defn- touched
  "The namespaces a check of spec s may rebind fns of, or whose fns it
  runs while another check may have them rebound: its target, those its
  target's code calls, the namespaces its calls, flows and signatures name, and those
  of the specs it uses, transitively, and those of the fns it assumes,
  which are wrapped while its laws run.  writ's own, and clojure's and
  jolt's otherwise, are only read."
  [s]
  (let [e (get @spec/registry s)
        named (for [x (tree-seq coll? seq (dissoc e :uses))
                    :when (and (symbol? x) (namespace x))
                    :let [n (symbol (namespace x))]
                    :when (and (find-ns n)
                               (not (re-find #"^(clojure|jolt)\." (str n)))
                               (not (contains? '#{writ.spec writ.law writ.core} n)))]
                n)]
    (set (concat (when-let [t (:target e)] [t])
                 named
                 ;; what the target's code calls: another spec may assume, and
                 ;; wrap, one of those -- clojure.string/trim
                 (when-let [t (:target e)]
                   (for [gs (vals (try (spec/call-graph t) (catch Throwable _ {})))
                         g gs :when (namespace g)]
                     (symbol (namespace g))))
                 ;; an assumed fn is wrapped while the laws run, clojure's too
                 (keep #(when-let [n (some-> % namespace symbol)]
                          ;; by the namespace the spec's alias names
                          (or (some-> (get (try (ns-aliases s) (catch Throwable _ {})) n) ns-name) n))
                       (keys (:assumes e)))
                 (mapcat touched (:uses e))))))

(defn- disjoint-units
  "specs in groups no two of which touch a namespace in common, each in
  the order given: checks in different groups share nothing, and may run
  at once."
  [specs]
  (let [ts (into {} (for [s specs] [s (touched s)]))
        ;; union-find over specs, joined through each namespace they touch
        parent (atom (zipmap specs specs))
        root (fn root [x] (let [p (get @parent x)] (if (= p x) x (root p))))
        owner (atom {})]
    (doseq [s specs, n (get ts s)]
      (if-let [o (get @owner n)]
        (let [a (root s) b (root o)] (when (not= a b) (swap! parent assoc a b)))
        (swap! owner assoc n s)))
    (vals (group-by root specs))))

(defn- in-workers
  "(mapv f units), the calls spread over n threads, each taking the next
  unit as it finishes one; the results in the order of units."
  [n f units]
  (let [units (vec units)
        next-i (atom -1)
        out (object-array (count units))
        work (fn [] (loop []
                      (let [i (swap! next-i inc)]
                        (when (< i (count units))
                          (aset out i (f (nth units i)))
                          (recur)))))]
    (run! deref (doall (repeatedly (min n (count units)) #(future (work)))))
    (vec out)))

(defn run
  "Check each spec namespace and return a row per law the prover tried:
  {:spec :law :status :proved? :winner :fuel :ms :attempts}.  opts go to
  writ.spec/check, over :cache false, :explain true, :adequacy false and
  :seed 1, so a run is the same run each time.

  The specs are checked :jobs at a time (one a processor by default),
  each check on one thread.  A check rebinds the fns of the namespaces it
  touches while it runs, so specs that touch one in common go to one
  worker, one after another; the rest share nothing, and the rows are
  those a run one at a time gives, in the same order.  Only :ms, time on
  a busy machine, may differ."
  ([specs] (run specs {}))
  ([specs opts]
   (let [jobs (or (:jobs opts) (.availableProcessors (Runtime/getRuntime)))
         opts (dissoc opts :jobs)
         ;; loaded one at a time: requiring is not done from many threads
         _ (doseq [s specs] (require s))]
     (if (<= jobs 1)
       (vec (mapcat #(spec-rows % opts) specs))
       (let [groups (disjoint-units specs)
             done (in-workers jobs
                              (fn [ss] (into {} (for [s ss] [s (spec-rows s (assoc opts :parallel false))])))
                              (sort-by #(- (count %)) groups))
             by-spec (apply merge done)]
         (vec (mapcat by-spec specs)))))))

(defn- p95 [xs]
  (if (empty? xs) 0 (nth (vec (sort xs)) (min (dec (count xs)) (int (* 0.95 (count xs)))))))

(defn summary
  "The rows in aggregate: laws proved of those tried, total rewrites and
  time, the 95th percentile of a law's time, and how many laws each
  strategy won."
  [rows]
  {:laws (count rows)
   :proved (count (filter :proved? rows))
   :fuel (reduce + 0 (map :fuel rows))
   :ms (reduce + 0 (map :ms rows))
   :p95-ms (p95 (map :ms rows))
   :winners (into (sorted-map) (frequencies (keep :by rows)))})

(defn- slower? [a b] (and (> (:ms b) (* 1.5 (:ms a))) (> (- (:ms b) (:ms a)) 200)))

(defn compare
  "What changed from baseline rows to current rows: {:gained :lost
  :slower :faster :new :gone}, each a vector of [spec law] with the two
  times for a speed change."
  [baseline current]
  (let [k (juxt :spec :law)
        b (into {} (map (juxt k identity)) baseline)
        c (into {} (map (juxt k identity)) current)
        both (filter #(contains? b %) (keys c))]
    {:gained (vec (sort (filter #(and (:proved? (c %)) (not (:proved? (b %)))) both)))
     :lost (vec (sort (filter #(and (:proved? (b %)) (not (:proved? (c %)))) both)))
     :slower (vec (sort (for [x both :when (slower? (b x) (c x))] [x (:ms (b x)) (:ms (c x))])))
     :faster (vec (sort (for [x both :when (slower? (c x) (b x))] [x (:ms (b x)) (:ms (c x))])))
     :new (vec (sort (remove #(contains? b %) (keys c))))
     :gone (vec (sort (remove #(contains? c %) (keys b))))}))

(defn table
  "The rows as text, one line a law, and the summary under them."
  [rows]
  (let [line (fn [{:keys [spec law status winner fuel ms]}]
               (format "%-40s %-44s %-9s %8d %7d  %s" (str spec) (str law) (name status) fuel ms (or winner "")))
        {:keys [laws proved fuel ms p95-ms winners]} (summary rows)]
    (str (format "%-40s %-44s %-9s %8s %7s  %s" "spec" "law" "status" "fuel" "ms" "proved by") "\n"
         (str/join "\n" (map line rows))
         "\n\n" proved " of " laws " laws proved; " fuel " rewrites, " ms " ms (95% of laws under "
         p95-ms " ms)\nwon by: "
         (str/join ", " (for [[w n] winners] (str (name w) " " n))))))

(defn- show-compare [{:keys [gained lost slower faster new gone]}]
  (let [ks #(str/join ", " (map (fn [[s l]] (str s "/" l)) %))
        ts #(str/join ", " (map (fn [[[s l] a b]] (str s "/" l " " a "->" b "ms")) %))]
    (str "gained: " (ks gained) "\nlost: " (ks lost)
         "\nslower: " (ts slower) "\nfaster: " (ts faster)
         (when (seq new) (str "\nnew: " (ks new)))
         (when (seq gone) (str "\ngone: " (ks gone))))))

(defn tune
  "Run each candidate prover config -- a map over
  writ.prove/default-config -- on a tuning corpus and a held-out one, and
  compare it with the default there, law by law.  A candidate is worth
  adopting only if it loses no law on either corpus and costs less: the
  report says, for each, what it gained and lost, and its rewrites and
  time against the default's.  Returns [{:config :tune :held-out}], each
  corpus {:compare :fuel [default candidate] :ms [default candidate]}.
  opts go to run: :jobs, the specs checked at once."
  ([configs tune-specs held-out-specs] (tune configs tune-specs held-out-specs {}))
  ([configs tune-specs held-out-specs opts]
  (let [base {:tune (run tune-specs opts) :held-out (run held-out-specs opts)}]
    (vec (for [c configs
               :let [rows {:tune (run tune-specs (assoc opts :prover c))
                           :held-out (run held-out-specs (assoc opts :prover c))}]]
           (into {:config c}
                 (for [k [:tune :held-out]
                       :let [b (get base k) r (get rows k)
                             total #(reduce + 0 (map %1 %2))]]
                   [k {:compare (compare b r)
                       :fuel [(total :fuel b) (total :fuel r)]
                       :ms [(total :ms b) (total :ms r)]}])))))))

(defn tune-report
  "tune's result as text: one block a config, and whether it is safe."
  [results]
  (str/join "\n\n"
            (for [{:keys [config] :as r} results]
              (str (pr-str config)
                   (apply str (for [k [:tune :held-out]
                                    :let [{:keys [compare fuel ms]} (get r k)]]
                                (str "\n  " (name k) ": " (count (:gained compare)) " gained, "
                                     (count (:lost compare)) " lost; rewrites " (first fuel) " -> " (second fuel)
                                     ", ms " (first ms) " -> " (second ms)
                                     (when (seq (:lost compare))
                                       (str "\n    lost: " (str/join ", " (map (fn [[s l]] (str s "/" l)) (:lost compare))))))))
                   (let [safe? (every? #(empty? (get-in r [% :compare :lost])) [:tune :held-out])
                         cheaper? (every? #(let [[a b] (get-in r [% :fuel])] (<= b a)) [:tune :held-out])]
                     (str "\n  " (cond (not safe?) "loses laws: keep the default"
                                        cheaper? "loses nothing and costs no more: a candidate for the default"
                                        :else "loses nothing but costs more")))))))

(defn- path->ns
  "test/writ/spec_demo/sort_spec.clj -> writ.spec-demo.sort-spec, reading
  the path from its first directory under test/ or src/."
  [p]
  (-> (str p)
      (str/replace #"^(.*/)?(test|src)/" "")
      (str/replace #"\.clj$" "")
      (str/replace "_" "-")
      (str/replace "/" ".")
      symbol))

(defn specs-in
  "The spec namespaces of the *_spec.clj files in dir, sorted."
  [dir]
  (sort (map path->ns (fs/list-dir dir "*_spec.clj"))))

(defn -main [& args]
  (let [[flags names] (loop [as args, fl {}, ns []]
                        (cond
                          (empty? as) [fl ns]
                          (= "--save" (first as)) (recur (drop 2 as) (assoc fl :save (second as)) ns)
                          (= "--baseline" (first as)) (recur (drop 2 as) (assoc fl :baseline (second as)) ns)
                          (= "--tune" (first as)) (recur (drop 2 as) (assoc fl :tune (read-string (second as))) ns)
                          (= "--held-out" (first as)) (recur (rest as) (assoc fl :held-out (count ns)) ns)
                          (= "--jobs" (first as)) (recur (drop 2 as) (assoc fl :jobs (parse-long (second as))) ns)
                          :else (recur (rest as) fl (conj ns (first as)))))
        specs-of (fn [names] (mapcat #(if (str/includes? % "/") (specs-in %) [(symbol %)]) names))]
    (when-let [configs (:tune flags)]
      (let [n (or (:held-out flags) (count names))]
        (println (tune-report (tune configs (specs-of (take n names)) (specs-of (drop n names))
                                    (select-keys flags [:jobs])))))
      (System/exit 0))
    (let [specs (specs-of names)
          rows (run specs (select-keys flags [:jobs]))]
    (println (table rows))
    (when-let [f (:baseline flags)]
      (println (str "\nagainst " f ":\n" (show-compare (compare (read-string (slurp f)) rows)))))
    (when-let [f (:save flags)]
      (spit f (pr-str (mapv #(dissoc % :attempts) rows)))
      (println (str "\nsaved " (count rows) " rows to " f)))
    (System/exit 0))))
