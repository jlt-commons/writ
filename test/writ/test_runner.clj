(ns writ.test-runner
  "Hand-rolled test runner. Keeps the project dependency-free.

    jolt -M:test                     every test namespace, spread over jolt
                                     processes (WRIT_TEST_JOBS, default 4),
                                     the slow ones split into shards
    jolt -M:test --serial            every namespace in this process
    jolt -M:test --run NS[:i/n] ...  these namespaces in this process, a
                                     shard i of n taking every nth test

  Exits non-zero on any failure."
  (:require [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :as t]))

(def test-namespaces
  '[writ.check-test writ.book-test writ.gaps-test writ.spec-test writ.prove-test writ.evidence-test
    writ.graph-test writ.solve-test writ.symbolic-test writ.proof-test writ.flow-test writ.shell-test
    writ.bench-test writ.domain-test writ.record-test writ.assume-test writ.frame-test writ.entity-test writ.ensures-test writ.throws-test writ.elicit-test writ.actors-test writ.starved-test writ.speed-test])

(def ^:private shards
  "How many processes a slow namespace is split over."
  '{writ.starved-test 4, writ.prove-test 3, writ.proof-test 2, writ.spec-test 2, writ.graph-test 2})

(defn- parse-task
  "\"ns\" or \"ns:i/n\" as [ns i n]."
  [s]
  (if-let [[_ nm i n] (re-matches #"(.+):(\d+)/(\d+)" s)]
    [(symbol nm) (parse-long i) (parse-long n)]
    [(symbol s) 0 1]))

(defn- run-task
  "Run shard i of n of namespace nm here; the report's counters."
  [[nm i n]]
  (require nm)
  (let [vs (->> (vals (ns-interns nm))
                (filter #(:test (meta %)))
                (sort-by str)
                (keep-indexed (fn [k v] (when (= i (mod k n)) v))))]
    (binding [t/*report-counters* (ref t/*initial-report-counters*)]
      (t/do-report {:type :begin-test-ns :ns (the-ns nm)})
      (t/test-vars vs)
      @t/*report-counters*)))

(defn- run-here [tasks]
  (let [cs (mapv run-task tasks)
        total (apply merge-with + {:test 0 :pass 0 :fail 0 :error 0} cs)]
    (println (str "WRIT-RESULT " (pr-str total)))
    total))

(defn- run-spread
  "Each task in a jolt process of its own, jobs at a time, the slow ones
  first; a task's output is printed whole when it fails."
  [jobs]
  (let [tasks (vec (for [nm (sort-by #(- (get shards % 1)) test-namespaces)
                         :let [n (get shards nm 1)]
                         i (range n)]
                     (if (= 1 n) (str nm) (str nm ":" i "/" n))))
        next-i (atom -1)
        lock (Object.)
        results (atom [])
        work (fn []
               (loop []
                 (let [k (swap! next-i inc)]
                   (when (< k (count tasks))
                     (let [task (nth tasks k)
                           t0 (System/currentTimeMillis)
                           {:keys [out err exit]} (sh/sh (or (System/getenv "JOLT") "jolt") "-M:test" "--run" task)
                           line (last (filter #(str/starts-with? % "WRIT-RESULT ") (str/split-lines (str out))))
                           c (when line (read-string (subs line (count "WRIT-RESULT "))))
                           ok? (and c (zero? exit) (zero? (+ (:fail c) (:error c))))]
                       (locking lock
                         (println (format "%-28s %4ds  %s" task (quot (- (System/currentTimeMillis) t0) 1000)
                                          (if c (str (:test c) " tests, " (:fail c) " failures, " (:error c) " errors")
                                              (str "exit " exit))))
                         (when-not ok? (println out) (println err)))
                       (swap! results conj (or c {:test 0 :pass 0 :fail 0 :error 1}))
                       (recur))))))]
    (run! deref (doall (repeatedly jobs #(future (work)))))
    (let [total (apply merge-with + {:test 0 :pass 0 :fail 0 :error 0} @results)]
      (println (str "\nRan " (:test total) " tests. " (:pass total) " assertions passed, "
                    (:fail total) " failures, " (:error total) " errors."))
      total)))

(defn -main [& args]
  (let [{:keys [fail error]}
        (case (first args)
          "--serial" (run-here (map #(vector % 0 1) test-namespaces))
          "--run" (run-here (map parse-task (rest args)))
          (run-spread (or (some-> (System/getenv "WRIT_TEST_JOBS") parse-long) 4)))]
    (shutdown-agents)
    (System/exit (if (zero? (+ (or fail 0) (or error 0))) 0 1))))
