(ns fetch.main
  "Fetch the README of each jolt-lang library this project depends on, over
  jolt-lang/http-client, retrying the way fetch.core decides (`jolt
  -M:fetch`, or pass URLs).

  The sockets, the sleeping and the printing are here; the policy is in
  fetch.core, checked by test/fetch/core_spec.clj."
  (:require [clojure.string :as str]
            [fetch.core :as policy]
            [jolt.http-client :as http]))

(def readmes
  ["https://raw.githubusercontent.com/jolt-lang/jolt/main/README.md"
   "https://raw.githubusercontent.com/jolt-lang/http-client/main/README.md"
   "https://raw.githubusercontent.com/jolt-lang/ring-chez-adapter/main/README.md"
   "https://raw.githubusercontent.com/jlt-commons/raylib-jlt/main/README.md"
   "https://raw.githubusercontent.com/jolt-lang/no-such-repo/main/README.md"])

(defn- attempt! [url]
  (try (http/get url {:throw-exceptions false :socket-timeout 10000 :conn-timeout 10000})
       (catch Exception e {:status 0 :error (ex-message e)})))

(defn fetch
  "GET `url`, following fetch.core's advice. Returns the last response
  with the number of attempts it took."
  [url]
  (loop [attempt 0]
    (let [resp (attempt! url)
          [action ms] (policy/next-action :get (:status resp) attempt)]
      (case action
        :Wait (do (println (str "  " (:status resp) " from " url ", retrying in " ms " ms"))
                  (Thread/sleep ms)
                  (recur (inc attempt)))
        (assoc resp :attempts (inc attempt) :outcome action)))))

(defn- title [text]
  (or (some #(when (str/starts-with? % "#") (str/trim (str/replace % #"^#+" "")))
            (str/split-lines text))
      "(no heading)"))

(defn -main [& urls]
  (doseq [url (if (seq urls) urls readmes)]
    (let [{:keys [status body attempts outcome error]} (fetch url)]
      (println (format "%-3s %-7s %2d attempt(s)  %s" status (name outcome) attempts url))
      (cond
        error (println "    " error)
        (= 200 status) (println (format "    %s (%d bytes)" (title body) (count body)))))))
