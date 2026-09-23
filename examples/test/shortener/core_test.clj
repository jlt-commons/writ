(ns shortener.core-test
  "shortener.core meets its spec, laws and call graph both. The broken
  variants show what each part catches: the call graph catches structure
  no law sees, and the static check catches an effect in the core. Last,
  the server runs for real and is driven over HTTP."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [jolt.http-client :as http]
            [shortener.server :as server]
            [writ.spec :as spec]))

(defn- check [target]
  (spec/check 'shortener.core-spec {:target target :seed 42}))

(defn- calls-of [r f]
  (first (filter #(= f (:fn %)) (:calls r))))

(deftest the-shortener-meets-its-spec
  (let [r (spec/check 'shortener.core-spec)]
    (is (:ok r) (:message r))
    (is (every? #(= :ok (:status %)) (:calls r)))))

(deftest a-pasted-copy-of-a-layer-passes-the-laws-but-not-the-call-graph
  (let [r (check 'shortener.broken.inlined)
        c (calls-of r 'handle)]
    (is (every? #(not= :failed (:status %)) (:laws r)) "the behaviour is the same...")
    (is (= '[shorten] (:missing c)) "...but handle no longer goes through shorten")
    (is (= '[code-for encode-id normalize-url valid-url?] (:extra c)))
    (testing "and with nothing calling it, no law pins shorten down"
      (is (= '[shorten] (map :fn (:gaps r)))))))

(deftest the-core-must-not-reach-the-store
  (let [r (check 'shortener.broken.reaches-store)]
    (testing "a call into another namespace passes the purity check and the laws"
      (is (:ok (:static r)))
      (is (every? #(not= :failed (:status %)) (:laws r))))
    (testing "the call graph shows it"
      (is (= '[shortener.store/remember!] (:extra (calls-of r 'shorten))))
      (is (str/includes? (:message r)
                         "`shorten` calls `shortener.store/remember!`, which the spec does not list")))))

(deftest a-debugging-println-is-an-effect
  (let [r (check 'shortener.broken.debug-print)]
    (is (not (:ok (:static r))))
    (is (str/includes? (:message r) "`println` in `shorten` is effect code"))))

(deftest scan-follows-an-effect-up-the-call-graph
  (let [{:keys [forms]} (spec/scan 'shortener.server)
        why (into {} (map (juxt :name :why)) forms)]
    (is (str/includes? (why 'body-text) "`slurp` in `body-text` is effect code"))
    (is (= "it uses `body-text`, which writ cannot check" (why 'app)))
    (is (= "it uses `app`, which writ cannot check" (why 'start!)))
    (is (= "it uses `start!`, which writ cannot check" (why '-main)))))

(deftest the-call-graph-of-the-server
  (is (= '#{response body-text shortener.store/transact! shortener.core/handle}
         (get (spec/call-graph 'shortener.server) 'app)))
  (is (str/includes? (spec/mermaid 'shortener.core-spec) "handle --> shorten")))

(deftest the-server-shortens-and-redirects-over-http
  (let [port 38917
        base (str "http://127.0.0.1:" port)
        srv (server/start! port)]
    (try
      (let [created (http/post (str base "/") {:body "https://github.com/jolt-lang"
                                               :throw-exceptions false})
            link (str/trim (:body created))
            code (last (str/split link #"/"))
            followed (http/get (str base "/" code) {:follow-redirects false
                                                    :throw-exceptions false})
            again (http/post (str base "/") {:body "https://github.com/jolt-lang"
                                             :throw-exceptions false})
            bad (http/post (str base "/") {:body "ftp://example.com"
                                           :throw-exceptions false})]
        (is (= 201 (:status created)))
        (is (= 302 (:status followed)))
        (is (= "https://github.com/jolt-lang" (get-in followed [:headers "location"])))
        (is (= link (str/trim (:body again))) "the same URL keeps its code")
        (is (= 400 (:status bad))))
      (finally (server/stop! srv)))))
