(ns shortener.server
  "The shortener over HTTP, on jolt-lang/ring-chez-adapter (`jolt
  -M:shortener`, then `curl -d https://clojure.org localhost:3000`).

  This namespace is the effect shell: it reads the socket, the body and the
  store, and turns shortener.core's replies into Ring responses. writ
  doesn't check it (`(writ.spec/scan 'shortener.server)` says why, form by
  form), so it is kept as thin as it can be."
  (:require [ring-chez.adapter :as adapter]
            [shortener.core :as core]
            [shortener.store :as store]))

(defn- response [host reply]
  (case (first reply)
    :Created {:status 201
              :headers {"Content-Type" "text/plain"}
              :body (str "http://" host "/" (second reply) "\n")}
    :Found {:status 302 :headers {"Location" (second reply)} :body ""}
    :Text (let [[_ status text] reply]
            {:status status :headers {"Content-Type" "text/plain"} :body text})))

(defn- body-text [req]
  (let [b (:body req)]
    (cond (nil? b) ""
          (string? b) b
          :else (slurp b))))

(defn app [req]
  (let [body (body-text req)
        reply (store/transact! #(core/handle % (:request-method req) (:uri req) body))]
    (response (get-in req [:headers "host"] "localhost") reply)))

(defn start! [port]
  (adapter/run-server app {:port port}))

(defn stop! [server]
  (adapter/stop-server server))

(defn -main [& [port]]
  (let [port (or (some-> port parse-long) 3000)]
    (start! port)
    (println (str "shortener on http://localhost:" port))
    @(promise)))
