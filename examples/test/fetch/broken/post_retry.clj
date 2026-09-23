(ns fetch.broken.post-retry
  "fetch.core retrying every transient failure whatever the method. A POST
  that timed out at the gateway may already have been applied; sending it
  again charges the card twice.")

(def base-ms 250)
(def cap-ms 8000)
(def max-attempts 5)

(defn classify [status]
  (cond
    (<= 200 status 299) [:Done]
    (contains? #{301 302 303 307 308} status) [:Redirect]
    (contains? #{0 408 425 429 500 502 503 504} status) [:Transient]
    :else [:Failed]))

(defn backoff-ms
  "The wait before retry number `attempt`: doubling from base-ms, never
  past cap-ms."
  [attempt]
  (min cap-ms (* base-ms (bit-shift-left 1 (min attempt 10)))))

(defn repeatable?
  "Whether sending the request again is safe. An idempotent method always
  is; anything else only when the server says it did not act on it."
  [method status]
  (or (contains? #{:get :head :put :delete :options} method)
      (contains? #{0 408 429 500 502 503 504} status)))

(defn next-action [method status attempt]
  (case (first (classify status))
    :Done [:Finish]
    :Redirect [:Finish]
    :Failed [:GiveUp]
    :Transient (if (and (< attempt max-attempts) (repeatable? method status))
                 [:Wait (backoff-ms attempt)]
                 [:GiveUp])))
