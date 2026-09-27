(ns fetch.core-spec
  "The contract for fetch.core, the retry policy.

  A retry policy is mostly constraints, and each one is a law: the wait
  grows, it is capped, the attempts run out, and a request the server may
  already have acted on is never sent twice.

  Statuses are three-digit numbers, and a generated Nat stays under 51, so
  the laws never quantify over a raw status. They reach each band from a
  generated offset, like (+ 400 (mod n 100)), and name the statuses that
  carry meaning one by one."
  (:require [fetch.core :refer [base-ms cap-ms max-attempts]]
            [writ.spec :refer [spec data ann refine graph flow law]]))

(spec fetch.core)

(data Class Done Redirect Transient Failed)
(data Action Finish (Wait Nat) GiveUp)

(ann classify    [Nat -> Class])
(ann backoff-ms  [Nat -> Nat])
(ann repeatable? [Keyword Nat -> Bool])
(ann next-action [Keyword Nat Nat -> Action])

;; --- the flow of a request ---------------------------------------------------------

;; a wait is never shorter than the base or longer than the cap
(refine Delay [ms Nat] (<= base-ms ms cap-ms))

;; an HTTP status, or 0 when no response came back
(refine Status [n Nat] (<= n 599))

(graph retry
  {:states {:status Status, :class Class, :attempt Nat, :delay Delay,
            :method Keyword, :safe Bool, :action Action}
   :edges  {:status  {[classify] #{:class}}
            :attempt {[backoff-ms] #{:delay}}
            :method  {[repeatable? Nat] #{:safe}
                      [next-action Nat Nat] #{:action}}}})

;; next-action is the steps above put together: the status is classified,
;; a retry waits by the backoff for its attempt, and only a repeatable
;; request is retried
(flow next-action [method status attempt]
  [status classify :result]
  [attempt backoff-ms :result]
  [method repeatable? :result]
  [status repeatable?])

(def redirects #{301 302 303 307 308})
(def transient #{0 408 425 429 500 502 503 504})
(def server-refused #{408 429 503})

(defn in-band [band n] (+ band (mod n 100)))

(defn one-of
  "A member of `xs`, picked by a generated index, so a law about a set of
  statuses reports the one it failed on."
  [xs i]
  (nth (sort xs) (mod i (count xs))))

;; --- statuses ----------------------------------------------------------------------

(law every-2xx-is-done
  (forall [n Nat] (= [:Done] (classify (in-band 200 n)))))

(law the-redirects (every? #(= [:Redirect] (classify %)) redirects))

(law the-transient-failures (every? #(= [:Transient] (classify %)) transient))

(law every-other-status-has-failed
  (forall [n Nat, band Nat]
    (=> (not (or (<= 200 (in-band (* 100 (mod band 7)) n) 299)
                 (contains? redirects (in-band (* 100 (mod band 7)) n))
                 (contains? transient (in-band (* 100 (mod band 7)) n))))
        (= [:Failed] (classify (in-band (* 100 (mod band 7)) n))))))

;; --- waiting -----------------------------------------------------------------------

(law the-first-wait-is-the-base (= base-ms (backoff-ms 0)))

(law a-wait-is-positive-and-capped
  (forall [a Nat] (<= 1 (backoff-ms a) cap-ms)))

(law waits-never-shrink
  (forall [a Nat, b Nat] (=> (<= a b) (<= (backoff-ms a) (backoff-ms b)))))

(law waits-double-until-the-cap
  (forall [a Nat]
    (= (backoff-ms (inc a)) (min cap-ms (* 2 (backoff-ms a))))))

(law a-request-waits-under-twenty-seconds-in-all
  (<= (reduce + (map backoff-ms (range max-attempts))) 20000))

;; --- deciding ----------------------------------------------------------------------

(law success-and-redirects-finish
  (forall [m Keyword, n Nat, i Nat, a Nat]
    (and (= [:Finish] (next-action m (in-band 200 n) a))
         (= [:Finish] (next-action m (one-of redirects i) a)))))

(law a-transient-get-waits-then-retries
  (forall [i Nat, a Nat]
    (=> (< a max-attempts)
        (= [:Wait (backoff-ms a)] (next-action :get (one-of transient i) a)))))

(defn waits? [action] (= :Wait (first action)))

(law the-attempts-run-out
  (forall [m Keyword, i Nat, a Nat]
    (=> (>= a max-attempts)
        (not (waits? (next-action m (one-of transient i) a))))))

(defn sent-again-only-if-refused? [status action]
  (= (contains? server-refused status) (waits? action)))

(law a-post-is-sent-again-only-when-the-server-refused-it
  (forall [i Nat, a Nat]
    (=> (< a max-attempts)
        (sent-again-only-if-refused? (one-of transient i)
                                     (next-action :post (one-of transient i) a)))))

(law a-failure-is-final
  (forall [m Keyword, n Nat, a Nat]
    (=> (= [:Failed] (classify (in-band 400 n)))
        (= [:GiveUp] (next-action m (in-band 400 n) a)))))

(law idempotent-methods-are-repeatable
  (forall [s Nat]
    (every? #(repeatable? % s) [:get :head :put :delete :options])))

(law other-methods-only-when-refused
  (forall [s Nat]
    (and (= (repeatable? :post (in-band 400 s)) (contains? server-refused (in-band 400 s)))
         (= (repeatable? :patch (in-band 500 s)) (contains? server-refused (in-band 500 s))))))
