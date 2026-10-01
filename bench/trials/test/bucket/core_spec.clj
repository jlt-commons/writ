(ns bucket.core-spec
  "The contract for bucket.core: a token bucket that earns one token every
  interval-ms, holds at most capacity, and lets a request through only when
  it has the tokens for it.

  A generated Nat stays under 51 and a token takes 100 ms, so the laws reach
  later times from a generated number of whole intervals and a remainder:
  (after b d r) is d intervals and r ms after the bucket's last refill."
  (:require [bucket.core :refer [capacity interval-ms]]
            [writ.spec :refer [spec ann law graph refine]]))

(spec bucket.core)

(refine Bucket [b {:tokens Nat, :last Nat}] (<= (:tokens b) capacity))

(ann refill   [Bucket Nat -> Bucket])
(ann try-take [Bucket Nat Nat -> (Tuple Bool Bucket)])
(ann wait-ms  [Bucket Nat Nat -> (Opt Nat)])

(graph limiter
  {:start  [:bucket {:tokens 10 :last 0}]
   :states {:bucket Bucket, :taken (Tuple Bool Bucket)}
   :edges  {:bucket {[refill Nat]       #{:bucket}
                     [try-take Nat Nat] #{:taken}}
            :taken  {[second] #{:bucket}}}
   :runs   30})

(defn after
  "d whole intervals and r ms after b's last refill."
  [b d r]
  (+ (:last b) (* d interval-ms) r))

(defn earned
  "The tokens b earns by time t, before the cap."
  [b t]
  (if (<= t (:last b)) 0 (quot (- t (:last b)) interval-ms)))

;; --- refill ------------------------------------------------------------------------

(law time-running-backwards-changes-nothing
  (forall [b Bucket, t Nat] (=> (<= t (:last b)) (= b (refill b t)))))

(law a-bucket-earns-a-token-per-interval-up-to-capacity
  (forall [b Bucket, d Nat, r Nat]
    (= (:tokens (refill b (after b d r)))
       (min capacity (+ (:tokens b) (earned b (after b d r)))))))

(law refilling-in-two-steps-is-refilling-once
  (forall [b Bucket, d1 Nat, r1 Nat, d2 Nat, r2 Nat]
    (= (refill (refill b (after b d1 r1)) (+ (after b d1 r1) (* d2 interval-ms) r2))
       (refill b (+ (after b d1 r1) (* d2 interval-ms) r2)))))

(law a-full-bucket-banks-no-time
  (forall [b Bucket, d Nat, r Nat]
    (=> (>= (+ (:tokens b) (earned b (after b d r))) capacity)
        (= (after b d r) (:last (refill b (after b d r)))))))

;; --- taking ------------------------------------------------------------------------

(law a-request-passes-exactly-when-the-tokens-are-there
  (forall [b Bucket, d Nat, r Nat, n Nat]
    (= (first (try-take b (after b d r) n))
       (<= n (:tokens (refill b (after b d r)))))))

(law a-passed-request-spends-its-tokens
  (forall [b Bucket, d Nat, r Nat, n Nat]
    (=> (first (try-take b (after b d r) n))
        (= (second (try-take b (after b d r) n))
           (update (refill b (after b d r)) :tokens - n)))))

(law a-refused-request-spends-nothing
  (forall [b Bucket, d Nat, r Nat, n Nat]
    (=> (not (first (try-take b (after b d r) n)))
        (= (second (try-take b (after b d r) n)) (refill b (after b d r))))))

;; --- waiting -----------------------------------------------------------------------

(law more-than-capacity-never-passes
  (forall [b Bucket, t Nat, k Nat]
    (nil? (wait-ms b t (+ capacity 1 k)))))

(law the-wait-is-exactly-long-enough
  (forall [b Bucket, t Nat, n Nat]
    (=> (<= n capacity)
        (and (first (try-take b (+ t (wait-ms b t n)) n))
             (or (zero? (wait-ms b t n))
                 (not (first (try-take b (+ t (wait-ms b t n) -1) n))))))))
