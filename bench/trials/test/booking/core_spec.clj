(ns booking.core-spec
  "The contract for booking.core: a calendar of room bookings that never
  holds two bookings of one room at the same time."
  (:require [clojure.set :as set]
            [writ.spec :refer [spec ann law graph refine]]))

(spec booking.core)

(refine Room [r Nat] (< r 3))
(refine Booking [b {:id Nat, :room Room, :start Nat, :end Nat}] true)

(defn span
  "The time units a booking holds: start up to, not including, end."
  [b]
  (set (range (:start b) (:end b))))

(defn clash?
  "Two bookings of one room that hold some time unit in common."
  [a b]
  (and (= (:room a) (:room b))
       (boolean (seq (set/intersection (span a) (span b))))))

(defn no-clash? [cal]
  (every? (fn [[a b]] (or (= (:id a) (:id b)) (not (clash? a b))))
          (for [a (vals cal) b (vals cal)] [a b])))

(defn well-formed? [cal]
  (every? (fn [[k b]] (and (= k (:id b)) (< (:start b) (:end b)))) cal))

(refine Calendar [cal (Index :id Booking)] (and (well-formed? cal) (no-clash? cal)))

(ann overlaps? [Booking Booking -> Bool])
(ann free?     [Calendar Room Nat Nat -> Bool])
(ann book      [Calendar Booking -> Calendar])
(ann cancel    [Calendar Nat -> Calendar])
(ann schedule  [Calendar Room -> (Vec Booking)])

(graph calendar
  {:start  [:cal {}]
   :states {:cal Calendar}
   :edges  {:cal {[book Booking] #{:cal}
                  [cancel Nat]   #{:cal}}}
   :final  [:cal]
   :runs   30})

(defn acceptable? [cal b]
  (and (< (:start b) (:end b))
       (not (contains? cal (:id b)))
       (not-any? #(clash? b %) (vals cal))))

(law overlap-is-sharing-a-time-unit
  (forall [a Booking, b Booking] (= (overlaps? a b) (clash? a b))))

(law free-means-nothing-in-the-way
  (forall [cal Calendar, r Room, s Nat, e Nat]
    (= (free? cal r s e)
       (acceptable? cal {:id -1 :room r :start s :end e}))))

(law a-booking-is-taken-exactly-when-acceptable
  (forall [cal Calendar, b Booking]
    (= (book cal b) (if (acceptable? cal b) (assoc cal (:id b) b) cal))))

(law cancel-removes-only-that-booking
  (forall [cal Calendar, id Nat] (= (cancel cal id) (dissoc cal id))))

(law cancelling-a-new-booking-undoes-it
  (forall [cal Calendar, b Booking]
    (=> (acceptable? cal b) (= cal (cancel (book cal b) (:id b))))))

(law a-schedule-is-the-rooms-bookings
  (forall [cal Calendar, r Room]
    (= (frequencies (schedule cal r))
       (frequencies (filter #(= r (:room %)) (vals cal))))))

(law a-schedule-runs-in-time-order
  (forall [cal Calendar, r Room]
    (let [starts (map :start (schedule cal r))]
      (or (empty? starts) (apply <= starts)))))
