(ns booking.core
  "Room bookings over half-open integer time intervals [start, end).")

(defn- in-the-way? [room start end b]
  (and (= room (:room b))
       (< (max start (:start b)) (min end (:end b)))))

(defn overlaps? [a b]
  (in-the-way? (:room a) (:start a) (:end a) b))

(defn free? [cal room start end]
  (and (< start end)
       (not-any? #(in-the-way? room start end %) (vals cal))))

(defn book [cal b]
  (if (and (not (contains? cal (:id b)))
           (free? cal (:room b) (:start b) (:end b)))
    (assoc cal (:id b) b)
    cal))

(defn cancel [cal id]
  (dissoc cal id))

(defn schedule [cal room]
  (vec (sort-by :start (filter #(= room (:room %)) (vals cal)))))
