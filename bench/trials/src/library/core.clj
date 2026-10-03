(ns library.core
  "The lending rules of a small library: loans, returns with fines,
  renewals, and hold queues per title.")

(def loan-days 14)
(def renew-days 14)
(def max-renewals 2)
(def max-loans 3)
(def fine-per-day 25)
(def fine-cap 300)
(def fine-block 500)
(def pickup-days 3)

(defn- queue [lib title]
  (get (:holds lib) title []))

(defn- hand-on
  "The copy passed to the next member waiting for its title, or put back
  on the shelf when nobody is."
  [lib c today]
  (let [q (queue lib (:title c))]
    (if (seq q)
      (-> lib
          (assoc-in [:copies (:id c)] (assoc c :status :held :holder (first q)
                                             :due (+ today pickup-days) :renewals 0))
          (assoc-in [:holds (:title c)] (vec (rest q))))
      (assoc-in lib [:copies (:id c)] (assoc c :status :shelf :holder nil :due nil :renewals 0)))))

(defn checkout [lib member-id copy-id today]
  (let [m (get (:members lib) member-id)
        c (get (:copies lib) copy-id)]
    (if (and m c
             (or (= :shelf (:status c))
                 (and (= :held (:status c)) (= member-id (:holder c))))
             (< (:loans m) max-loans)
             (< (:fines m) fine-block))
      (-> lib
          (assoc-in [:copies copy-id] (assoc c :status :loaned :holder member-id
                                             :due (+ today loan-days) :renewals 0))
          (assoc-in [:members member-id] (assoc m :loans (inc (:loans m)))))
      lib)))

(defn return-copy [lib copy-id today]
  (let [c (get (:copies lib) copy-id)]
    (if (and c (= :loaned (:status c)))
      (let [m (get (:members lib) (:holder c))
            late (max 0 (- today (:due c)))
            fine (min fine-cap (* fine-per-day late))]
        (hand-on (cond-> lib
                   m (assoc-in [:members (:id m)] (assoc m :fines (+ (:fines m) fine)
                                                         :loans (max 0 (dec (:loans m))))))
                 c today))
      lib)))

(defn renew [lib copy-id today]
  (let [c (get (:copies lib) copy-id)]
    (if (and c (= :loaned (:status c))
             (< (:renewals c) max-renewals)
             (<= today (:due c))
             (empty? (queue lib (:title c))))
      (assoc-in lib [:copies copy-id] (assoc c :due (+ (:due c) renew-days)
                                             :renewals (inc (:renewals c))))
      lib)))

(defn- has-title? [lib member-id title]
  (some #(and (= title (:title %)) (= member-id (:holder %))
              (contains? #{:loaned :held} (:status %)))
        (vals (:copies lib))))

(defn place-hold [lib member-id title]
  (let [copies (filter #(= title (:title %)) (vals (:copies lib)))]
    (if (and (contains? (:members lib) member-id)
             (seq copies)
             (not-any? #(= :shelf (:status %)) copies)
             (not (has-title? lib member-id title))
             (not (some #{member-id} (queue lib title))))
      (assoc-in lib [:holds title] (conj (vec (queue lib title)) member-id))
      lib)))

(defn cancel-hold [lib member-id title]
  (if (some #{member-id} (queue lib title))
    (assoc-in lib [:holds title] (vec (remove #{member-id} (queue lib title))))
    lib))

(defn expire-holds [lib today]
  (reduce (fn [l id]
            (let [c (get (:copies l) id)]
              (if (and (= :held (:status c)) (< (:due c) today))
                (hand-on l c today)
                l)))
          lib
          (sort (keys (:copies lib)))))

(defn pay [lib member-id amount]
  (if-let [m (get (:members lib) member-id)]
    (assoc-in lib [:members member-id] (assoc m :fines (max 0 (- (:fines m) amount))))
    lib))
