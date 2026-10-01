(ns library.core-spec
  "The contract for library.core, written from the problem statement: a
  library lends copies, fines late returns, renews loans, and keeps a
  queue of members waiting for each title.

  A random library almost never keeps the library's rules (loan counts
  that match the copies, queues without the members who have the title),
  so `settle` makes any library one that does, and Lib is built through it."
  (:require [library.core :refer [loan-days renew-days max-renewals max-loans
                                  fine-per-day fine-cap fine-block pickup-days]]
            [writ.spec :refer [spec ann law graph refine]]))

(spec library.core)

;; --- the parts --------------------------------------------------------------------

(refine Title    [t Nat] (< t 3))
(refine MemberId [m Nat] (< m 4))
(refine CopyId   [c Nat] (< c 6))
(refine Status   [s Keyword] (contains? #{:shelf :loaned :held} s))

(refine Copy [c {:id CopyId, :title Title, :status Status, :holder (Opt MemberId),
                 :due (Opt Nat), :renewals Nat}]
  true)
(refine Member [m {:id MemberId, :fines Nat, :loans Nat}] true)

;; --- the spec's vocabulary --------------------------------------------------------

(defn copy [l id] (get-in l [:copies id]))
(defn member [l id] (get-in l [:members id]))
(defn waiting [l t] (vec (get (:holds l) t [])))
(defn copies-of [l t] (filter #(= t (:title %)) (vals (:copies l))))
(defn on-loan-to [l m] (count (filter #(and (= :loaned (:status %)) (= m (:holder %))) (vals (:copies l)))))
(defn has-title? [l m t]
  (boolean (some #(and (= m (:holder %)) (contains? #{:loaned :held} (:status %))) (copies-of l t))))
(defn queues
  "The hold queues, a title nobody waits for left out: missing and [] are
  the same."
  [l]
  (into {} (remove (comp empty? val)) (:holds l)))

(defn well-formed-copy? [l c]
  (case (:status c)
    :shelf  (and (nil? (:holder c)) (nil? (:due c)) (zero? (:renewals c)))
    :loaned (and (contains? (:members l) (:holder c)) (some? (:due c)) (<= (:renewals c) max-renewals))
    :held   (and (contains? (:members l) (:holder c)) (some? (:due c)) (zero? (:renewals c)))
    false))

(defn consistent? [l]
  (and (every? #(well-formed-copy? l %) (vals (:copies l)))
       (every? (fn [m] (and (= (:loans m) (on-loan-to l (:id m))) (<= (:loans m) max-loans)))
               (vals (:members l)))
       (every? (fn [[t q]]
                 (and (= (count q) (count (distinct q)))
                      (every? #(contains? (:members l) %) q)
                      (not-any? #(has-title? l % t) q)
                      (or (empty? q)
                          (and (seq (copies-of l t))
                               (not-any? #(= :shelf (:status %)) (copies-of l t))))))
               (:holds l))))

(defn- shelved [c] (assoc c :status :shelf :holder nil :due nil :renewals 0))

(defn settle
  "Any library made one that keeps the rules: a copy lent or held for no
  member is lent or held for one that is, or goes back on the shelf when
  there are no members; a member's loans past max-loans go back on the
  shelf; loan counts are counted; and a queue keeps only members who may
  wait for the title, and only while none of its copies is on the shelf.
  Half the members owe close to fine-block, where borrowing stops."
  [raw]
  (let [members (into {} (for [[id m] (:members raw)]
                           [id (update m :fines #(if (odd? %) (+ (- fine-block 5) (mod % 11)) %))]))
        someone (fn [c] (if (contains? members (:holder c))
                          (:holder c)
                          (when (seq members)
                            (nth (sort (keys members)) (mod (:id c) (count members))))))
        fix (fn [c]
              (let [c (merge {:holder nil :due nil} c)
                    h (someone c)]
                (case (:status c)
                  :shelf (shelved c)
                  :loaned (if h
                            (assoc c :holder h :due (or (:due c) 0) :renewals (min max-renewals (:renewals c)))
                            (shelved c))
                  :held (if h
                          (assoc c :holder h :due (or (:due c) 0) :renewals 0)
                          (shelved c)))))
        ;; each member keeps at most max-loans copies, the lowest ids
        copies (loop [cs (sort-by :id (map fix (vals (:copies raw)))), n {}, out {}]
                 (if-let [c (first cs)]
                   (if (= :loaned (:status c))
                     (if (< (get n (:holder c) 0) max-loans)
                       (recur (rest cs) (update n (:holder c) (fnil inc 0)) (assoc out (:id c) c))
                       (recur (rest cs) n (assoc out (:id c) (shelved c))))
                     (recur (rest cs) n (assoc out (:id c) c)))
                   out))
        l {:copies copies :members members :holds {}}
        members (into {} (for [[id m] members] [id (assoc m :loans (on-loan-to l id))]))
        l (assoc l :members members)
        holds (into {} (for [[t q] (:holds raw)
                             :let [cs (copies-of l t)]]
                         [t (if (and (seq cs) (not-any? #(= :shelf (:status %)) cs))
                              (vec (distinct (filter #(and (contains? members %) (not (has-title? l % t))) q)))
                              [])]))]
    (assoc l :holds holds)))

(refine Lib [l {:copies (Index :id Copy), :members (Index :id Member), :holds (Map Title (Vec MemberId))}]
  (consistent? l)
  {:build settle})

(ann checkout     [Lib MemberId CopyId Nat -> Lib])
(ann return-copy  [Lib CopyId Nat -> Lib])
(ann renew        [Lib CopyId Nat -> Lib])
(ann place-hold   [Lib MemberId Title -> Lib])
(ann cancel-hold  [Lib MemberId Title -> Lib])
(ann expire-holds [Lib Nat -> Lib])
(ann pay          [Lib MemberId Nat -> Lib])

;; --- the steps: each keeps the library's rules, and touches only its part ---------

(def opening
  {:copies  {0 {:id 0 :title 0 :status :shelf :holder nil :due nil :renewals 0}
             1 {:id 1 :title 0 :status :shelf :holder nil :due nil :renewals 0}
             2 {:id 2 :title 1 :status :shelf :holder nil :due nil :renewals 0}
             3 {:id 3 :title 2 :status :shelf :holder nil :due nil :renewals 0}}
   :members {0 {:id 0 :fines 0 :loans 0}
             1 {:id 1 :fines 0 :loans 0}
             2 {:id 2 :fines 0 :loans 0}}
   :holds   {}})

(graph lending
  {:start  [:lib opening]
   :states {:lib Lib}
   :edges  {:lib {[checkout MemberId CopyId Nat]  {:to #{:lib} :changes [:copies :members]}
                  [return-copy CopyId Nat]        #{:lib}
                  [renew CopyId Nat]              {:to #{:lib} :changes [:copies]}
                  [place-hold MemberId Title]     {:to #{:lib} :changes [:holds]}
                  [cancel-hold MemberId Title]    {:to #{:lib} :changes [:holds]}
                  [expire-holds Nat]              {:to #{:lib} :changes [:copies :holds]}
                  [pay MemberId Nat]              {:to #{:lib} :changes [:members]}}}
   :runs   40})

;; --- checkout ---------------------------------------------------------------------

(defn may-borrow? [l m c]
  (let [cp (copy l c), mb (member l m)]
    (boolean (and cp mb
                  (or (= :shelf (:status cp)) (and (= :held (:status cp)) (= m (:holder cp))))
                  (< (:loans mb) max-loans)
                  (< (:fines mb) fine-block)))))

(law a-checkout-lends-the-copy-until-its-due-day
  (forall [l Lib, m MemberId, c CopyId, d Nat]
    (=> (may-borrow? l m c)
        (= (copy (checkout l m c d) c)
           (assoc (copy l c) :status :loaned :holder m :due (+ d loan-days) :renewals 0)))))

(law a-checkout-adds-a-loan-to-the-member
  (forall [l Lib, m MemberId, c CopyId, d Nat]
    (=> (may-borrow? l m c)
        (= (inc (:loans (member l m))) (:loans (member (checkout l m c d) m))))))

(law a-checkout-touches-only-that-copy-and-member
  (forall [l Lib, m MemberId, c CopyId, d Nat]
    (and (= (dissoc (:copies (checkout l m c d)) c) (dissoc (:copies l) c))
         (= (dissoc (:members (checkout l m c d)) m) (dissoc (:members l) m)))))

(law a-checkout-not-allowed-changes-nothing
  (forall [l Lib, m MemberId, c CopyId, d Nat]
    (=> (not (may-borrow? l m c)) (= l (checkout l m c d)))))

(law owing-500-bars-borrowing
  (forall [l Lib, m MemberId, c CopyId, d Nat]
    (=> (<= 500 (:fines (member l m))) (= l (checkout l m c d)))))

;; --- returning --------------------------------------------------------------------

(defn loaned? [l c] (= :loaned (:status (copy l c))))

(defn late-fine [due today]
  (min fine-cap (* fine-per-day (max 0 (- today due)))))

(law a-late-return-is-fined-by-the-day-up-to-the-cap
  (forall [l Lib, c CopyId, d Nat]
    (=> (loaned? l c)
        (= (+ (:fines (member l (:holder (copy l c)))) (late-fine (:due (copy l c)) d))
           (:fines (member (return-copy l c d) (:holder (copy l c))))))))

(law a-return-ends-the-loan
  (forall [l Lib, c CopyId, d Nat]
    (=> (loaned? l c)
        (= (dec (:loans (member l (:holder (copy l c)))))
           (:loans (member (return-copy l c d) (:holder (copy l c))))))))

(law a-returned-copy-is-held-for-the-first-in-line
  (forall [l Lib, c CopyId, d Nat]
    (=> (and (loaned? l c) (seq (waiting l (:title (copy l c)))))
        (= (assoc (copy l c) :status :held :holder (first (waiting l (:title (copy l c))))
                  :due (+ d pickup-days) :renewals 0)
           (copy (return-copy l c d) c)))))

(law the-first-in-line-leaves-the-queue
  (forall [l Lib, c CopyId, d Nat]
    (=> (loaned? l c)
        (= (vec (rest (waiting l (:title (copy l c)))))
           (waiting (return-copy l c d) (:title (copy l c)))))))

(law with-nobody-waiting-a-returned-copy-is-shelved
  (forall [l Lib, c CopyId, d Nat]
    (=> (and (loaned? l c) (empty? (waiting l (:title (copy l c)))))
        (= (shelved (copy l c)) (copy (return-copy l c d) c)))))

(law a-return-touches-only-that-copy-its-borrower-and-its-queue
  (forall [l Lib, c CopyId, d Nat]
    (and (= (dissoc (:copies (return-copy l c d)) c) (dissoc (:copies l) c))
         (= (dissoc (:members (return-copy l c d)) (:holder (copy l c)))
            (dissoc (:members l) (:holder (copy l c))))
         (= (dissoc (queues (return-copy l c d)) (:title (copy l c)))
            (dissoc (queues l) (:title (copy l c)))))))

(law returning-a-copy-not-on-loan-changes-nothing
  (forall [l Lib, c CopyId, d Nat]
    (=> (not (loaned? l c)) (= l (return-copy l c d)))))

;; --- renewing ---------------------------------------------------------------------

(defn may-renew? [l c d]
  (and (loaned? l c)
       (< (:renewals (copy l c)) max-renewals)
       (<= d (:due (copy l c)))
       (empty? (waiting l (:title (copy l c))))))

(defn a-loan
  "One of the library's loaned copies, picked by a generated index."
  [l i]
  (let [ids (sort (keep #(when (= :loaned (:status %)) (:id %)) (vals (:copies l))))]
    (when (seq ids) (nth ids (mod i (count ids))))))

(defn on-or-before
  "A day `back` days before copy c's due day, or the due day itself."
  [l c back]
  (max 0 (- (or (:due (copy l c)) 0) back)))

(law a-renewal-moves-the-due-day-from-the-due-day
  (forall [l Lib, i Nat, back Nat]
    (=> (may-renew? l (a-loan l i) (on-or-before l (a-loan l i) back))
        (= (assoc (copy l (a-loan l i))
                  :due (+ (:due (copy l (a-loan l i))) renew-days)
                  :renewals (inc (:renewals (copy l (a-loan l i)))))
           (copy (renew l (a-loan l i) (on-or-before l (a-loan l i) back)) (a-loan l i))))))

(law a-renewal-touches-only-that-copy
  (forall [l Lib, c CopyId, d Nat]
    (= (dissoc (:copies (renew l c d)) c) (dissoc (:copies l) c))))

(law a-renewal-not-allowed-changes-nothing
  (forall [l Lib, c CopyId, d Nat]
    (=> (not (may-renew? l c d)) (= l (renew l c d)))))

;; --- holds ------------------------------------------------------------------------

(defn may-hold? [l m t]
  (and (contains? (:members l) m)
       (boolean (seq (copies-of l t)))
       (not-any? #(= :shelf (:status %)) (copies-of l t))
       (not (has-title? l m t))
       (not (some #{m} (waiting l t)))))

(law a-hold-joins-the-end-of-the-queue
  (forall [l Lib, m MemberId, t Title]
    (=> (may-hold? l m t)
        (= (conj (waiting l t) m) (waiting (place-hold l m t) t)))))

(law a-hold-touches-only-its-queue
  (forall [l Lib, m MemberId, t Title]
    (= (dissoc (queues (place-hold l m t)) t) (dissoc (queues l) t))))

(law a-hold-not-allowed-changes-nothing
  (forall [l Lib, m MemberId, t Title]
    (=> (not (may-hold? l m t)) (= l (place-hold l m t)))))

(law cancelling-leaves-the-others-in-order
  (forall [l Lib, m MemberId, t Title]
    (= (vec (remove #{m} (waiting l t))) (waiting (cancel-hold l m t) t))))

(law cancelling-touches-only-its-queue
  (forall [l Lib, m MemberId, t Title]
    (= (dissoc (queues (cancel-hold l m t)) t) (dissoc (queues l) t))))

;; --- expiring holds: a model, one expired copy at a time in order of id -----------

(defn expired-model [l d]
  (reduce (fn [l id]
            (let [c (copy l id), q (waiting l (:title c))]
              (if (and (= :held (:status c)) (< (:due c) d))
                (if (seq q)
                  (-> l
                      (assoc-in [:copies id] (assoc c :holder (first q) :due (+ d pickup-days)))
                      (assoc-in [:holds (:title c)] (vec (rest q))))
                  (assoc-in l [:copies id] (shelved c)))
                l)))
          l
          (sort (keys (:copies l)))))

(law expiring-passes-each-lapsed-hold-down-the-line
  (forall [l Lib, d Nat]
    (= (:copies (expired-model l d)) (:copies (expire-holds l d)))))

(law expiring-takes-the-new-holders-off-the-queues
  (forall [l Lib, d Nat]
    (= (queues (expired-model l d)) (queues (expire-holds l d)))))

;; --- paying -----------------------------------------------------------------------

(law paying-lowers-fines-to-no-less-than-zero
  (forall [l Lib, m MemberId, a Nat]
    (=> (contains? (:members l) m)
        (= (max 0 (- (:fines (member l m)) a)) (:fines (member (pay l m a) m))))))

(law paying-touches-only-that-members-fines
  (forall [l Lib, m MemberId, a Nat]
    (and (= (dissoc (:members (pay l m a)) m) (dissoc (:members l) m))
         (= (dissoc (member (pay l m a) m) :fines) (dissoc (member l m) :fines)))))

(law paying-for-no-one-changes-nothing
  (forall [l Lib, m MemberId, a Nat]
    (=> (not (contains? (:members l) m)) (= l (pay l m a)))))
