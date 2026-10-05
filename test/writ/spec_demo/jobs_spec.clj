(ns writ.spec-demo.jobs-spec
  "A queue's order said as it reads: the job taken is a due :ready one,
  and no due job is better.  A Job's :status is any Keyword and its
  numbers any Nats, so a law meets a :ready job, or two jobs of one
  priority, only as the draws favour what the code tests."
  (:require [writ.spec :refer [spec ann law refine graph]]))

(spec writ.spec-demo.jobs {:require :tested})

(defn due? [j now] (and (= :ready (:status j)) (<= (:ready-at j) now)))

(defn better? [a b]
  (or (> (:priority a) (:priority b))
      (and (= (:priority a) (:priority b))
           (or (< (:ready-at a) (:ready-at b))
               (and (= (:ready-at a) (:ready-at b)) (< (:id a) (:id b)))))))

(refine Job [j {:id Nat, :priority Nat, :ready-at Nat, :status Keyword}] true)

(refine Queue [q {:jobs (Map Nat Job)}]
  (every? (fn [id] (= id (:id (get (:jobs q) id)))) (keys (:jobs q)))
  {:build keyed})

(defn keyed [q] {:jobs (into {} (map (fn [j] [(:id j) j]) (vals (:jobs q))))})

(ann next-job [Queue Nat -> (Opt Nat)])

(graph desk {:states {:queue Queue, :taken (Opt Nat)}
             :edges {:queue {[next-job Nat] #{:taken}}}})

(law the-next-job-is-due
  (forall [q Queue, now Nat]
    (let [id (next-job q now)]
      (=> (some? id) (due? (get (:jobs q) id) now)))))

(law no-due-job-is-better
  (forall [q Queue, now Nat]
    (let [id (next-job q now)]
      (=> (some? id)
          (every? (fn [k] (=> (due? (get (:jobs q) k) now)
                              (not (better? (get (:jobs q) k) (get (:jobs q) id)))))
                  (keys (:jobs q)))))))

(law a-due-job-is-taken
  (forall [q Queue, now Nat]
    (=> (some (fn [k] (due? (get (:jobs q) k) now)) (keys (:jobs q)))
        (some? (next-job q now)))))

(law a-due-job-named-is-taken
  (forall [q Queue, id Nat, now Nat]
    (=> (due? (get (:jobs q) id) now) (some? (next-job q now)))))
