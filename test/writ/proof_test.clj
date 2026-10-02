(ns writ.proof-test
  "The proof namespace: lemmas and hints the agent writes to get a spec's
  laws proved, kept apart from the spec, which is the contract.  A lemma
  is a law about the code like any other, so it must hold and be proved;
  it helps prove the spec's laws, but never counts as one of them."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(deftest without-its-lemma-a-law-stays-unproved
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42 :proof false})]
    (is (not (:ok r)))
    (is (= :unproved (:status (law-result r 'sorted))))
    (testing "the report shows the goal the search got stuck on, and what it was given"
      (let [[st] (:stuck (law-result r 'sorted))]
        (is (= ["induction on xs, case xs = (xs-h & xs-t)"] (:case st)))
        (is (str/includes? (:goal st) "(insert xs-h (isort xs-t))"))
        (is (some #(str/includes? % "(apply <= (isort xs-t))") (:facts st))))
      (is (str/includes? (:message r) "stuck in induction on xs, case xs = (xs-h & xs-t) on"))
      (is (str/includes? (:message r) "A lemma that proves such a goal")))))

(deftest a-proved-law-shows-no-stuck-goals-and-attempts-only-when-asked
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42 :cache false})
        e (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42 :cache false :explain true})]
    (is (nil? (:stuck (law-result r 'sorted))))
    (is (nil? (:attempts (law-result r 'sorted))))
    (is (seq (:attempts (law-result e 'sorted))))
    (is (every? #(contains? #{:proved :failed :fuel :rejected} (:outcome %)) (:attempts (law-result e 'sorted))))
    (is (= :proved (:outcome (last (:attempts (law-result e 'sorted))))))))

(deftest a-lemma-from-the-proof-namespace-gets-it-proved
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'sorted))))
    (is (= ['insert-keeps-sorted] (:lemmas (law-result r 'sorted))))
    (testing "the lemma is reported apart, and does not count as a law of the spec"
      (is (= [{:lemma 'insert-keeps-sorted :status :proved}]
             (mapv #(select-keys % [:lemma :status]) (:lemmas r))))
      ;; three laws, the graph's edge and the witness for its step
      (is (= 5 (:laws (:proof r))))
      (is (str/includes? (:message r) "lemma `insert-keeps-sorted` proved")))))

(deftest a-false-lemma-fails-the-check
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec
                      {:seed 42 :proof 'writ.spec-demo.sort-false-lemma-proof})]
    (is (not (:ok r)))
    (is (= :failed (:status (first (:lemmas r)))))
    (is (str/includes? (:message r) "lemma `insert-keeps-length` fails for"))))

(deftest proof-forms-are-checked-when-they-load
  (let [err (fn [form] (try (macroexpand-1 form) nil (catch Throwable e (ex-message e))))]
    (is (str/includes? (err '(writ.spec/hint sorted [:induct xs]))
                       "`hint sorted` takes a map"))
    (is (str/includes? (err '(writ.spec/hint sorted {:strategy :magic}))
                       ":strategy must be one of"))
    (is (str/includes? (err '(writ.spec/hint sorted {:color :red}))
                       "unknown keys"))))

(deftest the-tree-holds-a-sorted-set-is-proved-from-its-proof-namespace
  (let [r (spec/check 'writ.spec-demo.tree-spec {:seed 42 :cache false})
        l (law-result r 'holds-a-sorted-set)]
    (is (:ok r) (:message r))
    (is (= :proved (:status l)) (pr-str l))
    (is (= ['build-lists] (:lemmas l)))
    (testing "every lemma is proved, those about clojure.core alone too"
      (is (every? #(= :proved (:status %)) (:lemmas r)) (pr-str (:lemmas r)))
      (is (= :proved (:status (first (filter #(= 'none-below (:lemma %)) (:lemmas r)))))))
    (testing "the fold is proved with its accumulator varying in the hypothesis"
      (is (re-find #"by induction on xs"
                   (:proof (first (filter #(= 'build-lists (:lemma %)) (:lemmas r)))))))))

(deftest a-broken-tree-is-not-proved-a-sorted-set
  (doseq [target '[writ.spec-demo.tree-mirror writ.spec-demo.tree-bad-build]]
    (let [r (spec/check 'writ.spec-demo.tree-spec {:seed 42 :cache false :target target})]
      (is (not= :proved (:status (law-result r 'holds-a-sorted-set))) (str target))
      (is (not-any? :prover-bug (concat (:laws r) (:lemmas r))) (str target)))))

(deftest a-vary-hint-is-checked-when-it-loads
  (let [err (fn [form] (try (macroexpand-1 form) nil (catch Throwable e (ex-message e))))]
    (is (str/includes? (err '(writ.spec/hint fold {:vary acc})) ":vary is a vector"))
    (is (str/includes? (err '(writ.spec/hint fold {:induct xs :vary [xs]}))
                       "cannot vary in its own hypothesis"))
    (is (nil? (err '(writ.spec/hint fold {:induct xs :vary [acc]}))))))

(deftest a-proof-found-once-is-reused
  (let [dir (str ".target/writ-cache-test-" (System/currentTimeMillis))
        first-run (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache-dir dir})
        again (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache-dir dir})
        proved (fn [r] (set (map :law (filter #(= :proved (:status %)) (:laws r)))))]
    (is (:ok again) (:message again))
    (is (seq (proved first-run)))
    (is (= (proved first-run) (proved again)))
    (testing "the second check finds its proofs in the cache"
      (is (every? :cached (filter #(= :proved (:status %)) (:laws again))))
      (is (not-any? :cached (:laws first-run))))
    (testing "the contracts are kept apart from the laws, keyed on the code"
      (let [f (io/file dir "contracts--writ.spec-demo.court.edn")
            c (edn/read-string (slurp f))]
        (is (.exists f))
        (is (contains? (set (map :name (:rules c))) 'move%contract))))
    (testing "another target has a cache of its own"
      (let [other (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache-dir dir :target 'writ.spec-demo.court-open})]
        (is (not-any? :cached (:laws other)))))
    (testing "without the cache, every proof is found again"
      (is (not-any? :cached (:laws (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache false})))))))

;; --- the proof cache --------------------------------------------------------

(defn- cache-file-of [dir]
  (java.io.File. dir "writ.spec-demo.index-spec--writ.spec-demo.index.edn"))

(defn- temp-dir []
  (let [d (java.io.File. (System/getProperty "java.io.tmpdir") (str "writ-cache-test-" (System/nanoTime)))]
    (.mkdirs d)
    (str d)))

(deftest a-law-is-keyed-on-the-code-it-reaches
  (let [reach #'writ.spec/reach
        f '{:params [x] :body [:app my/g x]}
        g '{:params [y] :body [:call inc y]}
        h '{:params [z] :body [:call dec z]}
        prop '(forall [x Int] (= (my/f x) 1))]
    (is (= (reach {'my/f f 'my/g g 'my/h h} prop) (reach {'my/f f 'my/g g 'my/h (assoc h :body [:lit 0])} prop))
        "a fn the law does not reach is not in its key")
    (is (not= (reach {'my/f f 'my/g g} prop) (reach {'my/f f 'my/g (assoc g :body [:call dec 'y])} prop))
        "a fn it reaches through another is")
    (is (= (reach {'my/f '{:params [x] :body [:app my/f$loop3 x]} 'my/f$loop3 '{:params [l%4] :body l%4}} prop)
           (reach {'my/f '{:params [x] :body [:app my/f$loop9 x]} 'my/f$loop9 '{:params [l%12] :body l%12}} prop))
        "names translation made up are numbered afresh, so an edit elsewhere does not move them")))

(deftest a-cached-proof-is-replayed-and-a-wrong-one-never-proves
  (let [dir (temp-dir)
        check #(spec/check 'writ.spec-demo.index-spec {:cache-dir dir :seed 1 :explain true})
        proved #(set (keep (fn [l] (when (= :proved (:status l)) (:law l))) (:laws %)))
        first-run (check)
        f (cache-file-of dir)
        c (clojure.edn/read-string (slurp f))
        forget (fn [c] (assoc c :laws {}))]
    (is (= 4 (count (proved first-run))))
    (testing "with the results gone, each law's old proof is replayed, and nothing is searched"
      (spit f (pr-str (forget c)))
      (let [r (check)]
        (is (= (proved first-run) (proved r)))
        (is (every? #(= [:replay] (mapv :name (:attempts %))) (filter #(= :proved (:status %)) (:laws r))))
        (is (every? :replayed (filter #(= :proved (:status %)) (:laws r))))))
    (testing "a proof of some other law is rejected, and the law is searched for again"
      (let [ks (vec (keys (:traces c)))
            rotated (zipmap ks (map (:traces c) (concat (rest ks) [(first ks)])))]
        (spit f (pr-str (assoc (forget c) :traces rotated)))
        (let [r (check)]
          (is (= (proved first-run) (proved r)))
          (doseq [l (:laws r) :when (= :proved (:status l))]
            (is (= {:name :replay :outcome :rejected} (select-keys (first (:attempts l)) [:name :outcome])) (str (:law l)))
            (is (not (:replayed l)))))))
    (testing "a bogus proof never proves anything"
      (spit f (pr-str (assoc (forget c) :traces (zipmap (keys (:traces c)) (repeat {:by :cases :proofs [{:by :rewriting}]})))))
      (is (every? #(not (:replayed %)) (:laws (check)))))))

;; --- suggestions ----------------------------------------------------------------

(deftest a-hint-that-proves-a-law-is-found-and-printed
  ;; tree-novary-proof is tree-proof with build-lists' :induct and :vary gone
  (let [r (spec/check 'writ.spec-demo.tree-spec {:seed 1 :cache false :adequacy false :suggest true
                                                 :proof 'writ.spec-demo.tree-novary-proof})
        sg (:suggestion (first (filter #(= 'build-lists (:lemma %)) (:lemmas r))))]
    (is (= '(hint build-lists {:use [insert-keeps-bst to-list-insert] :induct xs :vary [acc]}) (:hint sg)))
    (is (str/includes? (:message r) "is proved with this hint in the proof namespace"))))

(deftest a-lemma-that-closes-a-law-is-proposed-only-once-it-is-proved
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42 :cache false :adequacy false :suggest true :proof false})
        [_ nm [_ bs body]] (:lemma (:suggestion (law-result r 'sorted)))]
    (is (= 'sorted-needs nm))
    (testing "it is insert-keeps-sorted: insert keeps an ascending list ascending"
      (is (= '[r0 (List Nat) xs-h Nat] bs))
      (is (str/includes? (pr-str body) "(writ.spec-demo.sort/insert xs-h r0)")))
    (is (str/includes? (:message r) "it passes its tests and the prover proves it"))))

(deftest suggestions-run-only-on-request
  (is (not-any? :suggestion (:laws (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42 :proof false})))))

;; --- specs that use specs -----------------------------------------------------

(deftest a-spec-cites-the-proved-laws-of-a-spec-it-uses
  (let [alone (spec/check 'writ.spec-demo.index-user-alone-spec {:seed 1 :cache false})
        uses (spec/check 'writ.spec-demo.index-user-uses-spec {:seed 1 :cache false})]
    (is (= :tested (:status (law-result alone 'a-find-is-a-match))))
    (is (= :proved (:status (law-result uses 'a-find-is-a-match))))
    (is (= '[writ.spec-demo.index-spec/a-take-is-a-match] (:lemmas (law-result uses 'a-find-is-a-match))))
    (testing "an imported law judges no stand-in and counts toward nothing"
      (is (= 2 (:laws (:proof uses)))))
    (testing "a law of a used spec that is only tested is not imported, and the report says why"
      (is (some #(= 'a-depth-is-at-most-the-printed-length (first %))
                (:skipped (first (filter #(= 'writ.spec-demo.walk-spec (:spec %)) (:uses uses))))))
      (is (str/includes? (:message uses) "law `a-depth-is-at-most-the-printed-length` of writ.spec-demo.walk-spec is not imported")))))
