(ns writ.spec
  "A spec namespace: the contract for another namespace, kept entirely
  outside it.

    (ns my.app.spec
      (:require [writ.spec :refer [spec data ann law calls]]))

    (spec my.app)                                ; the namespace it constrains
    (ann isort [(List Nat) -> (List Nat)])       ; a public fn's signature
    (law sorted (forall [xs (List Nat)] (ascending? (isort xs))))

  A spec is the problem statement: the laws say what the code means, in
  the spec's own terms, not how it works.  The implementation is plain
  Clojure and never mentions writ.  `check` reads its source and runs
  writ's static rules over it with the types the spec gives, then checks
  the spec itself and each law:

  * vacuous    -- the law holds whatever the code does (writ.norm proves it
                  without the code, or it calls no target fn): it fails,
                  because it says nothing about the code
  * evaluated  -- a closed law, decided by running the code once
  * tested     -- a universal law, run by test.check against inputs generated
                  from the binders' types; a failure is shrunk to the
                  smallest input that still breaks it, and its seed replays it
  * witnessed  -- an existential, with the generated value that satisfies it

  Tested is not proved: the report says which one each law got.

  When every law holds, `check` asks whether the laws pin the code down:
  each signed public fn is swapped for well-typed impostors (a constant,
  an argument passed through, the real result perturbed, and one that
  differs off the literals every law fixes an argument to), and an
  impostor that still satisfies every law is a gap in the spec.  A passing
  report counts the impostors each fn's laws rejected.

  `(calls f [g ...])` states the exact set of fns `f` calls, read from its
  source; `call-graph` and `mermaid` show a namespace's graph.

  `instrument` wraps the target's fns with the signatures' runtime checks,
  and `scan` says which of a namespace's fns writ could check at all."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [clojure.string :as str]
            [clojure.test]
            [writ.book :as book]
            [writ.check :as ck]
            [writ.data :as dt]
            [writ.hash :as hash]
            [writ.solve :as solve]
            [writ.kind :as kind]
            [writ.law :as lw]
            [writ.lower :as l]
            [writ.norm :as norm]
            [writ.types :as ty]
            [writ.prove :as prover]
            [writ.prove.term :as pterm]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.random :as random]
            [clojure.test.check.rose-tree :as rose]))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

;; --- the spec surface ----------------------------------------------------

(def registry
  "spec ns name -> {:target sym :data [form] :anns {name sig} :laws [law]}"
  (atom {}))

(defn- simple-sym? [x] (and (symbol? x) (nil? (namespace x))))

(defn- parse-sig
  "`[A B -> R]` into {:params [A B] :ret R}; where names the form."
  [where sig]
  (when-not (vector? sig)
    (fail! where " needs a signature vector like [A B -> R]"))
  (let [[ps [arrow & rs]] (split-with #(not= '-> %) sig)]
    (when-not (and (= '-> arrow) (= 1 (count rs)))
      (fail! where " must end in `-> ReturnType`, had: " (pr-str sig)))
    {:params (vec ps) :ret (first rs)}))

(defn parse-ann
  "`[A B -> R]` into {:params [A B] :ret R}."
  [nm sig]
  (when-not (simple-sym? nm)
    (fail! "`ann` needs a simple fn name, had: `" (pr-str nm) "`"))
  (parse-sig (str "`ann " nm "`") sig))

(def proofs
  "proof ns name -> {:proves spec-ns :lemmas [lemma] :hints {law hint}}"
  (atom {}))

(defn -register-proof! [proof-ns k v]
  (swap! proofs update proof-ns
         (fn [e] (case k
                   :proves {:proves v :lemmas [] :hints {}}
                   :lemma (update e :lemmas conj v)
                   :hint (assoc-in e [:hints (first v)] (second v)))))
  nil)

(defn -register! [spec-ns k v]
  (swap! registry update spec-ns
         (fn [e] (case k
                   :target (merge {:target (first v) :data [] :anns {} :laws [] :calls [] :machines []
                                   :refines [] :graphs []}
                                  (second v))
                   :refine (update e :refines (fnil conj []) v)
                   :graph (update e :graphs (fnil conj []) v)
                   :data (update e :data conj v)
                   :calls (update e :calls (fnil conj []) v)
                   :flow (update e :flows (fnil conj []) v)
                   :machine (update e :machines (fnil conj []) v)
                   :invariant (update e :invariants (fnil conj []) v)
                   :question (update e :questions (fnil conj []) v)
                   :assume-fn (assoc-in e [:assumes (first v)] (second v))
                   :assume-law (update e :assumptions (fnil conj []) v)
                   :ann (assoc-in e [:anns (first v)] (second v))
                   :contract (assoc-in e [:contracts (first v)] (second v))
                   :law (update e :laws conj v))))
  nil)

(def levels
  "What a law's evidence may be, strongest first.  A law is proved when the
  prover proves it, when it is closed and evaluates to true, or when an
  existential has a witness; tested when it only ran on generated inputs."
  [:proved :tested])

(defn- check-level! [where lv]
  (when-not (some #{lv} levels)
    (fail! where ": :require must be :proved or :tested, had: " (pr-str lv))))

(defmacro spec
  "Name the namespace this spec constrains.  Comes first.

    (spec my.sort)                     ; laws may be proved or only tested
    (spec my.sort {:require :proved})  ; every law must be proved

  Under {:require :proved} a law that is only tested fails the check,
  unless the law itself says why it cannot be proved yet.

    (spec my.app {:uses [my.sort-spec]})

  checks my.sort-spec first, and its laws that are proved are lemmas here:
  a proof may cite them.  Like a proof namespace's lemmas they are not
  laws of this spec, and judge no stand-in.  One that is only tested is
  not imported, and the report says so.

  It also defines `writ-check`, a clojure.test test in the spec namespace
  that runs `check` on it, so a test runner that loads the spec checks it.
  {:test {:seed 42 :trials 200}} passes options to that check, and
  {:test false} leaves the test out."
  ([target] `(spec ~target {}))
  ([target opts]
   (when-not (simple-sym? target)
     (fail! "`spec` names a namespace symbol, had: `" (pr-str target) "`"))
   (when-not (map? opts)
     (fail! "`spec " target "` takes an options map after the namespace, had: " (pr-str opts)))
   (when-let [bad (seq (remove #{:require :uses :test :baseline} (keys opts)))]
     (fail! "`spec " target "` has unknown options: " (pr-str bad) "; it takes :require, :uses, :test and :baseline"))
   (when (and (contains? opts :baseline) (not (string? (:baseline opts))))
     (fail! "`spec " target "` :baseline is the path of a record the check compares the spec with, had: "
            (pr-str (:baseline opts))))
   (when (contains? opts :require) (check-level! (str "`spec " target "`") (:require opts)))
   (when (and (contains? opts :uses) (not (and (vector? (:uses opts)) (every? simple-sym? (:uses opts)))))
     (fail! "`spec " target "` :uses takes a vector of spec namespaces, had: " (pr-str (:uses opts))))
   (let [t (get opts :test true)
         spec-ns (ns-name *ns*)]
     (when-not (or (boolean? t) (map? t))
       (fail! "`spec " target "` :test takes true, false or a map of `check` options, had: " (pr-str t)))
     `(do (-register! '~spec-ns :target '~[target (dissoc opts :test)])
          ~(when t
             `(clojure.test/deftest ~'writ-check
                (let [r# (check '~spec-ns ~(if (map? t) t {}))]
                  (clojure.test/is (:ok r#) (:message r#)))))))))

(defmacro data
  "Declare a datatype the target's values use, as writ.defn/data."
  [& args]
  (let [f (cons 'data args)]
    (dt/parse f)
    `(-register! '~(ns-name *ns*) :data '~f)))

(defn- contract-fn!
  "Check an ann's :requires or :ensures: (fn [arg ...] test), taking n
  parameters."
  [where k f n what]
  (when-not (and (seq? f) (= 'fn (first f)) (= 3 (count f)) (vector? (second f))
                 (every? simple-sym? (second f)) (= n (count (second f))))
    (fail! where ": " k " takes " what ", as (fn [" (str/join " " (repeat n "x")) "] test), had "
           (pr-str f))))

(defmacro ann
  "Give a target fn its signature: (ann f [A B -> R]).  An options map may
  say more than the types:

    (ann clamp [Int Int Int -> Int]
      {:requires (fn [lo hi x] (<= lo hi))
       :ensures  (fn [lo hi x r] (<= lo r hi))})

  :ensures is a law, `clamp:ensures`: on arguments of the parameter types
  that meet :requires, the result meets it.  It is tested, proved and
  cited like any law.  While the laws run, a call whose arguments break
  :requires fails at the call, and a result that breaks :ensures where it
  returns."
  ([nm sig] `(ann ~nm ~sig {}))
  ([nm sig opts]
   (let [s (parse-ann nm sig)
         where (str "`ann " nm "`")
         n (count (:params s))]
     (when-not (map? opts)
       (fail! where " takes an options map after the signature, had " (pr-str opts)))
     (when-let [bad (seq (remove #{:requires :ensures} (keys opts)))]
       (fail! where " has unknown options " (pr-str bad) "; it takes :requires and :ensures"))
     (when (contains? opts :requires)
       (contract-fn! where :requires (:requires opts) n (str "the fn's " n " argument(s)")))
     (when (contains? opts :ensures)
       (contract-fn! where :ensures (:ensures opts) (inc n)
                     (str "the fn's " n " argument(s) and its result, " (inc n) " in all")))
     `(do (-register! '~(ns-name *ns*) :ann '~[nm s])
          ~(when (seq opts) `(-register! '~(ns-name *ns*) :contract '~[nm opts]))))))

(defn- resolve-callee
  "A callee as the spec writes it: a target fn by its simple name, or a fn
  of another namespace, whose alias in the spec namespace is resolved."
  [g]
  (if-let [n (namespace g)]
    (let [a (get (ns-aliases *ns*) (symbol n))]
      (symbol (if a (str (ns-name a)) n) (name g)))
    g))

(defmacro calls
  "State how `f` calls:

    (calls f [g str/join])                 ; exactly these, directly
    (calls f {:through [g h] :not [io/x]}) ; reaches g and h, never io/x

  A simple name is a fn of the target; a qualified one is a fn of another
  namespace, through the spec's own aliases.  clojure.core and host
  members are not part of the call graph, and neither is `f` calling
  itself.  The map form is read on the transitive graph: `f` reaches `g`
  through any chain of the namespace's own fns.  `f` itself may be
  qualified, a fn of another namespace such as an effect shell; its
  simple names are then that namespace's own fns."
  [f gs]
  (when-not (symbol? f)
    (fail! "`calls` needs a fn name, had: `" (pr-str f) "`"))
  (let [names? #(and (vector? %) (every? symbol? %))]
    (when-not (or (names? gs)
                  (and (map? gs) (seq gs) (every? #{:through :not} (keys gs)) (every? names? (vals gs))))
      (fail! "`calls " f "` needs a vector of fn names, or {:through [fn ...] :not [fn ...]}, had: "
             (pr-str gs)))
    `(-register! '~(ns-name *ns*) :calls
                 '~[(resolve-callee f)
                    (if (map? gs) (update-vals gs #(mapv resolve-callee %)) (mapv resolve-callee gs))])))

(defmacro flow
  "State how data moves through fn `f`:

    (flow handle [req]
      [req normalize respond :result])

  The vector after `f` names its parameters, by position, for the chains
  that follow.  Each chain is a path the data takes: every link reaches
  the next.  A link is a parameter, a fn (what it returns), or, last,
  `:result`, what `f` returns.  `a` reaches fn `b` when some call `f`
  makes to `b` is passed a value that comes from `a`, directly or through
  other calls; it reaches `:result` when what `f` returns comes from it.
  A branch's test counts: a value that decides the answer reaches it."
  [f params & chains]
  (let [where (str "`flow " f "`")]
    (when-not (and (symbol? f) (vector? params) (every? simple-sym? params))
      (fail! where " is (flow f [param ...] [link link ...] ...), had: "
             (pr-str (list* 'flow f params chains))))
    (when (empty? chains)
      (fail! where " needs at least one chain: [link link ...]"))
    (doseq [c chains]
      (when-not (and (vector? c) (<= 2 (count c)))
        (fail! where ": a chain needs at least two links, had " (pr-str c)))
      (doseq [l c]
        (when-not (or (symbol? l) (= :result l))
          (fail! where ": a link is a parameter, a fn or :result, had " (pr-str l))))
      (when (some #{:result} (butlast c))
        (fail! where ": `:result` can only end a chain, had " (pr-str c))))
    `(-register! '~(ns-name *ns*) :flow
                 '~[(resolve-callee f) params (mapv (fn [c] (mapv #(if (symbol? %) (resolve-callee %) %) c)) chains)])))

(defmacro assume
  "Take as given what code writ does not check does: a library, another
  namespace, an effect shell.

    (assume str/trim [String -> String])
    (assume trim-is-idempotent
      (forall [s String] (= (str/trim (str/trim s)) (str/trim s))))

  A qualified fn and a signature: calls to it are typed by the signature
  in the static check, it is wrapped while the laws run so a value of
  the wrong type fails where it returns, and the prover takes its result
  to be of that type.  A name and a proposition: a law about such fns,
  never the target's, tested against the real fns on every check and
  cited by the prover as given.  An assumption counts toward no law and
  judges no stand-in, and every report names it: it is what the spec's
  proofs rest on."
  [nm x]
  (cond
    (and (symbol? nm) (namespace nm) (vector? x))
    `(-register! '~(ns-name *ns*) :assume-fn '~[(resolve-callee nm) (parse-sig (str "`assume " nm "`") x)])

    (and (simple-sym? nm) (vector? x))
    (fail! "`assume` names a fn by its qualified name, as str/trim, had `" nm
           "`; a simple name goes with a law: (assume name (forall ...))")

    (and (simple-sym? nm) (some? x))
    `(-register! '~(ns-name *ns*) :assume-law '~{:name nm :prop x})

    :else
    (fail! "`assume` takes (assume ns/f [A -> R]) or (assume name proposition), had: "
           (pr-str (list 'assume nm x)))))

(defmacro machine
  "State that a target fn steps a state machine by a transition table:

    (machine turnstile
      {:step step :start [:Locked]
       :transitions {[:Locked] {[:Coin] [:Unlocked]} ...}
       :final [[:Locked]] :never [[a b]] :before [[a b]]})

  `step` is run on every state and event (from its `ann` when those are
  data with field-less constructors, or :states and :events) and must give
  the table's state, or keep the state where the table lists nothing.  The
  table must reach every state from :start, and a :final state from every
  state it reaches; `:never [a b]` says no path leads from a to b, and
  `:before [a b]` that every path from :start to b passes through a."
  [nm m]
  (when-not (simple-sym? nm)
    (fail! "a `machine` name must be a simple symbol: `" (pr-str nm) "`"))
  (when-not (and (map? m) (simple-sym? (:step m)) (contains? m :start) (map? (:transitions m)))
    (fail! "`machine " nm "` needs a map with :step (a fn name), :start and :transitions"))
  (when-let [bad (seq (remove #{:step :start :transitions :final :never :before :states :events}
                              (keys m)))]
    (fail! "`machine " nm "` has unknown keys: " (pr-str bad)))
  `(-register! '~(ns-name *ns*) :machine '~[nm m]))

(defmacro refine
  "A type whose values are a base type's values that satisfy a predicate:

    (refine Row [y Int] (<= 0 y top))
    (refine Green [l (Tuple Keyword Nat)] (= :Green (first l)))

  A refinement can go wherever a type goes: in `ann`, in `forall`, as a
  graph's state.  Its values are generated to satisfy the predicate, the
  prover takes the predicate as a hypothesis, and the static check sees
  the base type.  It also defines the predicate as a fn, `Row?`.

  A value a random one of the base type rarely meets -- a receipt whose
  total is the sum of its items -- is built rather than filtered for:
  (refine Receipt [r ...] pred {:build settle}) generates base values and
  hands each to the spec's fn `settle`, which makes it one that meets pred."
  [nm binder pred & [opts]]
  (when-not (and (simple-sym? nm) (vector? binder) (= 2 (count binder)) (simple-sym? (first binder)))
    (fail! "`refine` is (refine Name [x BaseType] predicate), had: "
           (pr-str (list 'refine nm binder '...))))
  (when (and (some? opts) (not (and (map? opts) (= #{:build} (set (keys opts))) (simple-sym? (:build opts)))))
    (fail! "`refine " nm "` takes one option, {:build f}: f names the spec's fn that makes a base"
           " value one of the refinement, had: " (pr-str opts)))
  (let [[v base] binder
        pred-name (symbol (str nm "?"))
        ;; an Index's keys and unique fields are part of what a value of it
        ;; is, so a landing in a refinement of one must keep them
        pred (if (and (kind/index-type? base) (keyword? (second base)))
               (let [{k :key u :unique} (kind/index-parts base)
                     own (list 'writ.spec/indexed? k u v)]
                 (if (true? pred) own (list 'and own pred)))
               pred)]
    `(do (defn ~pred-name ~(str "Is `" v "` a " nm "?") [~v] ~pred)
         (-register! '~(ns-name *ns*) :refine '~(cond-> {:name nm :var v :base base :pred pred
                                                         :pred-name pred-name}
                                                  opts (assoc :build (:build opts)))))))

(defmacro invariant
  "State what always holds of a graph state's values, wherever they come
  from:

    (invariant signal :red [l] (pos? (second l)))

  Every edge that may land in :red carries the predicate as its own
  obligation, proved and tested with the edge itself, and the start
  value must satisfy it too.  A graph with every edge proved holds its
  invariants for every run of the code."
  [g state binder pred]
  (let [where (str "`invariant " g " " state "`")]
    (when-not (simple-sym? g)
      (fail! "an `invariant` names a graph by a simple symbol, had: `" (pr-str g) "`"))
    (when-not (keyword? state)
      (fail! "an `invariant` of `" g "` names a state by a keyword, had: " (pr-str state)))
    (when-not (and (vector? binder) (= 1 (count binder)) (simple-sym? (first binder)))
      (fail! "an `invariant` of `" g "` takes one binder for the state's value: [v predicate], had: "
             (pr-str binder)))
    `(-register! '~(ns-name *ns*) :invariant '~[g state binder pred])))

(defn- question*
  "The registration of a `question`, once its parts are checked."
  [id text opts]
  (when-not (simple-sym? id)
    (fail! "a `question` is named by a simple symbol, had: " (pr-str id)))
  (when-not (and (string? text) (not (str/blank? text)))
    (fail! "`question " id "` needs the question, as a string"))
  (when-not (and (map? opts) (every? #{:blocking} (keys opts)))
    (fail! "`question " id "` takes {:blocking true|false}, had: " (pr-str opts)))
  `(-register! '~(ns-name *ns*) :question '~{:id id :text text
                                              :blocking (boolean (:blocking opts))}))

(defmacro question
  "Record a question the spec does not answer yet:

    (question refund-reopens \"does a refund reopen a closed order?\")
    (question refund-reopens \"...\" {:blocking true})

  Every report lists the open questions, since a spec with one is not
  finished.  A blocking question, one the next piece of work depends on,
  fails the check until it is answered and removed."
  ([id text] (question* id text {}))
  ([id text opts] (question* id text opts)))

(def ^:private graph-keys #{:states :edges :start :never :before :final :tested :witnesses :runs :depth :actors
                             :model})

(declare guard-of)

(declare one-line-helpers)

(defn- when-shape!
  "An edge's :when must be (fn [state arg ...] test), taking the edge fn's
  n arguments."
  [edge w n]
  (when-not (and (seq? w) (= 'fn (first w)) (vector? (second w)) (= 3 (count w)))
    (fail! edge " needs :when (fn [state arg ...] test), or the name of a fn of the spec, of one"
           " expression, that takes the step's arguments in its order; had " (pr-str w)))
  (when-not (= n (count (second w)))
    (fail! edge ": its :when takes the fn's " n " argument(s), in the fn's order, had "
           (pr-str (second w)))))

(defn- by->when
  "A graph's edges with each :by, the roles that may take the step, made
  a guard: the step is taken when the acting argument -- the one of the
  graph's :actors type -- has one of the roles, and joined by `and` with
  the edge's own :when.  Anyone else is refused, as by any guard."
  [where {:keys [actors edges] :as m}]
  (assoc m :edges
         (into {} (for [[from es] edges]
                    [from (into {} (for [[k tos0] es]
                                     [k (if (vector? tos0)
                                          (mapv #(get-in (by->when where (assoc m :edges {from {k %}})) [:edges from k]) tos0)
                                          (let [tos tos0]
                                          (if-not (and (map? tos) (contains? tos :by))
                                          tos
                                          (let [edge (str where ": the edge " (pr-str from) " " (pr-str k))
                                                by (:by tos)
                                                _ (when-not (map? actors)
                                                    (fail! edge ": :by needs the graph's :actors, {:type T :role :key},"
                                                           " to know which argument acts"))
                                                _ (when-not (and (set? by) (seq by))
                                                    (fail! edge ": :by is a set of the roles that may take the step, had "
                                                           (pr-str by)))
                                                args (rest k)
                                                order (if (some #{'_} args) (vec args) (into ['_] args))
                                                i (first (keep-indexed #(when (= (:type actors) %2) %1) order))
                                                _ (when-not i
                                                    (fail! edge " takes no " (:type actors) ", so no one is there to act;"
                                                           " give it one, or drop :by"))
                                                ps (vec (for [j (range (count order))] (symbol (str "by%" j))))
                                                who (nth ps i)
                                                test (list 'contains? by (if (:role actors) (list 'get who (:role actors)) who))
                                                w (:when tos)
                                                _ (when (contains? tos :when) (when-shape! edge w (count order)))
                                                ;; the edge's own test, in the joined fn's
                                                ;; names, its clauses kept as clauses
                                                own (when w (guard-of w ps))
                                                body (cond (nil? w) test
                                                           (and (seq? own) (= 'and (first own))) (concat own [test])
                                                           :else (list 'and own test))]
                                            (cond-> (assoc tos :when (list 'fn ps body))
                                              w (assoc :own-when w))))))]))]))))

(def ^:private projections
  "clojure.core fns an edge may use to take a state out of a tuple state:
  the tuple element's position, from its arity."
  {'first (constantly 0), 'second (constantly 1), 'last dec})

(defmacro graph
  "The problem's state graph.  Its states are types, most often
  refinements; its edges are fns, each from a state to the states its
  result may be in:

    (graph signal
      {:start  [:green [:Green 0]]
       :states {:green Green, :yellow Yellow, :red Red}
       :edges  {:green  {[tick] #{:green :yellow}}
                :yellow {[tick] #{:yellow :red}}
                :red    {[tick] #{:red :green}}}
       :before [[:yellow :red]]})

  An edge's key is the fn and the types of any arguments after the
  state: [move Key] is (move state key) for every Key.  Each edge is an
  obligation, checked and proved like a law: the fn takes every value of
  its state to a value of one of the states named.  The fn's `ann` must
  fit: it takes the state's base type, and returns the targets' base
  type.  :start is a state, or [state value] with a value in it.
  :never [a b], :before [a b] and :final are rules of the graph itself,
  as for `machine`; with every edge proved they hold for every run.

  An edge on a record state may give :changes [:k ...], alone or beside
  :when: the step changes only those keys, and keeps every other one.

  :tested {state \"why\"} lets the edges out of state off proof, as a law's
  {:require :tested :because \"why\"} does: their obligations are tested,
  and every report shows the reason.

  :witnesses {[from to] [value arg ...]} gives the step from state from to
  state to an example: a value of from and the edge fn's other arguments
  that land in to.  The check tries it before any generated one, for a
  step no generated value takes -- one whose arguments must agree with
  each other, as a reply must carry the alias its request made.

  :actors {:type User :role :role} names the argument that acts, by its
  type, and the key of it that holds its role; an edge's :by #{:owner}
  then says which roles may take the step.  :by is a guard: anyone else
  is refused, and the state stays as it was."
  [nm m0]
  (let [where (str "`graph " nm "`")
        ;; a :when that names a spec fn of the edge fn's arguments, as
        ;; :when may-borrow?, is that fn's own (fn [params] body), so the
        ;; graph and the laws share one guard and its clauses are each seen
        named-when (fn [k w]
                     (let [n (inc (count (remove #{'_} (rest k))))
                           [ps body] (get (one-line-helpers (ns-name *ns*)) w)]
                       (cond
                         (and ps (= n (count ps))) (list 'fn ps body)
                         ps (fail! where ": the edge " (pr-str k) " names :when " w ", which takes "
                                   (count ps) " argument(s); the step's fn takes " n)
                         ;; not the spec's: the shape check says what a :when is
                         :else w)))
        m0 (if (and (map? m0) (map? (:edges m0)))
             (update m0 :edges
                     (fn [es] (into {} (for [[from e] es]
                                         [from (if (map? e)
                                                 (into {} (for [[k tos] e
                                                                :let [named (fn [c] (if (and (map? c) (symbol? (:when c)))
                                                                                      (update c :when #(named-when k %))
                                                                                      c))]]
                                                            [k (if (vector? tos) (mapv named tos) (named tos))]))
                                                 e)]))))
             m0)
        m (if (and (map? m0) (map? (:edges m0)) (every? map? (vals (:edges m0))))
            (by->when where m0)
            m0)]
    (when-not (simple-sym? nm)
      (fail! "a `graph` name must be a simple symbol: `" (pr-str nm) "`"))
    (when-not (and (map? m) (map? (:states m)) (map? (:edges m)))
      (fail! where " needs a map with :states (state -> type) and :edges"))
    (when-let [bad (seq (remove graph-keys (keys m)))]
      (fail! where " has unknown keys: " (pr-str bad) "; it takes " (pr-str (sort graph-keys))))
    (when-let [a (:actors m)]
      (when-not (and (map? a) (symbol? (:type a)) (every? #{:type :role} (keys a))
                     (or (nil? (:role a)) (keyword? (:role a))))
        (fail! where ": :actors is {:type T :role :key}: the type of the argument that acts, and the key"
               " of it that holds the role (none when the value is the role), had " (pr-str a))))
    (when-let [md (:model m)]
      (when-not (and (map? md) (simple-sym? (:view md)) (map? (:steps md))
                     (every? (fn [[k v]] (and (simple-sym? k) (simple-sym? v))) (:steps md))
                     (every? #{:view :steps} (keys md)))
        (fail! where ": :model is {:view f :steps {step model-step ...}}: the spec's fn from a state to"
               " its model, and for each step fn of the graph the spec's fn that does the same to the"
               " model, taking the model and the step's other arguments; had " (pr-str md))))
    (when (and (contains? m :runs) (not (pos-int? (:runs m))))
      (fail! where ": :runs is how many runs to walk from :start, a positive integer, had "
             (pr-str (:runs m))))
    (let [states (set (keys (:states m)))
          known! (fn [what s] (when-not (contains? states s)
                                (fail! where ": " what " names " (pr-str s) ", which is not a state")))]
      (when-let [w (:witnesses m)]
        (when-not (map? w)
          (fail! where ": :witnesses is {[from to] [value arg ...]}, had " (pr-str w)))
        (doseq [[k v] w]
          (when-not (and (vector? k) (= 2 (count k)) (vector? v))
            (fail! where ": a witness is [from to] [value arg ...], had " (pr-str k) " " (pr-str v)))
          (known! ":witnesses" (first k))
          (known! ":witnesses" (second k))))
      (when-let [t (:tested m)]
        (when-not (map? t)
          (fail! where ": :tested is {state \"why it cannot be proved yet\"}, had " (pr-str t)))
        (doseq [[st why] t]
          (known! ":tested" st)
          (when-not (and (string? why) (not (str/blank? why)))
            (fail! where ": :tested " (pr-str st) " needs the reason its edges cannot be proved yet"))))
      (doseq [[from es] (:edges m)]
        (known! "an edge" from)
        (when-not (map? es)
          (fail! where ": the edges from " (pr-str from) " must be a map of [fn ArgType ...] to states"))
        (doseq [[k tos0] es
                ;; a step of cases, each a map with its own :when
                :let [_ (when (vector? tos0)
                          (when-not (and (seq tos0)
                                         (every? #(and (map? %) (contains? % :when) (contains? % :to)
                                                       (not (contains? % :else)))
                                                 tos0))
                            (fail! where ": the edge " (pr-str from) " " (pr-str k) " gives a vector of cases;"
                                   " each is a map with its own :when and :to, and no :else -- where no case"
                                   " holds the step is refused and keeps the state")))]
                tos (if (vector? tos0) tos0 [tos0])]
          (when-not (and (vector? k) (simple-sym? (first k)))
            (fail! where ": an edge from " (pr-str from) " is keyed [fn ArgType ...], had " (pr-str k)))
          (when (< 1 (count (filter #{'_} (rest k))))
            (fail! where ": the edge " (pr-str from) " " (pr-str k) " marks the state with `_` more than once"))
          (when (and (contains? projections (first k)) (next k))
            (fail! where ": the edge " (pr-str from) " " (pr-str k) " -- `" (first k)
                   "` takes the state alone, a " (pr-str (get (:states m) from))))
          (when (map? tos)
            (let [edge (str where ": the edge " (pr-str from) " " (pr-str k))
                  {w :when el :else ch :changes} tos
                  n (inc (count (remove #{'_} (rest k))))]
              (when-let [bad (seq (remove #{:to :when :else :changes :by :own-when} (keys tos)))]
                (fail! edge " has unknown keys " (pr-str bad) "; an edge map takes :to, :when, :else, :changes and :by"))
              (when (contains? tos :changes)
                (when-not (and (vector? ch) (seq ch)
                               (every? #(or (keyword? %)
                                            (and (vector? %) (keyword? (first %))
                                                 (every? (fn [x] (or (keyword? x) (number? x) (string? x)
                                                                     (and (seq? x) (= 'arg (first x)) (= 2 (count x))
                                                                          (integer? (second x)) (<= 1 (second x) (dec n)))))
                                                         (rest %))))
                                       ch))
                  (fail! edge ": :changes is a vector of the keys the step may change, or of paths into the"
                         " state such as [:copies (arg i)], where (arg i) is the step's i-th argument after the"
                         " state, 1 to " (dec n) "; had " (pr-str ch))))
              (when (or (contains? tos :when) (not (contains? tos :changes)))
                (when-shape! edge w n))
              (when (and el (not (contains? tos :when)))
                (fail! edge ": :else says what a refused step does, so it needs :when"))
              (when-not (or (nil? el) (= :keep el) (contains? states el))
                (fail! edge ": :else is :keep, the state unchanged when the guard fails, or a state, had "
                       (pr-str el)))))
          (when-not (let [tos (if (map? tos) (:to tos) tos)] (and (coll? tos) (not (map? tos)) (seq tos)))
            (fail! where ": the edge " (pr-str from) " " (pr-str k) " needs a set of target states"))
          (doseq [t (if (map? tos) (:to tos) tos)]
            (when-not (contains? states t)
              (fail! where ": the edge from " (pr-str from) " names " (pr-str t) ", which is not a state")))))
      (when-let [st (:start m)]
        (known! ":start" (if (vector? st) (first st) st)))
      (doseq [[a b] (concat (:never m) (:before m))] (known! "a rule" a) (known! "a rule" b))
      (doseq [f (:final m)] (known! ":final" f)))
    `(-register! '~(ns-name *ns*) :graph '~[nm m])))

(def ^:private strategies #{:symbolic :induction :rewriting})

(defmacro proof-of
  "Name the spec this namespace proves.  A proof namespace holds what the
  prover needs and the spec should not say: lemmas and hints.  The agent
  writes it; the spec stays the contract.  writ finds it by name, my.sort-proof
  for my.sort-spec, or by check's :proof option."
  [spec-ns]
  (when-not (simple-sym? spec-ns)
    (fail! "`proof-of` names a spec namespace symbol, had: `" (pr-str spec-ns) "`"))
  `(-register-proof! '~(ns-name *ns*) :proves '~spec-ns))

(defmacro lemma
  "A law about the code that helps prove the spec's laws:

    (lemma insert-keeps-sorted
      (forall [x Nat, xs (List Nat)] (=> (ascending? xs) (ascending? (insert x xs)))))

  It is tested and must be proved, like a law the spec demands proof of;
  once proved, the spec's laws may cite it.  It is not part of the spec:
  it counts toward no law, and no stand-in is judged by it."
  [nm prop]
  (when-not (simple-sym? nm)
    (fail! "a `lemma` name must be a simple symbol: `" (pr-str nm) "`"))
  `(-register-proof! '~(ns-name *ns*) :lemma '~{:name nm :prop prop}))

(defmacro hint
  "Tell the prover how to prove one of the spec's laws (or a lemma):

    (hint sorted {:induct xs :use [insert-keeps-sorted]})

  :induct, the variable to try induction on first; :vary, the other
  variables the induction hypothesis holds at every value of, not just
  the goal's -- an accumulator a fold passes on, say; :use, the only
  lemmas and laws the proof may cite; :strategy, one of :symbolic (run
  the code on symbolic values), :induction or :rewriting; :fuel, the
  rewrites one attempt may make.  A hint only steers the search: a proof it finds is
  checked like any other."
  [law-name m]
  (let [where (str "`hint " law-name "`")]
    (when-not (simple-sym? law-name)
      (fail! "a `hint` names a law by its simple symbol, had: `" (pr-str law-name) "`"))
    (when-not (map? m)
      (fail! where " takes a map: {:induct x :vary [y] :use [lemma ...] :strategy :symbolic :fuel n}"))
    (when-let [bad (seq (remove #{:induct :vary :use :strategy :fuel} (keys m)))]
      (fail! where " has unknown keys: " (pr-str bad) "; it takes :induct :vary :use :strategy :fuel"))
    (when (and (contains? m :strategy) (not (contains? strategies (:strategy m))))
      (fail! where ": :strategy must be one of " (pr-str (sort strategies)) ", had " (pr-str (:strategy m))))
    (when (and (contains? m :induct) (not (simple-sym? (:induct m))))
      (fail! where ": :induct names a variable of the law"))
    (when (and (contains? m :vary) (not (and (vector? (:vary m)) (every? simple-sym? (:vary m)))))
      (fail! where ": :vary is a vector of variables of the law"))
    (when (and (contains? m :vary) (contains? (set (:vary m)) (:induct m)))
      (fail! where ": the variable of the induction cannot vary in its own hypothesis"))
    (when (and (contains? m :use) (not (and (vector? (:use m)) (every? simple-sym? (:use m)))))
      (fail! where ": :use is a vector of lemma and law names"))
    (when (and (contains? m :fuel) (not (pos-int? (:fuel m))))
      (fail! where ": :fuel is a positive integer"))
    `(-register-proof! '~(ns-name *ns*) :hint '~[law-name m])))

(defn- law-opts!
  "Check a law's options: :require sets the evidence it needs, and
  :require :tested needs :because, the reason it cannot be proved yet."
  [nm opts]
  (let [where (str "`law " nm "`")]
    (when-let [bad (seq (remove #{:require :because} (keys opts)))]
      (fail! where " has unknown options: " (pr-str bad) "; it takes :require and :because"))
    (when (contains? opts :require) (check-level! where (:require opts)))
    (when (and (= :tested (:require opts)) (not (and (string? (:because opts))
                                                     (not (str/blank? (:because opts))))))
      (fail! where " is let off proof with {:require :tested}, so it needs :because, a "
             "string saying why it cannot be proved yet"))
    (when (and (contains? opts :because) (not= :tested (:require opts)))
      (fail! where ": :because goes with :require :tested, the reason a law is only tested"))
    opts))

(def ^{:arglists '([a b])} same
  "= with NaN the same as NaN, at any depth, so that every value is the
  same as itself.  A law over a ! type -- Any!, Double!, whose values
  take in NaN -- compares with same where it means the same value; = is
  false of two NaNs, so a law that compares them with = is false there.
  The prover takes same to be what it is: reflexive, and = on values that
  hold no NaN."
  pterm/same)

(defmacro throws?
  "In a law: does evaluating expr throw?  A lazy seq it returns, and any
  inside what it returns, is realised first, since that is where its
  elements are computed.  An
  error writ raises -- an argument or a result that breaks a signature --
  is rethrown, not counted: it says the law misuses the code, not that
  the code throws.

    (law past-the-end-throws
      (forall [v (Vec Nat), i Nat] (= (throws? (at v i)) (>= i (count v)))))"
  [expr]
  `(try (let [v# ~expr] (walk/postwalk identity v#) false)
        (catch Throwable e#
          (if (:writ/error (ex-data e#)) (throw e#) true))))

(defmacro law
  "State a law about the target's behaviour.

    (law sorted (forall [xs (List Nat)] (ascending? (isort xs))))
    (law sorted {:require :proved} (forall ...))   ; this law must be proved
    (law fast {:require :tested :because \"...\"} (forall ...))

  The options map is optional.  It overrides the spec's :require for this
  one law; letting a law off proof takes a reason, shown in every report."
  ([nm prop] `(law ~nm {} ~prop))
  ([nm opts prop]
   (when-not (simple-sym? nm)
     (fail! "a `law` name must be a simple symbol: `" (pr-str nm) "`"))
   (when-not (map? opts)
     (fail! "`law " nm "` takes (law name prop) or (law name {options} prop), had a "
            (pr-str opts) " where the options go"))
   (law-opts! nm opts)
   `(-register! '~(ns-name *ns*) :law '~(cond-> {:name nm :prop prop}
                                          (seq opts) (assoc :opts opts)))))

(defmacro example
  "An example of what fn f returns at given arguments:

    (example price [6000] 12000)

  It is checked as a law, (= (price 6000) 12000), named example:price:N.
  It also asks of the other laws that they pin f down there: a stand-in
  that agrees with f everywhere but at the example, where it answers
  otherwise, must break one of them, or the report says no law says what
  f returns there."
  [f args out]
  (when-not (and (simple-sym? f) (vector? args))
    (fail! "`example` is (example f [arg ...] result), had " (pr-str (list 'example f args out))))
  (let [spec-ns (ns-name *ns*)
        n (inc (count (filter #(and (:example %) (= f (:fn (:example %))))
                              (:laws (get @registry spec-ns)))))]
    `(-register! '~spec-ns :law '~{:name (symbol (str "example:" f ":" n))
                                   :prop (list '= (list* f args) out)
                                   :example {:fn f :args args :out out}})))

;; --- propositions ----------------------------------------------------------

(defn- head? [f s]
  (and (seq? f) (symbol? (first f)) (= s (name (first f)))))

(defn- quant? [p] (or (head? p "forall") (head? p "exists")))

(defn desugar
  "Multi-binder quantifiers, (forall [x A, y B] P), into nested ones, the
  single-binder shape writ.law reads."
  [p]
  (cond
    (quant? p)
    (let [[q bs body & more] p]
      (when-not (and (vector? bs) (seq bs) (even? (count bs))
                     (every? simple-sym? (take-nth 2 bs)) (some? body) (empty? more))
        (fail! "`" (name q) "` must be (" (name q) " [x T ...] P), had: " (pr-str p)))
      (reduce (fn [acc [x t]] (list (symbol (name q)) [x t] acc))
              (desugar body)
              (reverse (partition 2 bs))))
    (or (head? p "and") (head? p "=>"))
    (cons (first p) (map desugar (rest p)))
    :else p))

;; --- an integer between bounds ----------------------------------------------------

(def ^:private binding-heads
  '#{let let* fn fn* loop loop* for doseq letfn binding when-let if-let when-some if-some
     as-> cond-> cond->> some-> some->> case condp})

(defn- inline-helpers
  "form with each call of a spec helper -- a defn of one expression that
  binds no names of its own -- replaced by its body at the call's
  arguments, to depth 4.  helpers: name -> [params body]."
  [form helpers]
  (let [plain? (fn [[_ body]] (not-any? #(and (seq? %) (contains? binding-heads (first %)))
                                        (tree-seq coll? seq body)))
        helpers (into {} (filter (comp plain? val)) helpers)]
    (letfn [(inl [f depth]
              (cond
                (and (seq? f) (contains? helpers (first f)) (pos? depth)
                     (= (count (first (get helpers (first f)))) (count (rest f))))
                (let [[params body] (get helpers (first f))]
                  (inl (walk/postwalk-replace (zipmap params (map #(inl % depth) (rest f))) body)
                       (dec depth)))
                (seq? f) (apply list (map #(inl % depth) f))
                (vector? f) (mapv #(inl % depth) f)
                :else f))]
      (inl form 4))))

(defn- bounds-of
  "An atom of an integer t's range as a vector of [:lo L k] (L + k <= t),
  [:up U k] (t + k <= U) and [:fact f] (a part without t); nil when t
  appears some other way."
  [a t]
  (let [has-t? #(some #{t} (tree-seq coll? seq %))
        pair (fn [op l r]
               (let [k (if (= '< op) 1 0)]
                 (cond
                   (not (or (has-t? l) (has-t? r))) [[:fact (list op l r)]]
                   (and (= t l) (not (has-t? r))) [[:up r k]]
                   (and (= t r) (not (has-t? l))) [[:lo l k]])))]
    (cond
      (not (has-t? a)) [[:fact a]]
      (not (and (seq? a) (symbol? (first a)))) nil
      :else
      (let [op (symbol (name (first a))), xs (vec (rest a))]
        (case op
          (< <=) (when (>= (count xs) 2)
                   (let [ps (map #(pair op %1 %2) xs (rest xs))]
                     (when (every? some? ps) (vec (apply concat ps)))))
          (> >=) (bounds-of (apply list (if (= '> op) '< '<=) (rseq xs)) t)
          = (when (= 2 (count xs))
              (let [[l r] xs]
                (cond (and (= t l) (not (has-t? r))) [[:lo r 0] [:up r 0]]
                      (and (= t r) (not (has-t? l))) [[:lo l 0] [:up l 0]])))
          nil)))))

(defn- eliminate-exists
  "Each (exists [t Nat] P), or over Int, whose body -- its spec helpers
  inlined -- is a conjunction of bounds on t and facts without t, read as
  the facts and each lower bound at most each upper one: over the
  integers there is such a t exactly then.  The prover reads that, and a
  test evaluates it exactly, where sampling t could miss the one value.
  An exists of any other shape is left as it is."
  [p helpers]
  (cond
    (head? p "exists")
    (let [[q [t ty] body] p
          body (eliminate-exists body helpers)
          tn (when (symbol? ty) (symbol (name ty)))
          flat (fn flat [f] (if (head? f "and") (mapcat flat (rest f)) [f]))
          parts (when (contains? '#{Nat Int} tn)
                  (map #(bounds-of % t) (flat (inline-helpers body helpers))))]
      (if (or (nil? parts) (some nil? parts))
        (list q [t ty] body)
        (let [xs (apply concat parts)
              facts (keep #(when (= :fact (first %)) (second %)) xs)
              los (cond-> (filter #(= :lo (first %)) xs) (= 'Nat tn) (conj [:lo 0 0]))
              ups (filter #(= :up (first %)) xs)
              meets (for [[_ l k1] los, [_ u k2] ups
                          :let [k (+ k1 k2)]]
                      (list '<= (if (zero? k) l (list '+ l k)) u))
              cs (distinct (concat facts meets))]
          (case (count cs) 0 true 1 (first cs) (cons 'and cs)))))
    (head? p "forall") (let [[q b body] p] (list q b (eliminate-exists body helpers)))
    (or (head? p "and") (head? p "=>")) (cons (first p) (map #(eliminate-exists % helpers) (rest p)))
    :else p))

(defn- auto-proof
  "The proof term a law's shape dictates, for writ.law/prove: refl for an
  equality, pair for a conjunction, fn for a universal or implication (a
  conclusion equal to its hypothesis cites it).  nil when the shape has no
  static proof (a predicate, an existential)."
  [p]
  (cond
    (head? p "=") 'refl
    (head? p "and") (let [ts (map auto-proof (rest p))]
                      (when (every? some? ts) (cons 'pair ts)))
    (head? p "=>") (let [h (gensym "h")]
                     (if (= (nth p 1) (nth p 2))
                       (list 'fn [h] h)
                       (when-let [t (auto-proof (nth p 2))] (list 'fn [h] t))))
    (head? p "forall") (let [[_ [x _] body] p]
                         (when-let [t (auto-proof body)] (list 'fn [x] t)))
    :else nil))

(defn- try-prove
  "true when writ.norm discharges `p` statically."
  [p tenv opaque numeric-fns]
  (when-let [t (auto-proof p)]
    (try
      (binding [norm/*opaque* opaque
                norm/*numeric-fns* numeric-fns]
        (lw/prove p t {:laws {} :hyps {} :numeric #{} :tenv tenv}))
      true
      (catch Throwable _ false))))

;; --- types at runtime --------------------------------------------------------

(defn- plain [t]
  (cond (symbol? t) (symbol (name t))
        (seq? t) (apply list (map plain t))
        (map? t) (update-vals t plain)
        :else t))

(defn- opt-type? [t] (and (seq? t) (= 'Opt (first t))))

(defn- subst [t m]
  (cond (symbol? t) (get m t t)
        (seq? t) (apply list (map #(subst % m) t))
        :else t))

(defn- ctor-info
  "[ctor-sym {:fields [types]}] for a data value's constructor, with the
  type's parameters instantiated at `args`."
  [decl args c]
  (when-let [info (get (:ctors decl) c)]
    (let [m (zipmap (:params decl) args)]
      {:fields (mapv #(subst % m) (:fields info))})))

(defn- data-decl [t tenv]
  (let [h (if (seq? t) (first t) t)]
    (when-let [d (get tenv h)]
      (when-not (:tvar d) [d (if (seq? t) (vec (rest t)) [])]))))

(declare conforms?)

(defn- conforms-data?
  "A data value is a vector headed by its constructor keyword, one element
  per field: [:Leaf], [:Node l v r]."
  [d args v tenv]
  (let [info (when (and (vector? v) (keyword? (first v)))
               (ctor-info d args (symbol (name (first v)))))]
    (boolean
      (and info
           (= (count (:fields info)) (dec (count v)))
           (every? true? (map #(conforms? %1 %2 tenv) (:fields info) (rest v)))))))

(defn unique-by?
  "Do no two of xs share (f x)?  True of none or one."
  [f xs]
  (let [ks (map f xs)] (= (count ks) (count (distinct ks)))))

(defn indexed?
  "Is db a map of records, each kept under its field k, no two sharing a
  field named in unique?  What an (Index :k R :unique [...]) says beyond
  its records' own type; a refinement of an Index checks it in its
  predicate, so a step that lands in one must keep it."
  [k unique db]
  (and (map? db)
       (every? (fn [[i x]] (= i (get x k))) db)
       (every? #(unique-by? % (vals db)) unique)))

(defn- refinement [t tenv]
  (when (symbol? t) (get-in tenv [::refines (symbol (name t))])))

(defn conforms?
  "Does value `v` fit type `t`?  Unknown types and type variables pass."
  [t v tenv]
  (let [t (plain t)]
    (cond
      (refinement t tenv)
      (let [{:keys [base pred]} (refinement t tenv)]
        (boolean (and (conforms? base v tenv) (pred v))))

      (symbol? t)
      (case t
        Nat (nat-int? v)
        Int (int? v)
        Bool (boolean? v)
        String (string? v)
        Char (char? v)
        Keyword (keyword? v)
        Symbol (symbol? v)
        (Float Double Float! Double!) (number? v)
        Unit (nil? v)
        (Any Any!) true
        (if-let [[d args] (data-decl t tenv)]
          (conforms-data? d args v tenv)
          true))

      ;; a record: each key of its own type; an (Opt T) key may be absent,
      ;; and keys it does not name may be there too
      (map? t)
      (and (map? v)
           (every? (fn [[k kt]]
                     (if (contains? v k)
                       (conforms? kt (get v k) tenv)
                       (opt-type? kt)))
                   t))

      (and (kind/index-type? t) (not (data-decl t tenv)))
      (let [{k :key r :of u :unique} (kind/index-parts t)]
        (and (map? v)
             (every? (fn [[i x]] (and (conforms? r x tenv) (= i (get x k)))) v)
             (every? #(unique-by? % (vals v)) u)))

      (seq? t)
      (let [[h & as] t]
        (case h
          Opt (or (nil? v) (conforms? (first as) v tenv))
          List (and (or (nil? v) (sequential? v)) (every? #(conforms? (first as) % tenv) v))
          Vec (and (vector? v) (every? #(conforms? (first as) % tenv) v))
          Set (and (set? v) (every? #(conforms? (first as) % tenv) v))
          Map (and (map? v) (every? (fn [[k x]] (and (conforms? (first as) k tenv)
                                                     (conforms? (second as) x tenv))) v))
          (Tuple &) (and (vector? v) (= (count as) (count v))
                         (every? true? (map #(conforms? %1 %2 tenv) as v)))
          -> (ifn? v)
          (if-let [[d args] (data-decl t tenv)]
            (conforms-data? d args v tenv)
            true)))

      :else true)))

;; --- generators ---------------------------------------------------------------
;; Values come from test.check generators built from the spec's types, so a
;; failure shrinks through test.check's rose trees and a seed replays it.

(defn- mentions? [t nm]
  (boolean (some #{nm} (tree-seq #(or (seq? %) (map? %)) #(if (map? %) (vals %) (seq %))
                                 (if (or (seq? t) (map? t)) t (list t))))))

(declare type->gen)

(defn- int-rose
  "n with the shrinks test.check gives an integer: 0 first, then halfway
  back to n, and so on, each shrinking again."
  [n]
  (rose/make-rose n (map (fn [d] (int-rose (- n d)))
                         (take-while #(not= 0 %) (iterate #(quot % 2) n)))))

(defn- seed-gen
  "One of a code's literals.  gen/elements shrinks only to the literals
  listed before it, so a failing 251 stays near 251; an integer literal
  here shrinks as any integer does, toward the smallest that still fails."
  [seeds]
  (gen/gen-fmap (fn [r] (rose/bind r #(if (integer? %) (int-rose %) (rose/pure %))))
                (gen/elements seeds)))

(defn- data-gen
  "A data value is a vector headed by its constructor keyword: [:Leaf],
  [:Node l v r].  Recursive fields get half the size, and at size 0 only
  the constructors that do not recurse are picked, so values stay finite."
  [d args nm tenv]
  (let [ctors (sort-by str (keys (:ctors d)))
        fields (fn [c] (:fields (ctor-info d args c)))
        base (remove (fn [c] (some #(mentions? % nm) (fields c))) ctors)
        ctor-gen (fn [c size]
                   (let [k (keyword (name c))
                         fs (fields c)]
                     (if (empty? fs)
                       (gen/return [k])
                       (gen/fmap #(into [k] %)
                                 (apply gen/tuple
                                        (map #(gen/resize (quot size 2) (type->gen % tenv)) fs))))))]
    (gen/sized (fn [size]
                 (let [pick (if (and (<= size 1) (seq base)) base ctors)]
                   (gen/one-of (mapv #(ctor-gen % size) pick)))))))

(def ^:private any-string
  "Mostly words, but now and then printable ASCII with tabs and newlines,
  so code that trims, splits or escapes meets what it is there for, and
  now and then one of a few short strings, so two strings generated apart
  are sometimes the same, as two small integers often are: an email
  already taken, a name looked up."
  (gen/frequency [[3 gen/string-alphanumeric]
                  [1 (gen/elements ["" "a" "b" "ab"])]
                  [1 (gen/fmap #(apply str %)
                               (gen/vector (gen/frequency [[8 gen/char-ascii]
                                                           [1 (gen/elements [\tab \newline])]])))]]))

(deftype GenFn [seed results calls]
  clojure.lang.IFn
  (invoke [this] (.applyTo this nil))
  (invoke [this a] (.applyTo this (list a)))
  (invoke [this a b] (.applyTo this (list a b)))
  (invoke [this a b c] (.applyTo this (list a b c)))
  (invoke [this a b c d] (.applyTo this (list a b c d)))
  (invoke [this a b c d e] (.applyTo this (list a b c d e)))
  (invoke [this a b c d e f] (.applyTo this (list a b c d e f)))
  (invoke [this a b c d e f g] (.applyTo this (list a b c d e f g)))
  (invoke [this a b c d e f g h] (.applyTo this (list a b c d e f g h)))
  (applyTo [_ args]
    (let [k (if (= 1 (count args)) (first args) (vec args))
          ;; a fn's hash is its identity, which a replay does not share,
          ;; so a fn among the arguments counts as any fn: the answer is
          ;; still the same for the same arguments
          stable (walk/postwalk #(if (and (ifn? %) (not (coll? %)) (not (keyword? %)) (not (symbol? %))) ::fn %) k)
          r (gen/generate results 20 (hash [seed stable]))]
      (swap! calls assoc k r)
      r)))

(defmethod print-method GenFn [g ^java.io.Writer w]
  (.write w (str "(fn {" (str/join ", " (for [[k v] (sort-by (comp pr-str key) @(.-calls g))]
                                          (str (pr-str k) " " (pr-str v))))
                 "})")))

(defn- fn-gen
  "Pure fns returning values of result generator g: each answers the same
  arguments the same way, as a table drawn once per argument from its own
  seed.  One prints as the calls it answered."
  [g]
  (gen/fmap (fn [seed] (GenFn. seed g (atom {}))) (gen/choose 0 1000000)))

(def ^:private finite-double
  (gen/double* {:NaN? false :infinite? false}))

(defn- domain-size
  "How many values type t has, when it is a handful: a Bool, a refinement
  of an integer over a finite range, an enumeration.  nil for a type with
  many.  A refinement of a finite type has at most its base's values."
  [t tenv]
  (let [t (plain t)]
    (cond
      (= 'Bool t) 2
      (= 'Unit t) 1
      (refinement t tenv) (let [r (refinement t tenv)]
                            (or (some-> (:window r) count)
                                (when-not (:window r) (domain-size (:base r) tenv))))
      (and (symbol? t) (data-decl t tenv))
      (let [[d args] (data-decl t tenv)
            cs (keys (:ctors d))]
        (when (and (seq cs) (every? #(empty? (:fields (ctor-info d args %))) cs))
          (count cs)))
      :else nil)))

(defn- record-field-type
  "The type of field k of a record type r, or of the record a refinement
  refines."
  [r k tenv]
  (let [r (plain r)]
    (cond (map? r) (get r k)
          (refinement r tenv) (record-field-type (:base (refinement r tenv)) k tenv)
          :else nil)))

(defn- collection-type?
  "Is t a collection whose length its generator chooses from the size?"
  [t tenv]
  (let [t (plain t)]
    (or (and (seq? t) (contains? '#{List Vec Set Map} (first t)))
        (and (kind/index-type? t) (not (data-decl t tenv))))))

(defn- element-gen
  "The generator of a collection's elements of type t.  An element that is
  itself a collection is at most the square root of the size long, so a
  map of vectors stays near the size rather than its square; the values
  inside keep the whole size, so a number in a nested vector is as large
  as one anywhere.  A collection of a type with few values keeps the
  whole size."
  [t tenv]
  (let [tenv (dissoc tenv ::nested)
        t* (plain t)
        ;; a vector of a few values, such as a queue of members, keeps the
        ;; whole size: its elements cost little, and its repeats are the point
        few? (and (seq? t*) (contains? '#{List Vec Set} (first t*)) (domain-size (second t*) tenv))]
    (type->gen t (cond-> tenv (and (collection-type? t tenv) (not few?)) (assoc ::nested true)))))

(defn- max-length
  "The longest a collection may be at size s: s, its root when the
  collection is inside another, and no more than cap."
  [tenv s cap]
  (cond-> (if (::nested tenv) (long (Math/sqrt s)) s)
    cap (min cap)))

(defn- capped-vector
  "A vector of g, no longer than max-length allows."
  [g tenv cap]
  (if (or cap (::nested tenv))
    (gen/sized (fn [s] (gen/vector g 0 (max-length tenv s cap))))
    (gen/vector g)))

(defn- keys-first
  "A generator of [[key value] ...] with distinct keys: the keys drawn as
  a vector the size long, as many as a collection's entries, and a value
  made for each distinct one.  As many keys come out as when whole
  entries are drawn and those that share a key dropped, but no value is
  made to be dropped: a map over three titles draws its values three
  times, not fifty."
  [kg vg tenv]
  (gen/sized
    (fn [s]
      (gen/bind (gen/vector kg 0 (max-length tenv s nil))
                (fn [ks]
                  (let [ks (vec (distinct ks))]
                    (if (empty? ks)
                      (gen/return [])
                      (gen/fmap #(mapv vector ks %) (apply gen/tuple (repeat (count ks) vg))))))))))

(defn- index-records
  "Records for an index keyed by k.  When its key type has few values,
  the keys are drawn first and a record made for each, its key set: a
  record that would land on a key already taken is never made."
  [r k tenv]
  (if-let [kt (when (domain-size (record-field-type r k tenv) tenv) (record-field-type r k tenv))]
    (gen/fmap (fn [kvs] (into [] (comp (map (fn [[kk rec]] (if (map? rec) (assoc rec k kk) rec)))
                                       (filter #(conforms? r % tenv)))
                              kvs))
              (keys-first (type->gen kt tenv) (element-gen r tenv) tenv))
    (capped-vector (element-gen r tenv) tenv nil)))

(defn type->gen
  "The test.check generator for values of type `t`."
  [t tenv]
  (let [t (plain t)]
    (cond
      (refinement t tenv) (:gen (refinement t tenv))

      (and (symbol? t) (seq (get-in tenv [::bias t])))
      (gen/frequency [[1 (type->gen t (update tenv ::bias dissoc t))]
                      [3 (gen/elements (vec (get-in tenv [::bias t])))]])

      ;; a law's own values: now and then, one of the scalars the target's
      ;; code mentions, since the code branches on exactly those
      (and (symbol? t) (seq (get-in tenv [::seeds t])))
      (let [seeds (vec (get-in tenv [::seeds t]))
            plain (type->gen t (update tenv ::seeds dissoc t))
            tags (vec (filter keyword? seeds))]
        (gen/frequency
          (cond-> [[3 plain] [1 (seed-gen seeds)]]
            ;; code that dispatches on a tag, (case (first ret) :reply ...),
            ;; wants tagged vectors: one of its keywords, then a few values
            (and (= 'Any t) (seq tags))
            (conj [2 (gen/fmap (fn [[k xs]] (into [k] xs))
                               (gen/tuple (gen/elements tags)
                                          (gen/vector (gen/one-of [plain (seed-gen seeds)]) 0 3)))]))))

      (symbol? t)
      (case t
        Nat gen/nat
        Int gen/small-integer
        Bool gen/boolean
        Char gen/char-alpha
        String any-string
        Keyword gen/keyword
        Symbol gen/symbol
        (Float Double) finite-double
        ;; a ! type's values take in NaN, alone and inside a vector
        (Float! Double!) (gen/frequency [[4 finite-double] [1 (gen/return ##NaN)]])
        Unit (gen/return nil)
        Any (gen/one-of [gen/small-integer gen/string-alphanumeric gen/keyword
                         (gen/vector gen/small-integer)])
        Any! (gen/one-of [gen/small-integer gen/string-alphanumeric gen/keyword
                          (gen/return ##NaN) finite-double
                          (gen/vector (gen/one-of [gen/small-integer (gen/return ##NaN)]))])
        (if-let [[d args] (data-decl t tenv)]
          (data-gen d args t tenv)
          (fail! "cannot generate values of type `" t "`: declare it with `data`")))

      ;; a record: a map with its keys, an (Opt T) key now absent, now nil,
      ;; now set
      (map? t)
      (let [ks (vec (sort-by str (keys t)))
            key-gen (fn [k]
                      (let [kt (get t k)]
                        (if (opt-type? kt)
                          (gen/frequency [[1 (gen/return ::absent)]
                                          [1 (gen/return nil)]
                                          [3 (type->gen (second kt) tenv)]])
                          (type->gen kt tenv))))]
        (gen/fmap (fn [vs] (into {} (remove #(= ::absent (second %))) (map vector ks vs)))
                  (apply gen/tuple (map key-gen ks))))

      ;; an index: records, each kept under its key, and one that would
      ;; share a key or a unique field with one before it left out
      (and (kind/index-type? t) (not (data-decl t tenv)))
      (let [{k :key r :of u :unique} (kind/index-parts t)]
        (gen/fmap (fn [rs]
                    (reduce (fn [m x]
                              (if (or (contains? m (get x k))
                                      (some (fn [f] (some #(= (get x f) (get % f)) (vals m))) u))
                                m
                                (assoc m (get x k) x)))
                            {} rs))
                  (index-records r k tenv)))

      (seq? t)
      (let [[h & as] t
            el #(type->gen (nth as %) tenv)]
        (case h
          Opt (gen/frequency [[1 (gen/return nil)] [3 (el 0)]])
          ;; a (List T) is any seq Clojure hands around: a list, a vector,
          ;; a lazy seq or nil.  Shrinking prefers the list.
          List (let [g (element-gen (nth as 0) tenv)
                     v (capped-vector g tenv nil)
                     l (if (::nested tenv) (gen/fmap #(apply list %) v) (gen/list g))]
                 (gen/frequency [[3 l]
                                 [3 v]
                                 [2 (gen/fmap #(map identity %) l)]
                                 [1 (gen/return nil)]]))
          Vec (capped-vector (element-gen (nth as 0) tenv) tenv nil)
          Set (let [g (element-gen (nth as 0) tenv)]
                (if (::nested tenv)
                  (gen/sized (fn [s] (gen/set g {:max-elements (max-length tenv s nil)})))
                  (gen/set g)))
          ;; keys first, when they have few values: a map over three
          ;; keys never draws fifty values to keep three
          Map (let [kg (element-gen (nth as 0) tenv)
                    vg (element-gen (nth as 1) tenv)]
                (cond (domain-size (nth as 0) tenv) (gen/fmap #(into {} %) (keys-first kg vg tenv))
                      (::nested tenv) (gen/sized (fn [s] (gen/map kg vg {:max-elements (max-length tenv s nil)})))
                      :else (gen/map kg vg)))
          (Tuple &) (apply gen/tuple (map #(type->gen % tenv) as))
          -> (fn-gen (type->gen (last t) tenv))
          (if-let [[d args] (data-decl t tenv)]
            (data-gen d args h tenv)
            (fail! "cannot generate values of type `" (pr-str t) "`"))))

      :else (fail! "cannot generate values of type `" (pr-str t) "`"))))

(defn sample
  "`n` generated values of type `t`, for a look at what laws are run on."
  ([t tenv] (sample t tenv 10))
  ([t tenv n] (gen/sample (type->gen t tenv) n)))

(def ^:dynamic *parallel*
  "Whether par-map may spread its work over threads: false under a check
  with {:parallel false}, and inside a par-map's own work, so a nested one
  runs on the thread it is given."
  true)

(defn- par-map
  "(mapv f xs), the calls spread over one thread a processor.  The results
  keep the order of xs; the first exception a call threw, in that order,
  is thrown again."
  [f xs]
  (let [xs (vec xs)
        n (min (count xs) (.availableProcessors (Runtime/getRuntime)))]
    (if (or (not *parallel*) (< n 2))
      (mapv f xs)
      (let [next-i (atom -1)
            out (object-array (count xs))
            work (fn []
                   (binding [*parallel* false]
                     (loop []
                       (let [i (swap! next-i inc)]
                         (when (< i (count xs))
                           (aset out i (try {:ok (f (nth xs i))} (catch Throwable e {:thrown e})))
                           (recur))))))]
        (run! deref (doall (repeatedly n #(future (work)))))
        (mapv #(if (contains? % :thrown) (throw (:thrown %)) (:ok %)) out)))))

(defn- draw
  "The value of type t drawn at size and seed.  The draw is deterministic,
  so a check makes it once: (:draws ctx), an atom, keeps it for every
  stand-in and law that asks for the same one."
  [ctx t size seed]
  (let [make #(gen/generate (type->gen t (:tenv ctx)) size seed)]
    (if-let [cache (:draws ctx)]
      ;; a delay, so threads that want the same draw at once make it once
      (let [k [t size seed]]
        @(or (get @cache k)
             (get (swap! cache #(if (contains? % k) % (assoc % k (delay (make))))) k)))
      (make))))

;; --- evaluating laws ---------------------------------------------------------

(defn- qualify
  "Resolve a law's free names the way the spec reads them: a target public
  first, then a name the spec ns interns; bound names and anything else
  (core, aliases) are left for eval in the spec ns.  own, name ->
  qualified name, comes before both: a lemma reads the defns of its proof
  namespace first."
  ([form bound target-publics spec-interns target spec-ns]
   (qualify form bound target-publics spec-interns target spec-ns {}))
  ([form bound target-publics spec-interns target spec-ns own]
  (letfn [(walk [f bound]
            (cond
              (and (symbol? f) (nil? (namespace f)) (not (contains? bound f)))
              (cond (contains? own f) (get own f)
                    (contains? target-publics f) (symbol (name target) (name f))
                    (contains? spec-interns f) (symbol (name spec-ns) (name f))
                    :else f)
              ;; an alias of the spec's, set/intersection, by its namespace's
              ;; own name, which the prover knows
              (and (symbol? f) (namespace f))
              (if-let [a (try (get (ns-aliases (the-ns spec-ns)) (symbol (namespace f))) (catch Throwable _ nil))]
                (symbol (str (ns-name a)) (name f))
                f)
              (and (seq? f) (= 'quote (first f))) f
              (and (seq? f) (quant? f))
              (let [[q [x t] body] f] (list q [x t] (walk body (conj bound x))))
              (seq? f) (apply list (map #(walk % bound) f))
              (vector? f) (mapv #(walk % bound) f)
              (map? f) (into {} (map (fn [[k v]] [(walk k bound) (walk v bound)])) f)
              (set? f) (into #{} (map #(walk % bound)) f)
              :else f))]
    (walk form bound))))

(defn- proof-own
  "name -> qualified name for the defns a proof namespace interns."
  [proof-ns]
  (if proof-ns
    (into {} (for [[k v] (ns-interns (the-ns proof-ns)) :when (fn? @v)]
               [k (symbol (name proof-ns) (name k))]))
    {}))

(defn- calls-target?
  "Does a qualified law mention any fn of the target namespace?"
  [qp target]
  (boolean (some #(and (symbol? %) (= (name target) (namespace %)))
                 (tree-seq coll? seq qp))))

(def ^:dynamic *in-code*
  "Is the target's code, or a law, running?  An assumed fn's signature
  types those calls; writ's own calls to the fn, and the fn's calls to
  itself, are not the spec's to type."
  false)

(defn- evaluator
  "Compile and cache term fns: (ev vars term env) runs `term` with the
  variables bound from env."
  [spec-ns]
  ;; keyed by the printed term: '(a b) and '[a b] are =, but not the same term
  (let [cache (atom {})]
    (fn [vars term env]
      (let [k (pr-str [vars term])
            f (or (get @cache k)
                  (let [f (binding [*ns* (the-ns spec-ns)]
                            (eval (list 'fn (vec vars) term)))]
                    (swap! cache assoc k f)
                    f))]
        ;; compiling the term is writ's; running it is the law's
        (binding [*in-code* true] (apply f (map #(get env %) vars)))))))

(defn- run-term
  "{:ok v} or {:thrown msg}."
  [ctx term env]
  (try {:ok ((:ev ctx) (:vars ctx) term env)}
       (catch Throwable e {:thrown (or (ex-message e) (str e))})))

(defn- literal? [x]
  (or (number? x) (string? x) (keyword? x) (char? x) (boolean? x) (nil? x)
      (and (coll? x) (empty? x))))

(declare holds)

(defn- sample-quant
  "A nested quantifier: sampled over a handful of generated values."
  [ctx [q [x t] body] env]
  (let [ctx* (update ctx :vars conj x)
        g (type->gen t (:tenv ctx))
        ;; drawn from the values around it, so a check with a seed
        ;; replays the same samples
        base (hash env)
        vals (map #(gen/generate g % (+ base %)) (range 20))
        rs (map #(holds ctx* body (assoc env x %)) vals)]
    (if (= "forall" (name q))
      (or (first (filter #(= :fail (:result %)) rs)) {:result :pass})
      (or (first (filter #(= :pass (:result %)) rs))
          {:result :fail :detail [[(list q [x t] '...) "no witness among 20 samples"]]}))))

(defn- binding-form?
  "A form whose arguments are not all expressions: a special form or a
  macro, such as `let`, whose binding vector cannot be evaluated alone.
  The connectives are kept, since each of their arguments is one."
  [p]
  (let [h (first p)]
    (and (symbol? h)
         (not (contains? '#{or and when if not} (symbol (name h))))
         (or (special-symbol? h)
             (boolean (some-> (ns-resolve (the-ns 'clojure.core) h) meta :macro))))))

(defn holds
  "Evaluate proposition `p` under env: {:result :pass|:fail|:discard
  :detail [[term value-or-note]]}."
  [ctx p env]
  (cond
    (head? p "=")
    (let [[_ a b] p
          ra (run-term ctx a env)
          rb (run-term ctx b env)
          show (fn [r] (if (contains? r :ok) (pr-str (:ok r)) (str "threw: " (:thrown r))))]
      (if (and (contains? ra :ok) (contains? rb :ok) (= (:ok ra) (:ok rb)))
        {:result :pass}
        {:result :fail
         :detail (cond-> [[a (show ra)] [b (show rb)]]
                   ;; they print alike: a NaN inside, which = says is not itself
                   (and (contains? ra :ok) (contains? rb :ok) (pterm/same (:ok ra) (:ok rb)))
                   (conj [(list '= a b) "false only because = says NaN is not NaN; compare with same, where a NaN is the same as a NaN"]))}))

    (head? p "and")
    (or (first (remove #(= :pass (:result %)) (map #(holds ctx % env) (rest p))))
        {:result :pass})

    (head? p "=>")
    (let [h (holds ctx (nth p 1) env)]
      (if (= :pass (:result h))
        (holds ctx (nth p 2) env)
        {:result :discard}))

    (quant? p) (sample-quant ctx p env)

    :else
    (let [r (run-term ctx p env)]
      (cond
        (:thrown r) {:result :fail :detail [[p (str "threw: " (:thrown r))]]}
        (:ok r) {:result :pass}
        :else
        {:result :fail
         :detail (into [[p (pr-str (:ok r))]]
                       (when (and (seq? p) (not (binding-form? p)))
                         (keep (fn [a]
                                 ;; a fn literal's value prints as an object
                                 (when-not (or (literal? a) (symbol? a)
                                               (and (seq? a) (contains? '#{fn fn*} (first a))))
                                   (let [ra (run-term ctx a env)]
                                     [a (if (contains? ra :ok) (pr-str (:ok ra))
                                            (str "threw: " (:thrown ra)))])))
                               (rest p))))}))))

(defn- leading-foralls [p]
  (loop [p p, bs []]
    (if (head? p "forall")
      (let [[_ [x t] body] p] (recur body (conj bs [x t])))
      [bs p])))

(defn- leading-exists [p]
  (loop [p p, bs []]
    (if (head? p "exists")
      (let [[_ [x t] body] p] (recur body (conj bs [x t])))
      [bs p])))


(def ^:private witness-trials 1000)

(defn- law-atoms
  "The clauses of a law whose outcome a test should see both ways: each
  comparison in it, and each part of its hypotheses, that mentions one of
  its variables.  Not inside a fn literal, whose locals a test cannot
  bind.  At most 8."
  [body vars]
  (let [vars (set vars)
        mentions? (fn [f] (some vars (tree-seq coll? seq f)))
        walk (fn walk [f]
               (cond
                 (and (seq? f) (contains? '#{fn fn* letfn} (first f))) []
                 (seq? f) (concat (when (contains? '#{< <= > >=} (first f)) [f]) (mapcat walk (rest f)))
                 (coll? f) (mapcat walk f)
                 :else []))
        flat (fn flat [f] (if (and (seq? f) (contains? '#{and or not} (first f))) (mapcat flat (rest f)) [f]))
        hyps (loop [p body, hs []] (if (head? p "=>") (recur (nth p 2) (into hs (flat (nth p 1)))) hs))]
    (vec (take 8 (distinct (filter #(and (seq? %) (mentions? %)) (concat hyps (walk body))))))))

(defn- count-atoms!
  "Note how each atom came out at env, in counts: {atom {true n false n}}."
  [ctx atoms counts env]
  (doseq [a atoms]
    (let [r (run-term ctx a env)]
      (when (contains? r :ok)
        (swap! counts update-in [a (boolean (:ok r))] (fnil inc 0))))))

(defn- test-law
  [ctx {:keys [name prop witness]} {:keys [trials seed max-size]}]
  (let [[bs body] (leading-foralls prop)
        qc (fn [p] (tc/quick-check trials p :seed seed :max-size max-size))]
    (cond
      ;; closed: run it once
      (and (empty? bs) (not (quant? body)))
      (let [r (holds (assoc ctx :vars []) body {})]
        (if (= :pass (:result r))
          {:law name :status :evaluated}
          {:law name :status :failed :counterexample {}
           :detail (or (:detail r) [[body "the hypothesis does not hold"]])}))

      ;; existential: a witness is a counterexample to its negation, so
      ;; test.check finds it and shrinks it to the simplest one.  The search
      ;; stops at the first, so a rare one -- a pong game a point from won,
      ;; with the ball past the paddle -- is looked for harder than a law
      ;; is tested: at least witness-trials values
      ;; an existential with a witness the spec gives: that one, first
      (and (empty? bs) (head? body "exists") witness
           (let [[ebs inner] (leading-exists body)
                 xs (mapv first ebs)]
             (and (= (count xs) (count witness))
                  (= :pass (:result (holds (assoc ctx :vars xs) inner (zipmap xs witness)))))))
      (let [[ebs] (leading-exists body)]
        {:law name :status :witnessed :witness (zipmap (map first ebs) witness)})

      (and (empty? bs) (head? body "exists"))
      (let [[ebs inner] (leading-exists body)
            xs (mapv first ebs)
            ctx* (assoc ctx :vars xs)
            res (tc/quick-check (max trials witness-trials)
                  (prop/for-all* (mapv #(type->gen (second %) (:tenv ctx)) ebs)
                                   (fn [& vs] (not= :pass (:result (holds ctx* inner (zipmap xs vs))))))
                  :seed seed :max-size max-size)]
        (if (:pass? res)
          {:law name :status :failed :counterexample {} :seed (:seed res)
           :detail [[(list 'exists (vec (apply concat ebs)) '...)
                     (str "no witness among " (:num-tests res) " generated values")]]}
          {:law name :status :witnessed :seed (:seed res)
           :witness (zipmap xs (get-in res [:shrunk :smallest]))}))

      :else
      (let [vars (mapv first bs)
            ctx* (assoc ctx :vars vars)
            discards (atom 0)
            atoms (law-atoms body vars)
            counts (atom {})
            res (qc (prop/for-all* (mapv #(type->gen (second %) (:tenv ctx)) bs)
                                   (fn [& vals]
                                     (case (:result (holds ctx* body (zipmap vars vals)))
                                       :pass (do (count-atoms! ctx* atoms counts (zipmap vars vals)) true)
                                       ;; a trial its hypothesis refused still shows
                                       ;; how the hypothesis came out
                                       :discard (do (swap! discards inc)
                                                    (count-atoms! ctx* atoms counts (zipmap vars vals))
                                                    true)
                                       false))))]
        (cond
          (not (:pass? res))
          (let [small (zipmap vars (get-in res [:shrunk :smallest]))]
            {:law name :status :failed
             :counterexample small
             :original (zipmap vars (:fail res))
             :trial (:num-tests res) :seed (:seed res)
             :detail (:detail (holds ctx* body small))})

          (= @discards (:num-tests res))
          {:law name :status :failed :counterexample {} :seed (:seed res) :no-hypothesis true
           :detail [[body (str "the hypothesis never held in " (:num-tests res) " trials")]]}

          :else
          {:law name :status :tested :trials (:num-tests res) :seed (:seed res)
           :discarded @discards :coverage @counts})))))

;; --- adequacy: does the spec pin the code down? ------------------------------

(defn- other-value
  "A fn from a result to a different value of type `ret`, or nil when the
  type has only one value.  Types with no perturbation of their own take
  the first of a few generated values that differs from the result."
  [ret tenv seed]
  (let [h (if (seq? ret) (first ret) ret)]
    (case h
      (Nat Int) inc
      Bool not
      String #(str % "x")
      (Unit Any) nil
      (let [g (type->gen ret tenv)
            cands (distinct (map #(gen/generate g (* 3 %) (+ seed %)) (range 8)))]
        (when (next cands)
          (fn [r] (or (first (remove #(= r %) cands)) r)))))))

(defn- pinned-args
  "{i #{values}} for each argument position of `f` that every law calls it
  with a literal at: the laws say what `f` does there and nowhere else.
  Empty when some law uses `f` as a value rather than calling it, since
  then its arguments cannot be read off the law."
  [props f n]
  (let [forms (mapcat #(tree-seq coll? seq %) props)
        calls (filter #(and (seq? %) (= f (first %))) forms)
        lit? #(or (number? %) (string? %) (keyword? %) (char? %) (boolean? %) (nil? %))]
    (if (or (empty? calls) (not= (count calls) (count (filter #{f} forms))))
      {}
      (into {} (for [i (range n)
                     :let [as (map #(nth % (inc i) ::none) calls)]
                     :when (every? #(and (not= ::none %) (lit? %)) as)]
                 [i (set as)])))))

(defn impostors
  "Well-typed stand-ins for fn `nm` with signature `sig`: {:desc :kind
  :make}, where (make real-fn) is the impostor.  Constants of the return
  type, each argument of the return type passed through, the real result
  perturbed, and -- for each argument `pins` fixes to a set of literals --
  the real result on those literals and a different one everywhere else.
  A spec that means something rejects every one of them."
  [nm sig argn tenv seed & [pins]]
  (let [ret (plain (:ret sig))
        g (type->gen ret tenv)
        consts (distinct [(gen/generate g 0 seed) (gen/generate g 5 (inc seed))])
        other (other-value ret tenv seed)
        arg-name #(nth argn % (str "arg" %))
        wrap (fn [desc f] {:desc desc :kind :perturbed
                           :make (fn [real] (fn [& args] (f (apply real args))))})]
    (concat
      (for [v consts]
        {:desc (str "always returns " (pr-str v)) :kind :constant :make (fn [_] (fn [& _] v))})
      (keep-indexed (fn [i t]
                      (when (= (plain t) ret)
                        {:desc (str "returns its argument `" (arg-name i) "` unchanged")
                         :kind :pass-through
                         :make (fn [_] (fn [& args] (nth args i)))}))
                    (:params sig))
      ;; the real result, changed a little: the mistakes that keep its
      ;; type -- one off, an element dropped or added, a field changed
      (let [h (if (seq? ret) (first ret) ret)
            el (when (and (seq? ret) (contains? '#{List Vec Set} h))
                 (try (gen/generate (type->gen (second ret) tenv) 3 seed) (catch Throwable _ nil)))]
        (case h
          Nat [(wrap "returns one more than the real result" inc)
               (wrap "returns one less than the real result (one more at 0)" #(if (pos? %) (dec %) 1))]
          Int [(wrap "returns one more than the real result" inc)
               (wrap "returns one less than the real result" dec)]
          Bool [(wrap "returns the opposite of the real result" not)]
          String [(wrap "returns the real result with a character appended" #(str % "x"))]
          List (cond-> [(wrap "returns the real result reversed" reverse)
                        (wrap "returns the real result without its first element" rest)
                        (wrap "returns the real result without its last element" #(or (butlast %) ()))]
                 (some? el) (conj (wrap (str "returns the real result with " (pr-str el) " added") #(cons el %))))
          Vec (cond-> [(wrap "returns the real result reversed" #(vec (reverse %)))
                       (wrap "returns the real result without its first element" #(vec (rest %)))
                       (wrap "returns the real result without its last element" #(vec (butlast %)))]
                (some? el) (conj (wrap (str "returns the real result with " (pr-str el) " added") #(conj (vec %) el))))
          Set (cond-> [(wrap "returns the real result without one of its elements" #(if (seq %) (disj % (first (sort-by pr-str %))) %))]
                (some? el) (conj (wrap (str "returns the real result with " (pr-str el) " added") #(conj (set %) el))))
          (if (and (map? ret) (seq ret) (every? keyword? (keys ret)))
            ;; a record: each field, changed alone
            (vec (for [[k kt] (sort-by (comp str key) ret)
                       :let [o (other-value (plain kt) tenv seed)]
                       :when o]
                   (wrap (str "returns the real result with its " k " changed")
                         #(if (map? %) (update % k o) %))))
            (when other [(wrap "returns a different value than the real result" other)]))))
      (when other
        (for [[i vs] (sort-by key pins)
              :when (not (and (= 'Bool (plain (nth (:params sig) i nil)))
                              (= #{true false} vs)))
              :let [shown (str/join ", " (map pr-str (sort-by (fn [v] [(if (number? v) 0 1)
                                                                       (if (number? v) v 0)
                                                                       (pr-str v)])
                                                              vs)))
                    vs (vec vs)]]
          {:desc (str "returns a different value whenever `" (arg-name i)
                      "` is not one of " shown)
           :kind :off-pin
           :make (fn [real]
                   (fn [& args]
                     (let [r (apply real args)]
                       (if (some #(= % (nth args i)) vs) r (other r)))))})))))

(def ^:private swaps
  "What a mutant puts in place of an operator: the mistake a slip of the
  hand makes."
  '{< <=, <= <, > >=, >= >, = not=, not= =, inc dec, dec inc, + -, - +, and or, or and,
    first last, rest butlast, pos? neg?, zero? pos?, empty? seq, max min, min max})

(defn- mutation-sites
  "The places in form a mutant changes, as [path replacement desc]: an
  operator swapped, an integer one off, an if's branches swapped.  A
  quoted form is data, and is left alone."
  [form]
  (letfn [(sites [f path parent]
            (cond
              (and (seq? f) (= 'quote (first f))) []
              (seq? f)
              (let [[h & args] f]
                (concat
                  (when-let [r (and (symbol? h) (get swaps (symbol (name h))))]
                    [[(conj path 0) r (str "uses `" r "` for `" h "` in " (pr-str f))]])
                  (when (and (contains? '#{if clojure.core/if} h) (= 4 (count f)))
                    [[path (list h (nth f 1) (nth f 3) (nth f 2)) (str "swaps the branches of " (pr-str f))]])
                  (mapcat (fn [i x] (sites x (conj path i) f)) (range 1 (count f)) args)))
              (vector? f) (mapcat (fn [i x] (sites x (conj path i) f)) (range) f)
              (and (integer? f) (not (boolean? f)))
              (for [x [(inc f) (dec f)]]
                [path x (str "has " x " for " f (when parent (str " in " (pr-str parent))))])
              :else []))]
    (sites form [] nil)))

(defn- put-at
  "form with the part at path replaced by x; lists stay lists."
  [form path x]
  (if (empty? path)
    x
    (let [[i & more] path
          v (vec form)
          v (assoc v i (put-at (nth v i) more x))]
      (if (vector? form) v (with-meta (apply list v) (meta form))))))

(declare static-check defn-parts source-url unbang)

(defn- mutants
  "Mutants of signed fn nm, as impostors: its source changed at one place,
  kept only when writ's static check still passes it -- so it is
  well-typed and terminates -- and when some input tells it from the
  real fn, which :distinguish holds.  A mutant no input tells apart is the
  same fn, and never a gap.  At most budget of them."
  [e target nm sig ctx seed budget]
  (let [forms (book/read-forms (source-url target))
        f (first (filter #(and (ck/defn-form? %) (= nm (second %))) forms))
        {:keys [params body]} (when f (defn-parts f))]
    (when (and f (vector? params))
      (let [gens (try (mapv #(type->gen % (:tenv ctx)) (:params sig)) (catch Throwable _ nil))
            real @(ns-resolve (the-ns target) nm)
            static-ok? (fn [body*]
                         (let [f* (apply list (concat (take-while #(not= params %) f) [params] body*))]
                           (:ok (static-check (assoc e ::forms-override {nm f*})))))
            run (fn [g args] (try {:ok (apply g args)} (catch Throwable _ ::threw)))
            differ (fn [g]
                     (when gens
                       (first (for [i (range 200)
                                    :let [args (map-indexed (fn [j t] (draw ctx t (mod i 20) (+ seed i (* 31 j)))) (:params sig))]
                                    :when (not= (run real args) (run g args))]
                                (with-meta (zipmap (map-indexed (fn [i _] (nth params i (symbol (str "arg" i)))) (:params sig)) args)
                                  {::args (vec args)})))))]
        (->> (mutation-sites (vec body))
             (take (* 4 budget))
             (keep (fn [[path x desc]]
                     (let [body* (seq (put-at (vec body) path x))]
                       (when (static-ok? body*)
                         (let [g (try (binding [*ns* (the-ns target)]
                                        (eval (list* 'fn nm params body*)))
                                      (catch Throwable _ nil))
                               d (when g (differ g))]
                           (when d
                             {:desc (str desc ", and it differs from the real fn on " (pr-str d))
                              :kind :mutant
                              :args (::args (meta d))
                              :make (fn [_] g)}))))))
             (take budget))))))

(declare leading-foralls holds)

(defn- holds-sampled?
  "Does `prop` hold on `n` deterministic samples?  Existentials never
  reject an impostor; a law's own failure is what adequacy looks for."
  [ctx prop n seed]
  (let [[bs body] (leading-foralls prop)]
    (cond
      (and (empty? bs) (not (quant? body)))
      (not= :fail (:result (holds (assoc ctx :vars []) body {})))

      (empty? bs) true

      :else
      (let [vars (mapv first bs)
            ctx* (assoc ctx :vars vars)]
        ;; each variable its own seed: with one seed, two variables of a
        ;; type get the same value every time, and a law relating them
        ;; never sees them differ
        (and (every? (fn [i]
                       (not= :fail (:result (holds ctx* body
                                                   (zipmap vars (map-indexed
                                                                  (fn [j [_ t]] (draw ctx t (mod i 30)
                                                                                          (+ seed i (* 7919 j))))
                                                                  bs))))))
                     (range n))
             ;; the inputs the solver found to meet a hypothesis no sample meets
             (every? #(not= :fail (:result (holds ctx* body %))) (::witness (meta prop))))))))

(defn- calls-on-vars
  "The calls of fn qnm in law prop whose arguments are each a variable
  the law binds or an expression of none: where the law can be run at
  given arguments of qnm.  Each as {var arg-position}."
  [prop qnm n]
  (let [[bs body] (leading-foralls prop)
        vars (set (map first bs))
        free? (fn [x] (not-any? vars (tree-seq coll? seq x)))]
    (vec (distinct
           (for [c (tree-seq coll? seq body)
                 :when (and (seq? c) (= qnm (first c)) (= n (count (rest c))))
                 :let [args (vec (rest c))]
                 :when (every? #(or (contains? vars %) (free? %)) args)
                 :let [pos (into {} (keep-indexed (fn [i a] (when (contains? vars a) [a i]))) args)]
                 :when (seq pos)]
             pos)))))

(defn- rejects-at?
  "Does law prop fail when run with fn qnm's arguments set to args, at a
  call that takes them straight from the law's variables, the law's
  other variables drawn n times?  A pinned value its variable's type
  does not take is no input of the law."
  [ctx prop qnm args n seed]
  (let [[bs body] (leading-foralls prop)
        vars (mapv first bs)
        types (into {} bs)
        ctx* (assoc ctx :vars vars)]
    (boolean
      (some (fn [pos]
              (let [pinned (into {} (for [[v i] pos] [v (nth args i)]))]
                (when (every? (fn [[v x]] (conforms? (get types v) x (:tenv ctx))) pinned)
                  (let [rest-bs (remove #(contains? pinned (first %)) bs)]
                    (some (fn [i]
                            (= :fail (:result
                                       (holds ctx* body
                                              (merge (zipmap (map first rest-bs)
                                                             (map-indexed (fn [j [_ t]] (draw ctx t (mod i 30) (+ seed i (* 7919 j))))
                                                                          rest-bs))
                                                     pinned)))))
                          (range n))))))
            (calls-on-vars prop qnm (count args))))))

(def ^:dynamic *stand-ins*
  "var -> the fn a stand-in puts in its place, on this thread: a var
  adequacy dispatches calls it while it judges stand-ins, so threads judge
  different ones at once."
  {})

(defn- dispatching
  "In place of fn real at var v: the stand-in this thread has for v, or real."
  [v real]
  (fn [& args]
    (if-let [g (get *stand-ins* v)]
      (apply g args)
      (apply real args))))

(declare adequacy*)

(defn- adequacy
  "Swap each signed public fn for its impostors, and run every law against
  each.  The impostors of every fn are judged at once, each on its own
  thread's view of the fns.  Returns, per fn, [{:fn f :laws n :rejected
  [impostor] :survivors [desc]}]: a survivor is a gap in the spec."
  [ctx target fns anns props trials seed & [extra]]
  (let [vars (into {} (for [nm fns
                            :let [v (ns-resolve (the-ns target) nm)]
                            :when (and (var? v) (fn? @v))]
                        [nm [v @v]]))]
    (try
      (doseq [[_ [v real]] vars] (alter-var-root v (constantly (dispatching v real))))
      (adequacy* ctx target fns anns props trials seed extra vars)
      (finally
        (doseq [[_ [v real]] vars] (alter-var-root v (constantly real)))))))

(defn- adequacy*
  [ctx target fns anns props trials seed extra vars]
  (let [per-fn
        (vec (for [nm fns
             :let [v (ns-resolve (the-ns target) nm)
                   real (or (second (get vars nm)) @v)
                   sig (get anns nm)
                   argn (vec (take (count (:params sig)) (first (:arglists (meta v)))))
                   qnm (symbol (name target) (name nm))
                   pins (pinned-args props qnm (count (:params sig)))
                   ;; a mutant is told apart at the input that shows it: when
                   ;; the samples miss it, each law that calls the fn on its
                   ;; own variables is run there, so a survivor is a gap in
                   ;; the laws, not in the data
                   ;; a stand-in off an example is judged by the other laws:
                   ;; the example's own law rejects it, and says nothing of them
                   judges (fn [imp] (if (= :off-example (:kind imp)) (remove #(::example (meta %)) props) props))
                   survives? (fn [imp]
                               (try
                                 (binding [*stand-ins* {v ((:make imp) real)}]
                                   (and (every? #(holds-sampled? ctx % trials seed) (judges imp))
                                        (not (and (:args imp)
                                                  (some #(rejects-at? ctx % qnm (:args imp) 10 seed) (judges imp))))))
                                 (catch Throwable _ false)))
                   off-examples (let [ret (plain (:ret sig))
                                      other (other-value ret (:tenv ctx) seed)]
                                  (when other
                                    (for [{:keys [args out]} (keep #(let [x (::example (meta %))]
                                                                      (when (= nm (:fn x)) x))
                                                                   props)
                                          :let [args (vec args) wrong (other out)]
                                          :when (not= wrong out)]
                                      {:desc (str "agrees with the real fn except at " (pr-str (list* nm args))
                                                  ", where it returns " (pr-str wrong) " -- the example says "
                                                  (pr-str out) ", and no other law says what `" nm "` returns there")
                                       :kind :off-example
                                       :args args
                                       :make (fn [real] (fn [& a] (if (= (vec a) args) wrong (apply real a))))})))
                   gap-desc (fn [imp]
                              (if (and (:args imp) (not= :off-example (:kind imp)))
                                (str (:desc imp)
                                     (if (some #(seq (calls-on-vars % qnm (count (:args imp)))) props)
                                       ", and no law tells it apart, even run there"
                                       (str ", and no law calls `" nm "` on its own variables, so none could be run there")))
                                (:desc imp)))
                   imps (vec (concat (impostors nm sig argn (:tenv ctx) seed pins)
                                     off-examples
                                     (when extra (extra nm sig))))]]
           {:nm nm :v v :real real :qnm qnm :imps imps :survives? survives? :gap-desc gap-desc}))
        ;; the values every stand-in is judged on, drawn first and at once:
        ;; judged at once, the stand-ins would all wait on the same draw
        _ (par-map (fn [[t size sd]] (try (draw ctx t size sd) (catch Throwable _ nil)))
                   (distinct (for [p props
                                   :let [[bs] (leading-foralls p)]
                                   i (range trials)
                                   [j [_ t]] (map-indexed vector bs)]
                               [t (mod i 30) (+ seed i (* 7919 j))])))
        ;; every stand-in of every fn, judged at once
        verdicts (par-map (fn [[i imp]] ((:survives? (nth per-fn i)) imp))
                          (for [[i f] (map-indexed vector per-fn), imp (:imps f)] [i imp]))
        verdicts (loop [vs verdicts, fs per-fn, out []]
                   (if-let [f (first fs)]
                     (let [n (count (:imps f))]
                       (recur (drop n vs) (rest fs) (conj out (vec (take n vs)))))
                     out))]
    (vec (for [[{:keys [nm v real qnm imps gap-desc]} vs] (map vector per-fn verdicts)
               :let [{survived true rejected false} (group-by first (map vector vs imps))
                     survived (map second survived)
                     rejected (map second rejected)
                   ;; which laws, each on its own, tell some stand-in apart: a
                   ;; law that tells none says no more than the types do
                   about (filter #(some #{qnm} (tree-seq coll? seq %)) props)
                   credited (reduce (fn [done imp]
                                      (let [open (remove #(or (nil? (::law (meta %))) (contains? done (::law (meta %))))
                                                         about)]
                                        (if (empty? open)
                                          (reduced done)
                                          (try
                                            (binding [*stand-ins* {v ((:make imp) real)}]
                                              (into done (keep #(when-not (holds-sampled? ctx % trials seed)
                                                                  (::law (meta %)))
                                                               open)))
                                            (catch Throwable _ done)))))
                                    #{} rejected)]]
         {:fn nm
          :laws (count about)
          :about (set (keep #(::law (meta %)) about))
          :credited credited
          :impostors (+ (count rejected) (count survived))
          :rejected (mapv #(dissoc % :make :args) rejected)
          :survivors (mapv gap-desc survived)}))))

;; --- the target's source -----------------------------------------------------

(def ^:private spec-forms-accepted
  (str "is not supported: in the code a spec covers, writ checks def and defn "
       "forms only (the ns form and comment blocks are skipped)"))

(defn- source-url [target]
  (let [base (-> (name target) (str/replace "-" "_") (str/replace "." "/"))]
    (or (io/resource (str base ".clj")) (io/resource (str base ".cljc"))
        (fail! "cannot find the source of `" target "` on the classpath"))))

(defn- defn-parts
  "[name docstring? attrs? params body] positions for a defn form."
  [f]
  (let [[h nm & tail] f
        doc (when (string? (first tail)) (first tail))
        tail (if doc (rest tail) tail)
        attrs (when (map? (first tail)) (first tail))
        tail (if attrs (rest tail) tail)]
    {:head h :name nm :doc doc :attrs attrs :params (first tail) :body (rest tail)}))

(defn- annotate-defn
  "Put a spec signature on a plain defn: param types as :writ/type, the
  return type as the name's :tag -- where writ's checker reads them."
  [f sig]
  (let [{:keys [head name doc attrs params body]} (defn-parts f)]
    (when-not (vector? params)
      (fail! "`" name "` is multi-arity; `ann` gives a single signature"))
    (let [fixed (vec (take-while #(not= '& %) params))
          rest? (some #{'&} params)]
      (when (if rest?
              (< (count (:params sig)) (count fixed))
              (not= (count (:params sig)) (count fixed)))
        (fail! "`ann " name "` gives " (count (:params sig)) " parameter type(s) but `"
               name "` takes " (count fixed)))
      (let [types (:params sig)
            params* (loop [ps params, ts types, out []]
                      (cond
                        (empty? ps) out
                        (= '& (first ps)) (into out ps)
                        (or (symbol? (first ps)) (coll? (first ps)))
                        (recur (rest ps) (rest ts)
                               (conj out (vary-meta (first ps) assoc :writ/type (first ts))))
                        :else (recur (rest ps) (rest ts) (conj out (first ps)))))]
        (apply list (concat [head (vary-meta name assoc :tag (:ret sig))]
                            (when doc [doc]) (when attrs [attrs])
                            [params*] body))))))

(declare erase erase-data refines-of)

(declare ns-names core-name?)

(defn- static-check
  "Run writ's rules over the target's source with the spec's types, each
  refinement read as its base type.  Returns {:ok true :defns {name
  private?}} or {:ok false :error msg}."
  [{:keys [target data anns] :as e}]
  (try
    (let [forms (cond->> (book/read-forms (source-url target))
                  ;; a mutant's source in place of the fn's own
                  (::forms-override e)
                  (mapv #(if (and (ck/defn-form? %) (contains? (::forms-override e) (second %)))
                           (get (::forms-override e) (second %))
                           %)))
          defns (into {} (keep (fn [f] (when (ck/defn-form? f)
                                         (let [p (defn-parts f)]
                                           [(:name p) (or (= "defn-" (name (first f)))
                                                          (boolean (:private (meta (:name p)))))]))))
                      forms)
          missing (remove #(contains? defns %) (sort (keys anns)))
          refs (refines-of e)
          ;; to the type checker a ! type is its plain type: NaN is a Double
          anns (into {} (map (fn [[k sig]] [k (unbang (erase sig refs))])) anns)
          data (mapv #(unbang (erase-data % refs)) data)]
      (when (seq missing)
        (fail! "the spec gives `" (first missing) "` a signature, but `" target
               "` defines no fn `" (first missing) "`"))
      (let [forms* (mapv (fn [f]
                           (if (and (ck/defn-form? f) (contains? anns (second f)))
                             (annotate-defn f (get anns (second f)))
                             f))
                         forms)
            [nsf others] [(filter #(head? % "ns") forms*) (remove #(head? % "ns") forms*)]]
        (binding [ck/*affine* false
                  ck/*descend-all* true
                  ty/*tagged* true
                  book/*forms-accepted* spec-forms-accepted
                  ;; by the qualified name an alias resolves to, and by a
                  ;; name the target refers
                  book/*extra-sigs* (let [sig-of #(unbang (erase (get (:assumes e) %) refs))
                                          {:keys [refers] :as names} (some-> (first nsf) ns-names)]
                                      (merge (into {} (for [q (keys (:assumes e))] [q (sig-of q)]))
                                             ;; a core fn by its plain name, where the
                                             ;; code reads that name as core's
                                             (into {} (for [q (keys (:assumes e))
                                                            :when (and (= "clojure.core" (namespace q))
                                                                       (core-name? names (symbol (name q))))]
                                                        [(symbol (name q)) (sig-of q)]))
                                             (into {} (for [[r q] refers :when (contains? (:assumes e) q)]
                                                        [r (sig-of q)]))))]
          (book/check-book (vec (concat nsf data others))))
        {:ok true :defns defns}))
    (catch Throwable e
      {:ok false :error (or (ex-message e) (str e))})))

(defn- form-name [f]
  (when (and (seq? f) (symbol? (second f))) (second f)))

(defn scan
  "Which of `target`'s top-level forms writ could check, before any spec is
  written.  Reads the source from the classpath without loading it, and
  checks each form in order against the forms above it that passed.
  Returns {:target t :forms [{:name :head :private? :status :why}]}, with
  :status :ok, :needs-ann (it fails only because a collection it recurses
  over has no type, which an `ann` gives it) or :no, and :message, a
  summary to read."
  [target]
  (let [forms (book/read-forms (source-url target))
        nsf (filterv #(head? % "ns") forms)
        body (remove #(or (head? % "ns") (head? % "comment")) forms)
        rows (loop [fs body, kept [], blocked {}, out []]
               (if-let [f (first fs)]
                 (let [nm (form-name f)
                       dep (first (keep #(when (symbol? %)
                                           (let [s (symbol (name %))]
                                             (when (and (not= nm s) (contains? blocked s)) s)))
                                        (tree-seq coll? seq (rest f))))
                       [status why]
                       (if dep
                         [(get blocked dep)
                          (str "it uses `" dep "`, which "
                               (if (= :needs-ann (get blocked dep))
                                 "needs an `ann` first"
                                 "writ cannot check"))]
                         (try
                           (binding [ck/*affine* false
                                     ck/*descend-all* true
                                     ty/*tagged* true
                                     book/*forms-accepted* spec-forms-accepted]
                             (book/check-book (vec (concat nsf kept [f]))))
                           [:ok nil]
                           (catch Throwable e
                             (let [m (str/replace (or (ex-message e) (str e)) #"^Writ: " "")]
                               [(if (str/includes? m "must be a finite collection") :needs-ann :no)
                                m]))))]
                   (recur (rest fs)
                          (if (= :ok status) (conj kept f) kept)
                          (if (and nm (not= :ok status)) (assoc blocked nm status) blocked)
                          (conj out (cond-> {:name nm :head (first f) :status status
                                             :private? (boolean (or (head? f "defn-")
                                                                    (and nm (:private (meta nm)))))}
                                      why (assoc :why why)))))
                 out))
        label (fn [{:keys [name head private?]}]
                (str (or name head)
                     (when-not (contains? #{"defn" "defn-" "def"} (clojure.core/name head))
                       (str " (" head ")"))
                     (when private? " (private)")))
        group (fn [k title]
                (when-let [rs (seq (filter #(= k (:status %)) rows))]
                  (str "\n\n" title
                       (apply str (for [r rs]
                                    (str "\n  " (label r)
                                         (when (:why r) (str ": " (:why r)))))))))
        n (fn [k] (count (filter #(= k (:status %)) rows)))]
    {:target target
     :forms rows
     :message (str "writ.spec/scan " target ": " (n :ok) " of " (count rows)
                   " forms can be checked"
                   (when (pos? (n :needs-ann)) (str ", " (n :needs-ann) " more once signed"))
                   (group :ok "can be checked:")
                   (group :needs-ann "can be checked once an `ann` types its collection:")
                   (group :no "cannot be checked:"))}))

;; --- the call graph --------------------------------------------------------------

(defn- ns-names
  "The names an ns form brings in: {:aliases {alias lib} :refers {name
  lib/name} :excludes #{name}}, from its :require clauses and the
  clojure.core names its :refer-clojure :exclude leaves out."
  [ns-form]
  (assoc
  (reduce (fn [acc [lib & opts]]
            (let [o (apply hash-map (take (* 2 (quot (count opts) 2)) opts))]
              (cond-> acc
                (symbol? (:as o)) (assoc-in [:aliases (:as o)] lib)
                (sequential? (:refer o))
                (update :refers into (map (fn [r] [r (symbol (name lib) (name r))]))
                        (:refer o)))))
          {:aliases {} :refers {}}
          (for [clause (rest ns-form)
                :when (and (seq? clause) (= :require (first clause)))
                spec (rest clause)
                :when (or (vector? spec) (symbol? spec))]
            (if (symbol? spec) [spec] (seq spec))))
  :excludes (set (for [clause (rest ns-form)
                       :when (and (seq? clause) (= :refer-clojure (first clause)))
                       :let [o (apply hash-map (take (* 2 (quot (count (rest clause)) 2)) (rest clause)))]
                       x (:exclude o)]
                   x))))

(defn- core-name?
  "Does a namespace with these names read the plain name nm as
  clojure.core's?"
  [{:keys [refers excludes]} nm]
  (not (or (contains? refers nm) (contains? excludes nm))))

(defn- callee
  "What a name in a body refers to in the call graph: the simple name of
  one of the namespace's own fns, or a qualified fn of another namespace.
  nil for clojure.core, host members, and anything else."
  [s own {:keys [aliases refers]}]
  (cond
    (nil? (namespace s)) (cond (contains? own s) s
                               (contains? refers s) (get refers s))
    (l/host-member? s) nil
    :else (let [q (symbol (namespace s))
                lib (get aliases q q)
                nm (symbol (name s))]
            ;; the namespace decides: other/f is other's f even when this
            ;; namespace has an f of its own
            (cond (and (= lib (:self aliases)) (contains? own nm)) nm
                  (= 'clojure.core lib) nil
                  :else (symbol (name lib) (name s))))))

(defn- body-refs
  "Every name a defn's body refers to, locals excluded.  The body is
  lowered and its binders renamed apart, so a local that shadows a fn is
  not a reference to it.  Code writ cannot lower is read as plain symbols."
  [params body own]
  (try
    (let [ast (binding [l/*locals* own]
                (l/uniquify (l/lower (list* 'fn params body))))]
      (keep #(when (and (map? %) (= :ref (:op %))) (:name %))
            (tree-seq coll? #(if (map? %) (vals %) (seq %)) ast)))
    (catch Throwable _
      (let [locals (set (mapcat l/binding-names params))]
        (remove locals (filter symbol? (tree-seq coll? seq body)))))))

(defn- graph-of
  "{f #{callee}} for each defn and defmacro in `forms`, in the terms of
  `callee`.  A macro calls what it calls as it expands and what its
  expansion names, so an effect shell's receive or with-x macro can be
  held to the layers it must go through."
  [forms]
  (let [nsf (first (filter #(head? % "ns") forms))
        names (assoc-in (ns-names nsf) [:aliases :self] (second nsf))
        defns (keep #(when (or (ck/defn-form? %) (head? % "defmacro")) (defn-parts %)) forms)
        own (set (map :name defns))]
    (into {} (for [{nm :name params :params body :body head :head} defns
                   :let [arities (cond (vector? params) [[params body]]
                                       (seq? params) (for [a (cons params body)
                                                           :when (and (seq? a) (vector? (first a)))]
                                                       [(first a) (rest a)]))]
                   :when (seq arities)]
               ;; a multi-arity fn calls whatever any of its arities calls;
               ;; one arity delegating to another is self-reference, left out
               [nm (disj (into (into #{} (comp (mapcat (fn [[ps b]] (body-refs ps b own)))
                                               (keep #(callee % own names)))
                                     arities)
                               ;; what a macro's expansion names: syntax-quote
                               ;; qualifies it, so it reads as quoted symbols
                               (when (= "defmacro" (name head))
                                 (keep #(when (and (symbol? %) (namespace %)
                                                   (not= "clojure.core" (namespace %)))
                                          (callee % own names))
                                       (tree-seq coll? seq body))))
                         nm)]))))

(defn- home
  "Where a `calls` or `flow` form's fn lives: [its namespace, its simple
  name].  A simple name is the target's."
  [target f]
  (if (namespace f) [(symbol (namespace f)) (symbol (name f))] [target f]))

(defn- reach-path
  "The shortest chain of calls from `f` to `g` in `graph`, through the
  namespace's own fns, as [f ... g]; nil when `f` never reaches `g`."
  [graph f g]
  (loop [frontier [[f]], seen #{f}]
    (when (seq frontier)
      (let [nexts (for [path frontier, h (get graph (peek path)) :when (not (contains? seen h))]
                    (conj path h))]
        (or (first (filter #(= g (peek %)) nexts))
            (recur (vec (filter #(contains? graph (peek %)) nexts))
                   (into seen (map peek nexts))))))))

(defn- ns-context
  "The names a namespace's source brings in, and its defns by name."
  [forms]
  (let [nsf (first (filter #(head? % "ns") forms))
        defns (keep #(when (ck/defn-form? %) (defn-parts %)) forms)]
    {:names (assoc-in (ns-names nsf) [:aliases :self] (second nsf))
     :defns (into {} (map (juxt :name identity)) defns)
     :own (set (map :name defns))}))

(defn- dataflow
  "Where each value in a fn comes from.  `ast` is the fn, lowered and
  uniquified.  A source is [:param i], the fn's i-th parameter, or
  [:call g], what a call to g returns.  Returns {:calls [{:g g :args
  [sources ...]}] :result sources}: each call the fn makes to a named fn,
  with the sources of each argument, and the sources of its result.
  A branch's test flows into its value.  A lambda passed to a fn is given
  that call's other arguments, and so is a fn passed by name."
  [ast self own names]
  (let [calls (atom #{})
        un (fn [xs] (reduce into #{} xs))
        named (fn [a] (when (= :ref (:op a)) (callee (:name a) own names)))]
    (letfn [(src [a env sink]
              (case (:op a)
                :ref (or (get env (:name a))
                         (when-let [g (named a)] (when (not= g self) #{[:call g]}))
                         #{})
                :lit #{}
                :if (un [(src (:test a) env sink) (src (:then a) env sink) (src (:else a) env sink)])
                :do (src (:ret a) env sink)
                :let (src (:body a)
                          (reduce (fn [e [b init]]
                                    (let [v (src init e sink)]
                                      (reduce #(assoc %1 %2 v) e (l/binding-names b))))
                                  env (:bindings a))
                          sink)
                :loop (frame (map (comp first) (:bindings a))
                             (mapv #(src (second %) env sink) (:bindings a))
                             (:body a) env)
                :recur (do (swap! sink conj (mapv #(src % env sink) (:args a))) #{})
                :fn (lambda a env #{})
                :case (un (concat [(src (:scrut a) env sink)]
                                  (map #(src (:body %) env sink) (:clauses a))
                                  (when (:default a) [(src (:default a) env sink)])))
                (:vec :set) (un (map #(src % env sink) (:items a)))
                :map (un (map #(src % env sink) (concat (:keys a) (:vals a))))
                :invoke (invoke a env sink)
                #{}))
            ;; a loop, or the fn itself: its binders take their inits and
            ;; whatever each recur passes, until nothing new arrives
            (frame [names inits body env]
              (loop [ins inits, n 0]
                (let [sink (atom [])
                      v (src body (merge env (zipmap names ins)) sink)
                      ins2 (reduce (fn [acc args] (mapv into acc (concat args (repeat #{}))))
                                   ins @sink)]
                  (if (or (= ins2 ins) (< 8 n)) v (recur ins2 (inc n))))))
            (lambda [a env given]
              (let [sink (atom [])]
                (src (:body a) (merge env (zipmap (:params a) (repeat given))) sink)))
            (invoke [a env sink]
              (let [fa (:fn a), args (:args a)
                    g (named fa)
                    plain (remove #(or (= :fn (:op %)) (named %)) args)
                    given (un (map #(src % env sink) plain))
                    arg-src (fn [x] (cond (= :fn (:op x)) (lambda x env given)
                                          :else (src x env sink)))]
                (cond
                  (= :fn (:op fa))
                  (let [s (atom [])]
                    (src (:body fa) (merge env (zipmap (:params fa) (map #(src % env sink) args))) s))

                  (= g self)
                  (do (swap! sink conj (mapv #(src % env sink) args))
                      (un (map #(src % env sink) args)))

                  :else
                  (let [srcs (mapv arg-src args)]
                    ;; a fn passed by name is called on the other arguments
                    (doseq [x args :let [h (named x)] :when (and h (not= h self))]
                      (swap! calls conj {:g h :args [given]}))
                    (when g (swap! calls conj {:g g :args srcs}))
                    (un (concat srcs [(src fa env sink)]
                                (when g [#{[:call g]}])))))))]
      (let [ps (:params ast)
            v (frame ps (mapv (fn [i] #{[:param i]}) (range (count ps))) (:body ast) {})]
        {:calls (vec @calls) :result v}))))

(defn- flow-facts*
  [ctx f]
  (when-let [{params :params body :body} (get (:defns ctx) f)]
    (let [ast (binding [l/*locals* (:own ctx)]
                (l/uniquify (l/lower (list* 'fn params body))))]
      (assoc (dataflow ast f (:own ctx) (:names ctx)) :arity (count params)))))

(defn flow-facts
  "How data moves through fn `f` of namespace `ns-sym`, read from source:
  {:calls [{:g g :args [sources ...]}] :result sources :arity n}.  A
  source is [:param i] or [:call g].  Nothing is checked."
  [ns-sym f]
  (flow-facts* (ns-context (book/read-forms (source-url ns-sym))) f))

(defn- check-flows
  "Each `flow` form against the source of the namespace its fn is in."
  [{:keys [target flows]} forms forms-of]
  (vec (for [[qf ps chains] flows]
           (let [[hns f] (home target qf)
                 ctx (ns-context (if (= hns target) forms (forms-of hns)))
                 target hns
                 facts (try (flow-facts* ctx f)
                            (catch Throwable ex {:unreadable (or (ex-message ex) (str ex))}))
                 pos (zipmap ps (range))
                 tok #(if (contains? pos %) [:param (pos %)] [:call %])
                 show #(if (= :result %) "result" (str %))
                 unknown (distinct (for [c chains, l c
                                         :when (and (symbol? l) (not (contains? pos l))
                                                    (nil? (namespace l)) (not (contains? (:own ctx) l)))]
                                     l))
                 errors
                 (cond
                   (nil? facts)
                   [(str "the spec gives `" f "` a flow, but " target " defines no fn `" f "`")]

                   (:unreadable facts)
                   [(str "writ cannot follow the data through `" f "`: " (:unreadable facts))]

                   (or (seq unknown) (not= (count ps) (:arity facts)))
                   (concat
                     (for [l unknown]
                       (str "the flow of `" f "` names `" l "`, which is neither a parameter of `" f
                            "` nor a fn of " target))
                     (when (not= (count ps) (:arity facts))
                       [(str "the flow of `" f "` names " (count ps) " parameter(s), but `" f "` takes "
                             (:arity facts))]))

                   :else
                   (distinct
                     (for [c chains, [a b] (partition 2 1 c)
                           :let [t (tok a)
                                 from (if (contains? pos a) (str "`" a "`") (str "`" a "`"))]
                           err [(cond
                                  (= :result b)
                                  (when-not (contains? (:result facts) t)
                                    (str "what `" f "` returns does not come from " from))

                                  (not-any? #(= b (:g %)) (:calls facts))
                                  (str "`" f "` never calls `" b "`")

                                  (not-any? #(and (= b (:g %)) (some (fn [x] (contains? x t)) (:args %)))
                                            (:calls facts))
                                  (str "`" b "` is never given anything that comes from " from))]
                           :when err]
                       err)))]
             (cond-> {:fn qf :chains (mapv #(str/join " -> " (map show %)) chains)
                      :status (if (seq errors) :failed :ok)}
               (seq errors) (assoc :errors (vec errors)))))))

(defn call-graph
  "The call graph of a namespace, read from its source: {f #{g ...}} for
  each of its defns and macros.  The namespace is loaded only so that
  ::alias/k keywords read as they compile; nothing of it is run.  A callee is one of its own fns
  by simple name, or a fn of another namespace, qualified in full.
  clojure.core, host members and self-recursion are left out.  Effect
  code is read too; nothing here is checked."
  [ns-sym]
  (graph-of (book/read-forms (source-url ns-sym))))

(defn- wide-graph
  "The call graph across the project namespaces reachable from ns-sym,
  every fn by its qualified name, so a reach can go from a shell through
  the core it calls into the helpers that core calls.  clojure.* and
  jolt.* are left out, as is a namespace whose source cannot be read."
  [ns-sym forms forms-of]
  (loop [todo [[ns-sym forms]], seen #{}, g {}]
    (if-let [[n fs] (first todo)]
      (if (contains? seen n)
        (recur (rest todo) seen g)
        (let [local (graph-of fs)
              q (fn [x] (if (namespace x) x (symbol (str n) (str x))))
              g (into g (for [[f cs] local] [(q f) (set (map q cs))]))
              libs (distinct (for [cs (vals local), c cs
                                   :let [lib (some-> (namespace c) symbol)]
                                   :when (and lib (not (re-find #"^(clojure|jolt)\." (str lib)))
                                              (not (contains? seen lib)))]
                               lib))
              more (keep (fn [lib] (when-let [fs (try (forms-of lib) (catch Throwable _ nil))] [lib fs])) libs)]
          (recur (concat (rest todo) more) (conj seen n) g)))
      g)))

(defn- check-calls
  "Each `calls` form against the call graph of the namespace its fn is in:
  the target's, read from `forms`, or another's, read by `forms-of`."
  [{:keys [target calls]} forms forms-of]
  (vec (for [[qf gs] (sort-by (comp str first) calls)]
         (let [[hns f] (home target qf)
               ;; a fn of f's own namespace, however it is written, is the
               ;; graph's simple name
               own (fn [g] (if (= (namespace g) (str hns)) (symbol (name g)) g))
               gs (if (map? gs) (update-vals gs #(mapv own %)) (mapv own gs))
               graph (graph-of (if (= hns target) forms (forms-of hns)))
               actual (get graph f)
               names (if (map? gs) (apply concat (vals gs)) gs)
               unknown (first (filter #(and (nil? (namespace %)) (not (contains? graph %))) names))]
           (cond
             (nil? actual)
             {:fn qf :calls gs :status :failed
              :error (str "the spec gives `" qf "` a call set, but " hns " defines no fn `" f "`")}

             unknown
             {:fn qf :calls gs :status :failed
              :error (str "the spec says `" qf "` calls `" unknown "`, but " hns
                          " defines no fn `" unknown "`")}

             (map? gs)
             ;; reach is read across namespaces: a shell reaches a helper
             ;; through the core it calls
             (let [wide (wide-graph hns (if (= hns target) forms (forms-of hns)) forms-of)
                   q (fn [x] (if (namespace x) x (symbol (str hns) (str x))))
                   ;; a path names the shell's own fns simply, as the spec does
                   plain (fn [x] (if (= (namespace x) (str hns)) (symbol (name x)) x))
                   reach (fn [g] (some->> (reach-path wide (q f) (q g)) (mapv plain)))
                   missing (vec (remove reach (:through gs)))
                   reached (vec (keep reach (:not gs)))]
               (if (and (empty? missing) (empty? reached))
                 {:fn qf :calls gs :status :ok}
                 {:fn qf :calls gs :status :failed :unreached missing :reached reached}))

             :else
             (let [declared (set gs)
                   missing (vec (sort-by str (remove actual declared)))
                   extra (vec (sort-by str (remove declared actual)))]
               (if (and (empty? missing) (empty? extra))
                 {:fn qf :calls gs :status :ok}
                 {:fn qf :calls gs :status :failed :missing missing :extra extra})))))))

;; --- machines ----------------------------------------------------------------------

(defn- enum-values
  "Every value of type `t`, when it has only field-less constructors (or
  is Bool), in declaration order; nil otherwise."
  [t data]
  (cond
    (= 'Bool t) [true false]
    (symbol? t)
    (when-let [f (first (filter #(= t (second %)) data))]
      (let [ctors (remove vector? (drop 2 f))]
        (when (every? symbol? ctors)
          (mapv (fn [c] [(keyword (name c))]) ctors))))
    :else nil))

(defn- table-edges
  "[from event to] for each transition the table lists."
  [transitions]
  (for [[s evs] transitions, [ev t] evs] [s ev t]))

(defn- find-path
  "The shortest path of edges from `from` to `to`, never passing through
  `avoid`, as [[s ev t] ...]; nil when there is none.  A path has at least
  one edge."
  [edges from to avoid]
  (loop [frontier (mapv (fn [e] [e]) (filter #(= from (first %)) edges))
         seen #{from}]
    (when (seq frontier)
      (let [done (first (filter #(= to (nth (peek %) 2)) frontier))]
        (or done
            (let [nexts (for [path frontier
                              :let [t (nth (peek path) 2)]
                              :when (and (not (contains? seen t)) (not= t avoid))
                              e edges :when (= t (first e))]
                          (conj path e))]
              (recur (vec nexts) (into seen (map #(nth (peek %) 2) frontier)))))))))

(defn- reachable [edges from]
  (loop [todo [from], seen #{from}]
    (if-let [s (first todo)]
      (let [ts (remove seen (map #(nth % 2) (filter #(= s (first %)) edges)))]
        (recur (into (vec (rest todo)) ts) (into seen ts)))
      seen)))

(defn- find-cycle
  "The first loop a depth-first walk from `from` runs into, as the path
  around it, [a b a]; nil when every walk ends."
  [edges from]
  (let [succ (reduce (fn [m [a _ b]] (update m a (fnil conj []) b)) {} edges)]
    (letfn [(walk [s path on done]
              (reduce (fn [done t]
                        (cond
                          (:cycle done) done
                          (contains? on t) {:cycle (conj (subvec path (first (keep-indexed #(when (= t %2) %1) path))) t)}
                          (contains? done t) done
                          :else (walk t (conj path t) (conj on t) done)))
                      (conj done s)
                      (get succ s)))]
      (:cycle (walk from [from] #{from} #{})))))

(defn- no-final-error
  "From s no final state can be reached, with the loop that keeps it
  there when there is one."
  [edges s]
  (str "from " (pr-str s) " no final state can be reached"
       (when-let [c (find-cycle edges s)]
         (str ": it loops " (str/join " -> " (map pr-str c))))))

(defn- show-path [path]
  (apply str (pr-str (first (first path)))
         (for [[_ ev t] path] (str " -" (pr-str ev) "-> " (pr-str t)))))

(defn- machine-domain
  "[states events] a machine's step is checked over."
  [[_ {:keys [step start transitions final states events]}] {:keys [anns data]}]
  (let [sig (get anns step)
        listed (distinct (concat [start] (keys transitions)
                                 (mapcat vals (vals transitions)) final))]
    [(vec (or states (enum-values (first (:params sig)) data) listed))
     (vec (or events (enum-values (second (:params sig)) data)
              (distinct (mapcat keys (vals transitions)))))]))

(defn- machine-prop
  "The machine's table as one closed proposition, so the adequacy check
  holds each stand-in for the step fn to it as it does to the laws."
  [[_ {:keys [step transitions]} :as m] e]
  (let [[states events] (machine-domain m e)]
    (cons 'and (for [s states, ev events]
                 (list '= (list step (list 'quote s) (list 'quote ev))
                       (list 'quote (get-in transitions [s ev] s)))))))

(defn- check-machine
  "Run the target's step fn over every state and event, against the table,
  then check the table against the machine's own constraints."
  [[nm {:keys [step start transitions final never before]} :as m] e target]
  (let [f (some-> (ns-resolve (the-ns target) step) deref)
        [states events] (machine-domain m e)
        mismatches (vec (for [s states, ev events
                              :let [listed? (contains? (get transitions s) ev)
                                    want (get-in transitions [s ev] s)
                                    got (try (f s ev) (catch Throwable t {:threw (ex-message t)}))]
                              :when (not= want got)]
                          (cond-> {:state s :event ev :expected want :actual got}
                            (not listed?) (assoc :unlisted true))))
        edges (table-edges transitions)
        from-start (reachable edges start)
        errors (vec (concat
                      (for [s states :when (not (contains? from-start s))]
                        (str (pr-str s) " cannot be reached from the start " (pr-str start)))
                      (when (seq final)
                        (for [s states
                              :when (and (contains? from-start s)
                                         (not-any? (reachable edges s) final))]
                          (no-final-error edges s)))
                      (for [[a b] never
                            :let [p (find-path edges a b nil)]
                            :when p]
                        (str (pr-str a) " must never lead to " (pr-str b) ", but it does: "
                             (show-path p)))
                      (for [[a b] before
                            :let [p (when (not= start a) (find-path edges start b a))]
                            :when p]
                        (str (pr-str b) " must be reached only through " (pr-str a) ", but "
                             (show-path p) " avoids it"))))
        base {:machine nm :step step :states (count states) :events (count events)}]
    (if (and (empty? mismatches) (empty? errors))
      (assoc base :status :ok)
      (assoc base :status :failed
                  :mismatches (mapv #(dissoc % :unlisted) mismatches)
                  :shown (mapv (fn [{:keys [state event expected actual unlisted]}]
                                 (str "(" step " " (pr-str state) " " (pr-str event) ") is "
                                      (if (and (map? actual) (:threw actual))
                                        (str "a throw: " (:threw actual))
                                        (pr-str actual))
                                      ", but the table says " (pr-str expected)
                                      (when unlisted " (no transition listed: the state stays)")))
                               mismatches)
                  :errors errors))))

;; --- graphs -----------------------------------------------------------------------

(defn- graph-edges
  "Each edge of a graph as {:from :f :args :pos :key :tos}: the types of the
  arguments beside the state, the state's position among the fn's
  parameters (where `_` marks it, else first), the edge's key as written,
  and its targets in the order the graph lists its states."
  [[_ m]]
  ;; a step of several cases, [{:when ... :to ...} ...], is an edge per
  ;; case, each knowing every case's guard and targets
  (for [[from es] (:edges m), [[f & args :as k] v0] es
        [i v] (if (vector? v0) (map-indexed vector v0) [[nil v0]])
        :let [tos (if (map? v) (:to v) v)
              in-order #(filterv (set %) (keys (:states m)))]]
    (cond-> {:from from :f f :args (vec (remove #{'_} args)) :key k
             :pos (or (first (keep-indexed #(when (= '_ %2) %1) args)) 0)
             :tos (in-order tos)}
      (and (map? v) (:when v)) (assoc :guard (:when v) :else (or (:else v) :keep)
                                      :by (:by v) :own-when (:own-when v))
      (and (map? v) (:changes v)) (assoc :changes (:changes v))
      i (assoc :case (inc i)
               :cases (mapv (fn [c] {:guard (:when c) :tos (in-order (:to c))}) v0)))))

(defn- insert-at [v i x] (vec (concat (take i v) [x] (drop i v))))

(defn- fixed-arg?
  "An edge argument written 'name: not a type to generate, but the spec's
  own value of that name, passed as is -- how an edge gives a fn a fn
  argument, a comparator or a guard, which cannot be generated."
  [a]
  (and (seq? a) (= 'quote (first a)) (symbol? (second a))))

(defn- subst-var
  "`form` with free occurrences of symbol `x` replaced by `e`.  A binder
  of `x` in a let, fn, loop or quantifier stops it."
  [form x e]
  (letfn [(binds? [bs] (some #{x} (mapcat l/binding-names (take-nth 2 bs))))
          (walk [f]
            (cond
              (= x f) e
              (and (seq? f) (= 'quote (first f))) f
              (and (seq? f) (contains? '#{let let* loop loop* forall exists} (first f))
                   (vector? (second f)) (binds? (second f)))
              f
              (and (seq? f) (contains? '#{fn fn*} (first f))
                   (some #(and (vector? %) (some #{x} (mapcat l/binding-names %))) (take 3 f)))
              f
              (seq? f) (apply list (map walk f))
              (vector? f) (mapv walk f)
              (map? f) (into {} (map (fn [[k v]] [(walk k) (walk v)])) f)
              (set? f) (into #{} (map walk) f)
              :else f))]
    (walk form)))

(defn- arg-var
  "A law's name for argument i, of type t: the type's name in lower case,
  unless that is taken or a clojure.core fn a law may call (`keyword`,
  `int`)."
  [t i taken]
  (let [base (if (symbol? t) (str/lower-case (name t)) (str "arg" i))
        v (symbol base)]
    (if (or (contains? taken v) (contains? (ns-publics 'clojure.core) v)) (symbol (str base i)) v)))

(defn- invariants-of
  "The predicates the spec's invariants give state `s` of graph `g`, each
  as [binder pred]."
  [invs g s]
  (for [[g' s' [b] pred] invs :when (and (= g g') (= s s'))] [b pred]))

(defn- guard-of
  "An edge's guard, (fn [state arg ...] test), as its test of the call's
  own arguments: each parameter replaced, all at once, by what the call
  passes in its place."
  [[_ ps body] call-args]
  (let [tmp (vec (for [i (range (count ps))] (symbol (str "guard%" i))))
        body (reduce (fn [b [p t]] (subst-var b p t)) body (map vector ps tmp))]
    (reduce (fn [b [t a]] (subst-var b t a)) body (map vector tmp call-args))))

(defn- guard-clauses
  "The clauses of a guard's test: the parts of a top-level `and`, or
  nothing when there is only one."
  [test]
  (when (and (seq? test) (= 'and (first test)) (< 2 (count test)))
    (vec (rest test))))

(defn- graph-obligations
  "Laws for each edge whose targets are refinements.  One says every value
  of its state goes, by the edge's fn, to a value of one of its targets,
  holding every invariant of the state it lands in.  One per target says
  the step is taken: some value of the state, and some arguments, land
  there.  Without those the graph only bounds the code, and code that
  never leaves its state keeps every bound.  An edge into plain types
  needs no law; the signatures and the static check keep it.

  A guarded edge, {:to #{...} :when (fn [state arg ...] test) :else s},
  is taken only when its test holds: the landing law and each step are
  under the test.  Where it fails the step is refused, and a law says so:
  the state is left as it was (:else :keep, the default) or lands in the
  :else state.  One more law says some value passes the guard, and, for a
  test that is an `and`, one per clause says it fails while the others
  hold, so each clause rules out something of its own."
  [[gname m :as g] refs invs]
  (vec (for [{:keys [from f args tos pos guard else changes by own-when case cases]} (graph-edges g)
             :let [ty #(get (:states m) %)
                   ref-of #(let [t (plain (ty %))] (when (symbol? t) (get refs t)))
                   refined? (every? ref-of tos)
                   ;; a landing in a state with invariants is checked even
                   ;; when the state is a plain type, since edges out of it
                   ;; assume them
                   inv? #(seq (invariants-of invs gname %))
                   landing? (or refined? (some inv? tos))]
             :let [model-step (get-in m [:model :steps f])]
             :when (or landing? guard (seq changes) model-step)
             :let [v (or (:var (ref-of from)) 's)
                   avs (reduce (fn [acc [i t]]
                                 (conj acc (if (fixed-arg? t) (second t) (arg-var t i (set (conj acc v))))))
                               [] (map-indexed vector args))
                   binders (vec (concat [v (ty from)]
                                        (mapcat (fn [a t] (when-not (fixed-arg? t) [a t])) avs args)))
                   call-args (insert-at avs pos v)
                   call (apply list f call-args)
                   ;; each target's predicate, of the call itself: the law
                   ;; reads as the spec would write it, (ascending? (isort xs)),
                   ;; the shape the prover takes apart
                   in (fn [t] (if-let [r (ref-of t)] (subst-var (:pred r) (:var r) call) true))
                   ;; a landing in t holds t's invariants: (and (Hot? ..) (even? ..))
                   in-held (fn [t]
                             (let [ps (for [[b pred] (invariants-of invs gname t)] (subst-var pred b call))]
                               (if (seq ps) (list* 'and (in t) ps) (in t))))
                   held-of (filterv #(seq (invariants-of invs gname %)) tos)
                   lands (fn [ts] (if (next ts) (cons 'or (map in-held ts)) (in-held (first ts))))
                   test (when guard (guard-of guard call-args))
                   ;; the invariants of the state the step leaves hold of it:
                   ;; a step keeps an invariant when it holds before it, and
                   ;; the start holds each, so every run holds them
                   ;; a [state value] start is checked against them; a
                   ;; start named by its state alone may be any value of it,
                   ;; and a graph with no start any value of any state
                   start (:start m)
                   entered? (or (vector? start) (and (keyword? start) (not= from start)))
                   held (let [hs (for [[b pred] (invariants-of invs gname from)] (subst-var pred b v))]
                          (when (and entered? (seq hs)) (if (next hs) (cons 'and hs) (first hs))))
                   pre (cond (and held test) (list 'and held test) held held :else test)
                   under (fn [p] (if pre (list '=> pre p) p))
                   step-name (str gname ":" (name from) ":" f)
                   edge (str step-name (when case (str "#" case)))
                   sfx (when case (str "#" case))
                   tested (get-in m [:tested from])
                   off-proof #(cond-> % tested (assoc :opts {:require :tested :because tested}))]
             law (concat
                   (when landing?
                     (cons (off-proof
                             {:name (symbol edge) :oid (str "edge." gname "." (name from) "." f sfx)
                              :prop (list 'forall binders (under (lands tos)))
                              :explain (str "a " f " from " (name from)
                                            (when test " that passes its guard")
                                            " must land in " (str/join " or " (map name tos))
                                            (when (seq held-of)
                                              (str ", holding the invariant of "
                                                   (str/join " and " (map #(str ":" (name %)) held-of)))))
                              :graph gname
                              :total true})
                           (for [t (when refined? tos)]
                             (cond-> {:name (symbol (str edge "->" (name t)))
                                      :oid (str "step." gname "." (name from) "." f "." (name t))
                                      :prop (list 'exists binders (if pre (list 'and pre (in t)) (in t)))
                                      :explain (str "the graph says a " f " can take " (name from) " to "
                                                    (name t) ", but no generated " (name from) " does")
                                      :step-of gname}
                               (get-in m [:witnesses [from t]])
                               (assoc :witness (get-in m [:witnesses [from t]]))))))
                   ;; a frame: the keys the step may change, and every other
                   ;; key, named by the record or not, as it was
                   (when (seq changes)
                     (let [;; (arg i), the step's i-th argument after the state
                           at (fn [x] (if (and (seq? x) (= 'arg (first x))) (nth avs (dec (second x))) x))
                           paths (mapv #(if (vector? %) (mapv at %) %) changes)]
                       [(off-proof
                          {:name (symbol (str edge ":frame"))
                           :oid (str "frame." gname "." (name from) "." f sfx)
                           :prop (list 'forall binders
                                       (under (if (every? keyword? paths)
                                                (list '= (list* 'dissoc call paths) (list* 'dissoc v paths))
                                                (list '= (list 'writ.spec/without call paths)
                                                      (list 'writ.spec/without v paths)))))
                           :explain (str "a " f " from " (name from) " may change only "
                                         (str/join ", " (map pr-str changes))
                                         ", and must keep everything else as it was")
                           :graph gname})]))
                   ;; the step does to the model what the model's own step does
                   (when model-step
                     (let [view (get-in m [:model :view])]
                       [(off-proof
                          {:name (symbol (str edge ":model"))
                           :oid (str "model." gname "." (name from) "." f sfx)
                           :prop (list 'forall binders
                                       (under (list '= (list view call) (list* model-step (list view v) avs))))
                           :explain (str "a " f " from " (name from) " must do to its " view " what "
                                         model-step " does")
                           :graph gname})]))
                   ;; a step of cases: once, that where no case holds it is
                   ;; refused, and that no two cases hold at once
                   (when (= 1 case)
                     (let [tests (mapv #(guard-of (:guard %) call-args) cases)
                           pairs (for [i (range (count tests)) j (range (inc i) (count tests))] [i j])]
                       (cons (off-proof
                               {:name (symbol (str step-name ":refused"))
                                :oid (str "refused." gname "." (name from) "." f)
                                ;; some case holds, or the state is kept: an
                                ;; implication from "no case holds" starves
                                ;; when the cases cover every input
                                :prop (list 'forall binders
                                            (let [p (list 'or (cons 'or tests) (list '= call v))]
                                              (if held (list '=> held p) p)))
                                :explain (str "when none of its cases holds, a " f " from " (name from)
                                              " must leave it as it was")
                                :graph gname
                                :total true})
                             (for [[i j] pairs]
                               {:name (symbol (str step-name ":cases" (when (next pairs) (str "." (inc i) "." (inc j)))))
                                :oid (str "cases." gname "." (name from) "." f "." (inc i) "." (inc j))
                                :prop (list 'forall binders
                                            (let [p (list 'not (list 'and (nth tests i) (nth tests j)))]
                                              (if held (list '=> held p) p)))
                                :explain (str "cases " (inc i) " and " (inc j) " of " f " from " (name from)
                                              " both hold: a step is in one case at most, or which it takes is"
                                              " left to the code")
                                ;; about the spec's guards, not the code
                                :graph gname :guard-law true}))))
                   (when guard
                     (concat
                       (when (and (nil? case) (or (= :keep else) (ref-of else) (inv? else)))
                         [(off-proof
                            {:name (symbol (str edge ":refused"))
                             :oid (str "refused." gname "." (name from) "." f)
                             :prop (list 'forall binders
                                         (list '=> (if held (list 'and held (list 'not test)) (list 'not test))
                                               (if (= :keep else) (list '= call v) (in-held else))))
                             :explain (str (if by
                                             (str "taken by anyone but " (str/join " or " (sort-by str by))
                                                  (when own-when ", or when its guard fails")
                                                  ",")
                                             "when its guard fails,")
                                           " a " f " from " (name from)
                                           (if (= :keep else)
                                             " must leave it as it was"
                                             (str " must land in " (name else))))
                             :graph gname
                             :total true})])
                       [{:name (symbol (str edge ":when"))
                         :oid (str "guard." gname "." (name from) "." f sfx)
                         :prop (list 'exists binders test)
                         :explain (str "the guard of " f " from " (name from) " never holds: no generated "
                                       (name from) " and arguments pass it, so the step can never be taken")
                         :step-of gname :guard-law true}]
                       (let [cs (guard-clauses test)]
                         (for [[i c] (map-indexed vector cs)]
                           {:name (symbol (str edge ":when." (inc i)))
                            :oid (str "guard." gname "." (name from) "." f sfx "." (inc i))
                            :prop (list 'exists binders
                                        (list* 'and (list 'not c) (concat (take i cs) (drop (inc i) cs))))
                            :explain (str "clause " (pr-str (nth (guard-clauses (nth guard 2)) i))
                                          " of the guard of " f " from " (name from)
                                          " never fails on its own: whenever the other clauses hold,"
                                          " so does it, and it rules out nothing they do not")
                            :step-of gname :guard-law true})))))]
         law)))

(defn- ensures-laws
  "A law per ann with :ensures, `f:ensures`: on arguments of f's parameter
  types that meet its :requires, what f returns meets :ensures."
  [e]
  (vec (for [[f {:keys [requires ensures]}] (sort-by (comp str key) (:contracts e))
             :when ensures
             :let [{:keys [params]} (get (:anns e) f)
                   ;; the contract's own names for the arguments, as it wrote them
                   avs (let [own (vec (butlast (second ensures)))]
                         (if (and (every? symbol? own) (apply distinct? nil own)
                                  (not-any? #{'_ '&} own) (= (count own) (count params)))
                           own
                           (reduce (fn [acc [i t]] (conj acc (arg-var t i (set acc)))) [] (map-indexed vector params))))
                   call (apply list f avs)
                   post (guard-of ensures (conj avs call))
                   pre (when requires (guard-of requires avs))]]
         {:name (symbol (str f ":ensures"))
          :oid (str "ensures." f)
          :prop (list 'forall (vec (interleave avs params)) (if pre (list '=> pre post) post))
          :explain (str "what `" f "` returns must meet its :ensures, " (pr-str (nth ensures 2)))})))

(defn- fits?
  "Does a value of type `a` fit where type `b` is expected?"
  [a b]
  (or (= a b) (and (= 'Nat a) (= 'Int b)) (= 'Any b)))

(defn- same-type-errors
  "States of one plain type: a value of one is a value of the other, so an
  edge between them checks the type and nothing else, and the names say
  more than the graph does."
  [[gname m] refs]
  (let [refined? #(let [t (plain %)] (and (symbol? t) (contains? refs t)))]
    (for [[t ss] (group-by val (:states m))
          :when (and (next ss) (not (refined? t)))
          :let [ss (map key ss)]]
      (str "graph `" gname "`: " (str/join " and " (map pr-str ss)) " are both " (pr-str t)
           ", so nothing tells them apart and a step between them checks only the type;"
           " make each a refinement that says what sets it apart"))))

(defn without
  "m with each of paths taken out: a key, or a path to an entry, which is
  left out of the map that holds it.  What a frame compares."
  [m paths]
  (reduce (fn [m p]
            (cond
              (keyword? p) (dissoc m p)
              (= 1 (count p)) (dissoc m (first p))
              (map? (get-in m (pop p))) (update-in m (pop p) dissoc (peek p))
              :else m))
          m paths))

(defn- graph-flow-errors
  "Each edge's fn must take its state's type, and return its targets'."
  [[gname m :as g] anns refs]
  (let [base #(plain (erase % refs))
        ty #(get (:states m) %)]
    (vec (concat (same-type-errors g refs)
         (for [{:keys [from key changes]} (graph-edges g)
               :when (seq changes)
               :let [t (base (ty from))
                     edge (str "graph `" gname "`: the edge " (pr-str from) " " (pr-str key))]
               err (if (kind/record-type? t)
                     (for [c changes :let [k (if (vector? c) (first c) c)] :when (not (contains? t k))]
                       (str edge ": :changes names " k ", which the record of " (pr-str from)
                            " does not have; name only its keys"))
                     [(str edge ": :changes needs a record state, but " (pr-str from) " is a " (pr-str t)
                           "; a frame names the keys a step may change")])]
           err)
         (for [{:keys [from f args pos key else] tos :tos} (graph-edges g)
               :let [tos (cond-> tos (and else (not= :keep else) (not-any? #{else} tos)) (conj else))
                     proj (get projections f)
                     tup (let [t (base (ty from))] (when (and (seq? t) (= 'Tuple (first t))) (vec (rest t))))
                     sig (if proj
                           (when tup {:params [(base (ty from))] :ret (get tup (proj (count tup)))})
                           (get anns f))
                     edge (str "the edge " (pr-str from) " -" (pr-str key) "->")
                     ps (let [ps (mapv base (:params sig))]
                          (if (< pos (count ps))
                            (into [(nth ps pos)] (concat (take pos ps) (drop (inc pos) ps)))
                            ps))]
               err (cond
                     (and proj (nil? tup))
                     [(str edge " takes `" f "` of " (pr-str from) ", which is a " (pr-str (ty from))
                           ", not a Tuple")]
                     proj
                     (for [t tos :when (not (fits? (base (:ret sig)) (base (ty t))))]
                       (str edge " " (pr-str t) " expects a " (pr-str (base (ty t))) ", but `" f "` of "
                            (pr-str from) " gives a " (pr-str (base (:ret sig)))))
                     (nil? sig) [(str edge " uses `" f "`, which has no ann")]
                     (not= (count ps) (inc (count args)))
                     [(str edge " calls `" f "` with " (inc (count args)) " argument(s), but its ann takes "
                           (count ps))]
                     :else
                     (concat
                       (let [refined? #(let [t (plain (ty %))] (and (symbol? t) (contains? refs t)))]
                         (when (some refined? tos)
                           (for [t tos :when (not (refined? t))]
                             (str edge " lands in " (pr-str t) ", a plain " (pr-str (ty t))
                                  ", beside refined states, so every result is in it and the edge"
                                  " says nothing about where `" f "` goes; make " (pr-str t)
                                  " a refinement"))))
                       (when-not (fits? (base (ty from)) (first ps))
                         [(str edge " passes `" f "` a " (pr-str (base (ty from)))
                               ", but its ann takes " (pr-str (first ps)))])
                       (for [[a p] (map vector args (rest ps))
                             :when (not (fixed-arg? a))
                             :let [a (base a)]
                             :when (not (fits? a p))]
                         (str edge " passes `" f "` a " (pr-str a) ", but its ann takes " (pr-str p)))
                       (for [t tos :when (not (fits? (base (:ret sig)) (base (ty t))))]
                         (str edge " " (pr-str t) " expects a " (pr-str (base (ty t)))
                              ", but `" f "` returns " (pr-str (base (:ret sig))) " by its ann"))))]
           (str "graph `" gname "`: " err))))))

(defn- graph-rule-errors
  "The graph's own rules, over its edges: reachability from :start, a
  :final state from every state reached, :never and :before."
  [[_ m :as g]]
  (let [edges (vec (for [{:keys [from key tos]} (graph-edges g), t tos]
                     [from key t]))
        st (:start m)
        start (if (vector? st) (first st) st)
        from-start (when start (reachable edges start))]
    (vec (concat
           (when start
             (for [s (keys (:states m)) :when (not (contains? from-start s))]
               (str (pr-str s) " cannot be reached from the start " (pr-str start))))
           (when (and start (seq (:final m)))
             (for [s (keys (:states m))
                   :when (and (contains? from-start s) (not-any? (reachable edges s) (:final m)))]
               (no-final-error edges s)))
           (for [[a b] (:never m) :let [p (find-path edges a b nil)] :when p]
             (str (pr-str a) " must never lead to " (pr-str b) ", but it does: " (show-path p)))
           (for [[a b] (:before m)
                 :let [p (when (and start (not= start a)) (find-path edges start b a))]
                 :when p]
             (str (pr-str b) " must be reached only through " (pr-str a) ", but "
                  (show-path p) " avoids it"))
           (let [finals (set (:final m))
                 out (fn [s] (some #(= s (nth % 0)) edges))]
             (for [s (keys (:states m))
                   :when (and (contains? from-start s) (not (finals s)) (not (out s)))]
               (str (pr-str s) " cannot be left and is not final")))))))

(defn- invariant-check
  "A fn of one value that returns the first invariant of state `s` it
  breaks, or nil when it holds them all.  A predicate that throws is
  broken."
  [invs g s spec-ns qualify-form]
  (let [fs (vec (for [[b pred] (invariants-of invs g s)]
                  [pred (binding [*ns* (the-ns spec-ns)]
                          (eval (list 'fn [b] (qualify-form pred))))]))]
    (fn [v]
      (some (fn [[pred f]] (when-not (try (f v) (catch Throwable _ false)) pred)) fs))))

(defn- graph-start-errors
  "A [state value] start: the value, run once, must be in its state and
  hold its invariants."
  [[gname m :as g] spec-ns tenv qualify-form invs]
  (let [st (:start m)]
    (when (vector? st)
      (let [[s expr] st
            expr (qualify-form expr)
            t (get (:states m) s)
            v (try {:ok (binding [*ns* (the-ns spec-ns)] (eval expr))}
                   (catch Throwable ex {:thrown (ex-message ex)}))]
        (cond
          (:thrown v) [(str "graph `" gname "`: the start " (pr-str expr) " throws: " (:thrown v))]
          (not (conforms? t (:ok v) tenv))
          [(str "graph `" gname "`: the start " (pr-str (:ok v)) " is not a " (pr-str t)
                ", the type of " (pr-str s))]
          :else
          (when-let [pred ((invariant-check invs gname s spec-ns qualify-form) (:ok v))]
            [(str "graph `" gname "`: the start " (pr-str (:ok v)) " breaks the invariant of "
                  (pr-str s) ": " (pr-str pred))]))))))

(def ^:private default-depth 20)

(def ^:private guard-draws
  "How many plain draws a run makes for a guarded step before it draws
  from the state's own integers; it makes twice as many of those."
  4)

(defn- graph-runs
  "Walk :runs runs through the graph's real steps.  Each starts at the
  :start value and takes up to :depth steps (default 20): at each, an
  edge out of the current state, chosen by the seed, is called with
  generated arguments.  A run stops early at a state with no edges out.
  Each landing must be a state the edge allows and hold that state's
  invariants.  Returns {:failures [...] :visited #{state ...}}: a failure
  carries the path walked, the value it was at and the reason."
  [[gname m :as g] spec-ns tenv invs qualify-form seed]
  (when-let [n (:runs m)]
    (let [st (:start m)
          _ (when-not (vector? st)
              (fail! "graph `" gname "`: :runs needs a :start of [state value] to walk from"))
          depth (or (:depth m) default-depth)
          edges (group-by :from (graph-edges g))
          checks (into {} (for [s (keys (:states m))]
                            [s (invariant-check invs gname s spec-ns qualify-form)]))
          start-v (try (binding [*ns* (the-ns spec-ns)] (eval (qualify-form (second st))))
                       (catch Throwable _ ::none))
          pick (fn [k r] (gen/generate (gen/choose 0 (dec k)) 30 r))
          ;; a guard compares an argument with the state, most often: a
          ;; payment with the order's total.  On a searching step a draw it
          ;; refuses is tried again, then with the state's own integers and
          ;; their neighbours, so a run gets past a guard a random value
          ;; rarely meets.  Each step's refusal is counted, by edge
          refusals (atom {})
          draw (fn [v args r i]
                 (let [pool (vec (distinct (mapcat (fn [n] [n (inc n) (dec n)])
                                                   (filter integer? (tree-seq coll? seq v)))))]
                   (vec (map-indexed
                          (fn [j t]
                            (if (fixed-arg? t)
                              (second t)
                              (list 'quote
                                    (let [g (type->gen t tenv)
                                          sd (+ r j 1 (* 104729 i))
                                          x (when (and (>= i guard-draws) (seq pool)
                                                       (contains? '#{Nat Int} (plain t)))
                                              (gen/generate (gen/elements pool) 30 sd))]
                                      (if (and (some? x) (conforms? t x tenv)) x (gen/generate g 30 sd))))))
                          args))))
          call-edge (fn [v {:keys [f args pos guard cases]} r search?]
                      (let [ev #(binding [*ns* (the-ns spec-ns)] (eval %))
                            call-args (fn [avs] (insert-at avs pos (list 'quote v)))
                            passes? #(try (boolean (ev (qualify-form (guard-of guard (call-args %)))))
                                          (catch Throwable _ false))
                            ;; every other step takes its first draw, so a
                            ;; run still meets the guard's refusals
                            avs (if (and guard (or search? (odd? r)))
                                  (let [tries (map #(draw v args r %) (range (* 3 guard-draws)))]
                                    (or (first (filter passes? tries)) (first tries)))
                                  (draw v args r 0))
                            call (qualify-form (apply list f (call-args avs)))]
                        (try (cond-> {:v (ev call)}
                               guard (assoc :passes (passes? avs))
                               ;; a step of cases: the targets of whichever case holds
                               cases (assoc :case-tos
                                            (some (fn [c] (when (try (boolean (ev (qualify-form (guard-of (:guard c) (call-args avs)))))
                                                                     (catch Throwable _ false))
                                                            (:tos c)))
                                                  cases)))
                             (catch Throwable ex {:thrown (ex-message ex)}))))
          conforms (fn [s v] (try (conforms? (get (:states m) s) v tenv) (catch Throwable _ false)))
          ;; how many steps each state is from s, by the graph's edges
          preds (reduce (fn [m [from es]] (reduce #(update %1 %2 (fnil conj #{}) from) m (mapcat :tos es)))
                        {} edges)
          steps-to (memoize
                     (fn [s]
                       (loop [d {s 0}, frontier [s], k 1]
                         (let [nxt (distinct (remove d (mapcat preds frontier)))]
                           (if (empty? nxt)
                             d
                             (recur (into d (map #(vector % k) nxt)) nxt (inc k)))))))
          ;; a run toward a state takes, at each step, an edge that brings it
          ;; closer when there is one, and looks for arguments its guard takes
          run (fn [i & [toward]]
                (loop [state (first st), v start-v, path [(first st)], k 0]
                  (let [es (get edges state)
                        es (if-let [d (some-> toward steps-to)]
                             (or (seq (filter (fn [e] (some #(< (get d % ##Inf) (get d state ##Inf)) (:tos e))) es))
                                 es)
                             es)]
                    (if (or (empty? es) (= k depth) (and toward (= state toward)))
                      {:path path}
                      (let [r (+ (or seed 0) (* 7919 i) (* 31 k))
                            {:keys [tos guard else] :as e} (nth es (pick (count es) r))
                            {nv :v thrown :thrown passes :passes case-tos :case-tos} (call-edge v e r (boolean toward))
                            ;; a case refused is no refusal when another case holds
                            refused (and guard (not passes) (not case-tos))
                            tos (if (and guard (not passes) case-tos) case-tos tos)
                            _ (when guard
                                (swap! refusals update [state (:f e)]
                                       (fnil #(update % (if refused :refused :passed) inc)
                                             {:refused 0 :passed 0})))
                            tos (if refused (if (= :keep else) [state] [else]) tos)
                            land (first (filter #(conforms % nv) tos))
                            fail (fn [why] {:path path :value v :reason why})]
                        (cond
                          thrown (fail (str "a " (:f e) " from " (pr-str state) " at " (pr-str v)
                                            " throws: " thrown))
                          (and refused (= :keep else) (not= v nv))
                          (fail (str "a " (:f e) " takes " (pr-str v) " to " (pr-str nv)
                                     ", though its guard fails there and it must leave it as it was"))
                          (nil? land)
                          (fail (str "a " (:f e) " takes " (pr-str v) " to " (pr-str nv)
                                     ", which is in none of " (str/join ", " (map pr-str tos))))
                          :else
                          (if-let [pred ((checks land) nv)]
                            (fail (str "a " (:f e) " takes " (pr-str v) " to " (pr-str nv) ", which breaks"
                                       " the invariant of " (pr-str land) ": " (pr-str pred)))
                            (recur land nv (conj path land) (inc k)))))))))]
      (if (= ::none start-v)
        {:failures [] :visited #{}}
        (let [rs (doall (map run (range n)))
              ;; a final state no run happened to reach: runs toward it,
              ;; until one gets there
              missed (remove (set (mapcat :path rs)) (:final m))
              toward (doall (mapcat (fn [f]
                                      (let [ts (map #(run (+ n %) f) (range n))]
                                        (concat (take-while #(not (some #{f} (:path %))) ts)
                                                (take 1 (drop-while #(not (some #{f} (:path %))) ts)))))
                                    missed))
              rs (concat rs toward)]
          {:failures (vec (distinct (filter :reason rs)))
           :visited (set (mapcat :path rs))
           :refusals @refusals})))))

(defn- vacuous-invariants
  "Invariants the state's own type already says: the prover shows them
  from the refinement alone, without the code, so they constrain
  nothing a landing in the state does not already."
  [[gname m] invs refs data-tenv]
  (vec (for [[g st [b] pred] invs
             :when (and (= gname g) (contains? (:states m) st))
             :let [t (get (:states m) st)
                   r (let [p (plain t)] (when (symbol? p) (get refs p)))
                   prop (if r
                          (list 'forall [b (:base r)]
                                (list '=> (subst-var (:pred r) (:var r) b) pred))
                          (list 'forall [b t] pred))]
             :when (try (try-prove (desugar prop) data-tenv #{} #{}) (catch Throwable _ false))]
         (str "invariant `" g " " st "` is vacuous: " (pr-str t) " already says " (pr-str pred)
              ", so it holds of the state whatever the code does. State what a landing in "
              (pr-str st) " must keep that its type does not."))))

(defn- invariant-errors
  "Each invariant names a graph and a state of it."
  [[gname m] invs]
  (vec (keep (fn [[g state _ _]]
               (when (and (= gname g) (not (contains? (:states m) state)))
                 (str "invariant `" g " " state "` names a state the graph does not have")))
             invs)))

(defn- state-id [s]
  (let [id (-> (str/join "_" (map #(if (keyword? %) (name %) (str %)) (flatten [s])))
               (str/replace #"[^A-Za-z0-9_]" "_"))]
    (if (contains? #{"end" "state" "note"} id) (str id "_") id)))

(defn- state-diagram [{:keys [start transitions final]}]
  (str "stateDiagram-v2"
       "\n  [*] --> " (state-id start)
       (apply str (for [[s ev t] (table-edges transitions)]
                    (str "\n  " (state-id s) " --> " (state-id t) " : " (state-id ev))))
       (apply str (for [s final] (str "\n  " (state-id s) " --> [*]")))))

(defn- graph-diagram [[_ m :as g]]
  (let [st (:start m)
        start (if (vector? st) (first st) st)]
    (str "stateDiagram-v2"
         (apply str (for [[s t] (:states m)]
                      (str "\n  " (state-id s) " : " (name s) ", a " (pr-str t))))
         (when start (str "\n  [*] --> " (state-id start)))
         (apply str (for [{:keys [from key tos]} (graph-edges g), t tos]
                      (str "\n  " (state-id from) " --> " (state-id t) " : "
                           (str/join " " (map str key)))))
         (apply str (for [s (:final m)] (str "\n  " (state-id s) " --> [*]"))))))

(defn- mermaid-id [s]
  (let [id (-> (str s) (str/replace "?" "_Q") (str/replace "!" "_B")
               (str/replace #"[^A-Za-z0-9_]" "_"))]
    (if (contains? #{"end" "graph" "subgraph" "flowchart"} id) (str id "_") id)))

(defn mermaid
  "A mermaid flowchart of a call graph.  Given a namespace, its own call
  graph.  Given a spec namespace, its target's (or opts :target's), with
  the spec's `calls` laid over it: a call the spec does not list is a
  dotted edge marked `not in spec`, and a call it lists that the code does
  not make is an edge marked `missing`.  opts :graph or :machine draws
  that graph or machine of the spec as a mermaid stateDiagram-v2."
  ([ns-sym] (mermaid ns-sym {}))
  ([ns-sym opts]
   (require ns-sym)
   (cond
     (:graph opts)
     (graph-diagram (or (first (filter #(= (:graph opts) (first %)) (:graphs (get @registry ns-sym))))
                        (fail! "`" ns-sym "` has no graph `" (:graph opts) "`")))

     (:machine opts)
     (let [m (:machine opts)
           [_ spec-m] (or (first (filter #(= m (first %)) (:machines (get @registry ns-sym))))
                          (fail! "`" ns-sym "` has no machine `" m "`"))]
       (state-diagram spec-m))

     :else
   (let [e (get @registry ns-sym)
         target (if e (or (:target opts) (:target e)) ns-sym)
         graph (call-graph target)
         declared (into {} (map (fn [[f gs]] [f (set gs)])) (when e (:calls e)))
         edges (concat
                 (for [[f gs] (sort-by (comp str key) graph), g (sort-by str gs)]
                   (if (and (contains? declared f) (not (contains? (declared f) g)))
                     [f "-.->|not in spec|" g]
                     [f "-->" g]))
                 (for [[f gs] (sort-by (comp str key) declared)
                       g (sort-by str gs)
                       :when (and (contains? graph f) (not (contains? (get graph f) g)))]
                   [f "--x|missing|" g]))
         nodes (sort-by str (distinct (concat (keys graph) (mapcat (fn [[f _ g]] [f g]) edges))))]
     (str "flowchart LR"
          (apply str (for [n nodes] (str "\n  " (mermaid-id n) "[\"" n "\"]")))
          (apply str (for [[f arrow g] edges]
                       (str "\n  " (mermaid-id f) " " arrow " " (mermaid-id g)))))))))

(defn- tenv-of [data]
  (into {} (map (fn [f] (let [d (dt/parse f)] [(:name d) (dt/env d)]))) data))

(defn- refines-of [e] (into {} (map (juxt :name identity)) (:refines e)))

(defn- erase
  "A type (or a signature, or a data form) with each refinement replaced
  by its base type."
  [t refines]
  (cond
    (and (symbol? t) (contains? refines (symbol (name t))))
    (erase (:base (get refines (symbol (name t)))) refines)
    (seq? t) (apply list (map #(erase % refines) t))
    (vector? t) (mapv #(erase % refines) t)
    (map? t) (into {} (map (fn [[k v]] [k (erase v refines)])) t)
    :else t))

(defn- unbang
  "t with each ! type as the type it adds NaN to."
  [t]
  (walk/postwalk #(get '{Any! Any Double! Double Float! Float} % %) t))

(defn- sig-str [{:keys [params ret]}]
  (str "[" (str/join " " (map pr-str params)) (when (seq params) " ") "-> " (pr-str ret) "]"))

(defn- calls-str [gs]
  (cond
    (map? gs) (str (when (seq (:through gs)) (str "\n    goes through: " (str/join ", " (:through gs))))
                   (when (seq (:not gs)) (str "\n    never reaches: " (str/join ", " (:not gs)))))
    (seq gs) (str "\n    calls exactly: " (str/join ", " gs))
    :else "\n    calls nothing outside clojure.core"))

(def ^:private elicit-asks
  [[:empty "What should each give for an empty collection or string: nothing, a default, or a refusal?"]
   [:zero-and-negative "What should each do at zero, and with a negative number where one can arrive?"]
   [:absent "When an optional value is missing, what should each do: skip it, use a default, or refuse?"]
   [:precision "How precise must each be, how does it round, and in what units?"]
   [:whole-life (str "Can what happens here be undone, cancelled, repeated, paused, or expire?"
                     " Each is a step the graph should have, or a question to record.")]])

(defn- elicit*
  "The decisions a spec's types raise, as [{:class :ask :fns|:graphs}]."
  [e]
  (let [refs (refines-of e)
        base #(plain (erase % refs))
        coll? #(or (= 'String %) (kind/index-type? %)
                   (and (seq? %) (contains? '#{List Vec Set Map} (first %))))
        opt? #(or (kind/opt-type? %) (and (kind/record-type? %) (some kind/opt-type? (vals %))))
        float? #(contains? '#{Float Double Float! Double!} %)
        ;; a type and every type inside it: (List Int) raises the sign of
        ;; its elements, a record the decisions of its keys
        parts (fn parts [t]
                (cons t (cond (kind/record-type? t) (mapcat parts (vals t))
                              (kind/index-type? t) (parts (:of (kind/index-parts t)))
                              (seq? t) (mapcat parts (rest t))
                              :else nil)))
        fns-where (fn [pred ret?]
                    (vec (sort (for [[f {:keys [params ret]}] (:anns e)
                                     :when (some pred (mapcat (comp parts base) (cond-> params ret? (conj ret))))]
                                 f))))
        by {:empty (fns-where coll? false)
            :zero-and-negative (fns-where #(contains? '#{Int Nat} %) false)
            :absent (fns-where opt? false)
            :precision (fns-where float? true)}
        graphs (vec (sort (map first (:graphs e))))]
    (vec (for [[k ask] elicit-asks
               :let [fs (get by k)]
               :when (if (= :whole-life k) (seq graphs) (seq fs))]
           (if (= :whole-life k)
             {:class k :ask ask :graphs graphs}
             {:class k :ask ask :fns fs})))))

(defn elicit
  "What to ask the spec's owner before the plan is confirmed: the
  decisions its types raise, which the code will make one way or another
  whether anyone chose it.  [{:class :ask :fns [f ...]}] per kind of
  decision, and :graphs for what a run's whole life may hold.  Each answer
  is a law, a state or a step, or a `question` until someone knows."
  [spec-ns]
  (require spec-ns)
  (elicit* (or (get @registry spec-ns) (fail! "`" spec-ns "` is not a spec namespace"))))

(defn plan
  "The spec as a plan a person can read and confirm, from the spec alone:
  each graph's states and steps, each signed fn with the laws that name
  it, its flows and its call set, and each machine.  Nothing is checked,
  and the target need not exist yet."
  [spec-ns]
  (require spec-ns)
  (let [e (or (get @registry spec-ns) (fail! "`" spec-ns "` is not a spec namespace"))
        refs (refines-of e)
        show-type (fn [t] (if-let [r (get refs (plain t))]
                            (str (pr-str t) ", a " (pr-str (:base r)) " where " (pr-str (:pred r)))
                            (pr-str t)))
        names-in (fn [p] (set (filter symbol? (tree-seq coll? seq p))))
        laws-of (fn [f] (for [{:keys [name prop]} (:laws e) :when (contains? (names-in prop) f)] name))
        flows (group-by first (:flows e))
        calls (into {} (:calls e))]
    (str "plan: " spec-ns " for " (:target e)
         (when (= :proved (:require e)) " (every law must be proved)")
         (apply str
                (for [[gname m :as g] (:graphs e)
                      :let [w (+ 2 (apply max 0 (map (comp count str) (keys (:states m)))))]]
                  (str "\n\ngraph `" gname "`"
                       (when-let [st (:start m)] (str "\n  start: " (pr-str st)))
                       "\n  states"
                       (apply str (for [[s t] (:states m)]
                                    (str "\n    " (format (str "%-" w "s") (str s)) (show-type t))))
                       "\n  steps"
                       (apply str (for [{:keys [from key tos guard else by own-when]} (graph-edges g)]
                                    (str "\n    " from " -" key "-> "
                                         (str/join " or " (map str tos))
                                         (when guard
                                           (str (when by (str " by " (str/join " or " (sort-by str by))))
                                                (when (or own-when (not by))
                                                  (str " when " (pr-str (or own-when guard))))
                                                (if (= :keep else)
                                                  ", else it stays"
                                                  (str ", else to " else)))))))
                       (apply str (for [[k label] [[:never "never"] [:before "only through"]]
                                        [a b] (get m k)]
                                    (if (= k :never)
                                      (str "\n  " a " never leads to " b)
                                      (str "\n  " b " is reached only through " a))))
                       (when (seq (:final m))
                         (str "\n  final: " (str/join ", " (map str (:final m)))))
                       ;; each role, and the steps it may take
                       (let [steps (for [[from es] (:edges m), [[f] tos] es
                                         :when (and (map? tos) (:by tos))
                                         r (sort-by str (:by tos))]
                                     [r (str f " from " (name from))])]
                         (when (seq steps)
                           (str "\n  who may do what"
                                (apply str (for [[r ss] (sort-by (comp str key) (group-by first steps))]
                                             (str "\n    " r "  " (str/join ", " (map second ss)))))))))))
         (when (seq (:anns e))
           (str "\n\nfns"
                (apply str
                       (for [[f sig] (sort-by (comp str key) (:anns e))
                             :let [ls (laws-of f)]]
                         (str "\n  " f "  " (sig-str sig)
                              (when-let [c (get-in e [:contracts f :requires])] (str "\n    requires: " (pr-str (nth c 2))))
                              (when-let [c (get-in e [:contracts f :ensures])] (str "\n    ensures: " (pr-str (nth c 2))))
                              (if (seq ls)
                                (str "\n    laws: " (str/join ", " ls))
                                "\n    laws: none")
                              (apply str (for [[_ ps chains] (get flows f), c chains]
                                           (str "\n    flow: "
                                                (str/join " -> " (map #(if (= :result %) "result" (str %)) c)))))
                              (when-let [gs (get calls f)] (calls-str gs)))))))
         (let [outside (sort-by str (remove (set (keys (:anns e)))
                                            (distinct (concat (keys calls) (keys flows)))))]
           (when (seq outside)
             (str "\n\nwiring outside the signed fns"
                  (apply str (for [f outside]
                               (str "\n  " f
                                    (apply str (for [[_ ps chains] (get flows f), c chains]
                                                 (str "\n    flow: "
                                                      (str/join " -> " (map #(if (= :result %) "result" (str %)) c)))))
                                    (when-let [gs (get calls f)] (calls-str gs))))))))
         (when (or (seq (:assumes e)) (seq (:assumptions e)))
           (str "\n\nassumes, of code writ does not check"
                (apply str (for [[q sig] (sort-by (comp str key) (:assumes e))]
                             (str "\n  " q "  " (sig-str sig))))
                (apply str (for [{:keys [name prop]} (:assumptions e)]
                             (str "\n  " name ": " (pr-str prop))))))
         (when (seq (:questions e))
           (str "\n\nopen questions"
                (apply str (for [{:keys [id text blocking]} (:questions e)]
                             (str "\n  " id (when blocking " (blocking)") ": " text)))))
         (apply str (for [[mname m] (:machines e)]
                      (str "\n\nmachine `" mname "`: " (:step m) " steps it from " (pr-str (:start m))
                           (apply str (for [[st evs] (:transitions m), [ev to] evs]
                                        (str "\n  " (pr-str st) " -" (pr-str ev) "-> " (pr-str to)))))))
         (when-let [asks (seq (elicit* e))]
           (str "\n\nask the spec's owner, before the code decides"
                (apply str (for [{:keys [ask fns graphs]} asks]
                             (str "\n  " ask "\n    " (str/join ", " (or fns graphs))))))))))

(defn- erase-data
  "A data form with refinements in its field types erased; the type's and
  constructors' own names are left as they are."
  [f refs]
  (let [[h nm & more] f
        [params ctors] (if (vector? (first more)) [(first more) (rest more)] [nil more])]
    (apply list (concat [h nm] (when params [params])
                        (for [c ctors]
                          (if (seq? c) (apply list (first c) (map #(erase % refs) (rest c))) c))))))

(defn- guard
  "The form saying value `x` meets the refinements inside type `t`, or
  nil when `t` has none."
  [t x refs spec-ns]
  (let [t (plain t)]
    (cond
      (and (symbol? t) (contains? refs t))
      (let [r (get refs t)
            g (guard (:base r) x refs spec-ns)
            p (list (symbol (str spec-ns) (str (:pred-name r))) x)]
        (if g (list 'and g p) p))
      (and (seq? t) (= 'Tuple (first t)))
      (let [gs (vec (keep-indexed (fn [i ct] (guard ct (list 'nth x i) refs spec-ns)) (rest t)))]
        (when (seq gs) (if (next gs) (cons 'and gs) (first gs))))
      (and (seq? t) (contains? '#{List Vec} (first t)))
      (let [el (symbol (str x "-el"))]
        (when-let [g (guard (second t) el refs spec-ns)]
          (list 'every? (list 'fn [el] g) x)))
      :else nil)))

(def ^:private int-window 2000)

(defn- literals
  "The scalars a form mentions: its literals, the values of the constants
  it names, and the same for the spec's own fns it calls, so a generator
  can favour the values a predicate singles out."
  [form spec-ns bodies]
  (loop [todo [form], seen #{}, out #{}]
    (if-let [f (first todo)]
      (let [xs (tree-seq coll? seq f)
            called (for [x xs :when (and (symbol? x) (contains? bodies (symbol (name x)))
                                         (not (contains? seen (symbol (name x)))))]
                     (symbol (name x)))
            consts (for [x xs :when (symbol? x)
                         :let [v (try (ns-resolve (the-ns spec-ns) x) (catch Throwable _ nil))]
                         :when (and (var? v) (bound? v))
                         :let [c @v]
                         :when (or (number? c) (keyword? c) (string? c))]
                     c)
            lits (concat consts (filter #(or (number? %) (keyword? %) (string? %)) xs))]
        (recur (into (vec (rest todo)) (map bodies called)) (into seen called) (into out lits)))
      out)))

(defn- bias-of
  "Per scalar type, the values to favour when generating: the literals,
  and each integer's neighbours, where a bound is decided."
  [lits]
  (let [ints (filter integer? lits)
        near (set (mapcat (fn [n] [(dec n) n (inc n)]) (conj ints 0)))]
    {'Int near
     'Nat (set (filter #(>= % 0) near))
     'Keyword (set (filter keyword? lits))
     'String (set (filter string? lits))}))

(declare lib-pairs)

(defn- code-seeds
  "Per scalar type, the values a target's code mentions -- its own and that
  of the project namespaces it requires, where the prover reads it too: its
  keyword literals and its integer literals with their neighbours.  A law
  generates these now and then, so a branch on `(= :normal reason)` or
  `(< n 3)` is reached even when the type is as wide as Keyword or Any.
  Strings are left out: a namespace's strings are mostly its docs."
  [target]
  (try
    (let [forms (remove #(head? % "ns") (mapcat second (lib-pairs target)))
          xs (tree-seq coll? seq forms)
          kws (set (filter #(and (keyword? %) (nil? (namespace %))) xs))
          ints (set (filter #(and (integer? %) (<= -1000000000 % 1000000000)) xs))
          near (set (mapcat (fn [n] [(dec n) n (inc n)]) ints))]
      {'Keyword kws
       'Int near
       'Nat (set (filter #(>= % 0) near))
       'Any (into kws near)})
    (catch Throwable _ {})))

(def ^:private filter-size
  "The largest size a filtered generator draws at.  test.check's such-that
  grows the size by one each time its predicate refuses a value, so 5000
  refusals would draw vectors 5000 long."
  200)

(defn- starved-error [nm what]
  (ex-info (str "writ could not generate a value of refinement `" nm
                "`: its predicate rejected " what ". Refine its parts"
                " (a refined field, a narrower base type) so values are built"
                " to fit rather than filtered, or give it {:build f}, a fn of"
                " the spec that makes any value of its base one of it.")
           {:writ/error true}))

(def ^:private sizable
  "The size from which a filter's candidates count toward its starving."
  20)

(defn- filtered
  "gen/such-that, as test.check has it -- each refused candidate the next
  one drawn a size larger -- but no larger than filter-size.  A
  refinement's filter (opts from such-that-opts) also starves when fewer
  than one in 200 of its candidates of size 20 or more meet it, after 1000
  of them: the values it finds are the few small ones a random draw
  happens on, such as a receipt with no items, and a law tested on them
  tests little."
  [pred g {:keys [max-tries ex-fn] :as opts}]
  (let [nm (::name opts)
        big (atom [0 0])]
    (gen/->Generator
      (fn [rnd size]
        (loop [rnd rnd, size size, k 0]
          (when (>= k max-tries)
            (throw (ex-fn {:pred pred :gen g :max-tries max-tries})))
          (let [[r1 r2] (random/split rnd)
                sz (min size filter-size)
                tree ((:gen g) r1 sz)
                ok (pred (rose/root tree))]
            (when (and nm (>= sz sizable))
              (let [[t h] (swap! big (fn [[t h]] [(inc t) (if ok (inc h) h)]))]
                (when (and (>= t 1000) (< (* 200 h) t))
                  (throw (starved-error nm (str "all but " h " of the " t " candidates of size "
                                                sizable " or more"))))))
            (if ok
              (rose/filter pred tree)
              (recur r2 (inc size) (inc k)))))))))

(defn- such-that-opts
  "How hard to look for a value of a refinement.  A value can be rare --
  a tag and an exact score together -- so it tries many times, and says
  which refinement starved if it still finds none."
  [nm]
  {:max-tries 5000
   ::name nm
   :ex-fn (fn [_] (starved-error nm "5000 candidates in a row"))})

(defn- fitting
  "A fn that sets the fields of a refinement's value that its predicate
  pins, or nil when it pins none: a conjunct (= :placed (:status o)) sets
  :status, (zero? (:paid o)) sets :paid to 0, (= (:paid o) (:total o))
  gives :paid the value of :total, and a tuple's (first t), (second t)
  and (nth t i) are positions.  The spec's one-line helpers are read
  through, (unpaid? o) as its body.  A value a random one of the base
  rarely meets is then built rather than filtered for; the predicate
  still judges it."
  [r tenv]
  (let [x (:var r)
        form (or (:pred-form r) (when-not (fn? (:pred r)) (:pred r)))
        helpers (::helpers tenv {})
        conjuncts (fn conjuncts [f depth]
                    (cond
                      (and (seq? f) (= 'and (first f))) (mapcat #(conjuncts % depth) (rest f))
                      (and (seq? f) (symbol? (first f)) (= [x] (vec (rest f))) (< depth 4))
                      (if-let [[[p] body] (let [h (get helpers (symbol (name (first f))))]
                                            (when (= 1 (count (first h))) h))]
                        (conjuncts (walk/postwalk-replace {p x} body) (inc depth))
                        [f])
                      :else [f]))
        place (fn [f]
                (when (and (seq? f) (= x (second f)))
                  (let [[h _ b] f n (count f)]
                    (cond (and (keyword? h) (= 2 n)) [:key h]
                          (and (= 'get h) (keyword? b) (= 3 n)) [:key b]
                          (and (= 'first h) (= 2 n)) [:pos 0]
                          (and (= 'second h) (= 2 n)) [:pos 1]
                          (and (= 'nth h) (nat-int? b) (= 3 n)) [:pos b]))))
        lit? #(or (keyword? %) (number? %) (string? %) (nil? %) (boolean? %))
        sets (for [f (conjuncts form 0)
                   :when (seq? f)
                   :let [[h a b] f n (count f)
                         s (cond
                             (and (= '= h) (= 3 n) (place a) (lit? b)) [:const (place a) b]
                             (and (= '= h) (= 3 n) (lit? a) (place b)) [:const (place b) a]
                             (and (= '= h) (= 3 n) (place a) (place b)) [:copy (place a) (place b)]
                             (and (= 'zero? h) (= 2 n) (place a)) [:const (place a) 0]
                             (and (= 'nil? h) (= 2 n) (place a)) [:const (place a) nil]
                             (and (= 'true? h) (= 2 n) (place a)) [:const (place a) true]
                             (and (= 'false? h) (= 2 n) (place a)) [:const (place a) false])]
                   :when s]
               s)]
    (when (seq sets)
      (let [at (fn [v [kind k]] (if (= :key kind) (get v k) (nth v k nil)))
            put (fn [v [kind k] y] (cond (and (= :key kind) (map? v)) (assoc v k y)
                                         (and (= :pos kind) (vector? v) (< k (count v))) (assoc v k y)
                                         :else v))
            ;; the constants first, then the copies, so a copy of a set
            ;; field takes its set value
            ordered (concat (filter #(= :const (first %)) sets) (filter #(= :copy (first %)) sets))]
        (fn [v]
          (if (or (map? v) (vector? v))
            (reduce (fn [v [kind to from]]
                      (put v to (if (= :const kind) from (at v from))))
                    v ordered)
            v))))))

(defn- window-values
  "The values of integer base b in the window around 0 that meet pred."
  [b pred tenv]
  (filterv #(and (conforms? b % tenv) (try (pred %) (catch Throwable _ false)))
           (range (- int-window) (inc int-window))))

(defn- finite-window
  "The values of an integer refinement, when they all lie inside the
  window: none at its edges, so none past them."
  [ok]
  (when (and (seq ok) (not= (first ok) (- int-window)) (not= (peek ok) int-window))
    ok))

(defn- refine-gen
  "Values of a refinement.  An integer one is found once across a window
  and generated in its range, so a narrow range is never starved; any
  other is its base's values, favouring the literals its predicate
  mentions, that satisfy the predicate."
  [{:keys [name base] :as r} pred tenv]
  (let [b (plain base)]
    (if (contains? '#{Int Nat} b)
      (let [ok (or (::window r) (window-values b pred tenv))]
        (cond
          (empty? ok)
          ;; none near 0: a range past the window, such as (<= 5000 q).
          ;; Its values are found from one that is in it -- the spec's own
          ;; numbers first, where such a range starts, then powers of ten
          ;; and two -- and drawn around it
          (let [cands (concat (::spec-ints tenv)
                              (for [k (range 3 19), sgn [1 -1], d [0 1 -1]] (+ d (* sgn (long (Math/pow 10 k)))))
                              (for [k (range 11 62), sgn [1 -1]] (* sgn (bit-shift-left 1 k))))
                anchor (first (filter #(try (and (conforms? b % tenv) (pred %)) (catch Throwable _ false)) cands))]
            (if-not anchor
              (fail! "refinement `" name "` has no value between " (- int-window) " and " int-window
                     ", nor at any number the spec names or any power of ten or two")
              (gen/frequency [[1 (gen/return anchor)]
                              [3 (filtered #(try (and (conforms? b % tenv) (pred %)) (catch Throwable _ false))
                                                (gen/fmap #(+ anchor %) gen/small-integer)
                                                (such-that-opts name))]])))
          (or (= (first ok) (- int-window)) (= (peek ok) int-window))
          (filtered pred (type->gen b tenv) (such-that-opts name))
          :else
          (let [lo (first ok) hi (peek ok)
                spread (if (= (count ok) (inc (- hi lo)))
                         ;; near either bound first, as test.check's sizes
                         ;; grow: the edges of a range are where code breaks
                         (gen/sized (fn [size]
                                      (gen/one-of [(gen/choose lo (min hi (+ lo size)))
                                                   (gen/choose (max lo (- hi size)) hi)])))
                         (gen/elements ok))
                ;; the bounds, and the spec's own numbers, where the code
                ;; decides things: a wall, a paddle's column, a cap
                ok-set (set ok)
                edges (vec (sort (filter ok-set (concat [(first ok) (peek ok)]
                                                        (get-in tenv [::spec-ints] [])))))]
            (gen/frequency [[3 spread] [1 (gen/elements edges)]]))))
      (if (and (kind/index-type? base) (not (data-decl base tenv)))
        ;; a refinement of an index is built a record at a time, each kept
        ;; only when the index with it still meets the predicate, so a
        ;; rule across the records -- no two bookings clash -- is met
        ;; rather than filtered for.  A predicate that dropping a record
        ;; can break is still filtered for, from what was built
        (let [{k :key r :of u :unique} (kind/index-parts base)
              ok? #(try (boolean (pred %)) (catch Throwable _ false))
              built (gen/fmap (fn [rs]
                                (reduce (fn [m x]
                                          (let [m2 (assoc m (get x k) x)]
                                            (if (or (contains? m (get x k))
                                                    (some (fn [f] (some #(= (get x f) (get % f)) (vals m))) u)
                                                    (not (ok? m2)))
                                              m
                                              m2)))
                                        {} rs))
                              (index-records r k tenv))]
          (filtered ok? built (such-that-opts name)))
        (let [g (type->gen base (assoc tenv ::bias (::bias-of-refine tenv)))]
          (if-let [fit (fitting r tenv)]
            ;; set as the predicate pins it, and still judged by it and
            ;; by the base, whose own rule a set field may break
            (filtered #(and (conforms? base % tenv) (pred %)) (gen/fmap fit g) (such-that-opts name))
            (filtered pred g (such-that-opts name))))))))

(defn- int-leaves
  "Paths to the integers inside v, through maps and vectors: their
  values, never a map's keys."
  [v path]
  (cond
    (integer? v) [path]
    (map? v) (mapcat (fn [[k x]] (int-leaves x (conj path k))) v)
    (vector? v) (mapcat (fn [i x] (int-leaves x (conj path i))) (range) v)
    :else []))

(defn- at-boundaries
  "Values of g, and a third of the time with one integer inside set to a
  number the code or the spec compares against, or one either side of it:
  the inputs that tell `<` from `<=`.  A refinement's own generator never
  sees the law's seeds, and a value its :build makes is moved off them,
  so they are put back here.  A change that takes the value out of the
  refinement is undone."
  [g nums ok?]
  (if (empty? nums)
    g
    (gen/frequency
      [[2 g]
       [1 (gen/bind g (fn [v]
                        (let [paths (vec (int-leaves v []))]
                          (if (empty? paths)
                            (gen/return v)
                            (gen/fmap (fn [[p n]] (let [v2 (if (seq p) (assoc-in v p n) n)] (if (ok? v2) v2 v)))
                                      (gen/tuple (gen/elements paths) (gen/elements nums)))))))]])))

(defn- remembering-starved
  "Generator g, which once it starves -- its filter finds no value -- fails
  every draw after with the same error at once, rather than looking as
  hard again for each law."
  [g]
  (let [starved (atom nil)]
    (gen/->Generator
      (fn [rnd size]
        (if-let [e @starved]
          (throw e)
          (try ((:gen g) rnd size)
               (catch clojure.lang.ExceptionInfo e
                 (when (:writ/error (ex-data e)) (reset! starved e))
                 (throw e))))))))

(defn- type-env-of
  "The data types and refinements of a spec entry.  Refinements sit under
  ::refines, apart from the data the prover and the static check read."
  [{:keys [data refines laws] :as e} spec-ns]
  (let [bodies (delay (into {} (for [f (book/read-forms (source-url spec-ns))
                                     :when (and (seq? f) (contains? '#{defn defn-} (first f)))]
                                 [(second f) f])))
        spec-ints (delay (let [ns (filter integer? (literals (concat (map :prop laws) (map :pred refines)
                                                                     (vals @bodies))
                                                             spec-ns @bodies))]
                           (vec (sort (distinct (mapcat (fn [n] [(dec n) n (inc n)]) ns))))))
        ;; the numbers the code and the spec mention, with their neighbours
        boundary-nums (delay (vec (sort (into (set @spec-ints)
                                              (get (code-seeds (:target e)) 'Int)))))]
    (reduce (fn [tenv {:keys [name pred-name] :as r}]
              (let [pred (deref (ns-resolve (the-ns spec-ns) pred-name))
                    ;; an integer refinement's values near 0, found once:
                    ;; its generator draws from them, and when they are
                    ;; all of its values, a collection keyed by it is sized by them
                    window (when (contains? '#{Int Nat} (plain (:base r)))
                             (window-values (plain (:base r)) pred tenv))
                    tenv (assoc-in tenv [::refines name] (cond-> (assoc r :pred pred :pred-form (:pred r)
                                                                        :spec-ns spec-ns)
                                                           window (assoc :window (finite-window window))))
                    bias (bias-of (literals (:pred r) spec-ns @bodies))]
                (assoc-in tenv [::refines name :gen]
                          (remembering-starved
                          (at-boundaries
                          (if-let [b (:build r)]
                            ;; built by the spec's own fn, then checked
                            (let [build (some-> (ns-resolve (the-ns spec-ns) b) deref)]
                              (when-not (fn? build)
                                (fail! "refinement `" name "` is built by `" b "`, which is not a fn of the spec"))
                              (filtered #(try (boolean (pred %)) (catch Throwable _ false))
                                             (gen/fmap build (type->gen (:base r) tenv))
                                             {:max-tries 100
                                              :ex-fn (fn [_] (ex-info (str "the :build of refinement `" name "`, `" b
                                                                           "`, makes values its predicate rejects")
                                                                      {:writ/error true}))}))
                            (refine-gen (cond-> r window (assoc ::window window))
                                        pred (assoc tenv ::bias-of-refine bias ::spec-ints @spec-ints)))
                          @boundary-nums
                          #(try (and (conforms? (:base r) % tenv) (boolean (pred %)))
                                (catch Throwable _ false)))))))
            ;; the spec's one-line fns, which a refinement built to fit
            ;; reads its predicate through
            (cond-> (tenv-of data) (seq refines) (assoc ::helpers (one-line-helpers spec-ns)))
            refines)))

(defn type-env
  "The types a spec declares, for `sample` and `conforms?`."
  [spec-ns]
  (require spec-ns)
  (type-env-of (get @registry spec-ns) spec-ns))

;; --- why a value is not of its type ----------------------------------------------

(defn- one-line-helpers
  "name -> [params body] for the spec's defns of one expression."
  [spec-ns]
  (try
    (into {} (for [f (book/read-forms (source-url spec-ns))
                   :when (and (seq? f) (contains? '#{defn defn-} (first f)))
                   :let [{:keys [name params body]} (defn-parts f)]
                   :when (and (vector? params) (every? symbol? params) (not-any? #{'&} params)
                              (= 1 (count body)))]
               [name [params (first body)]]))
    (catch Throwable _ {})))

(defn- broken-rule
  "Where in predicate form, with env binding its names, the value breaks
  it: [{:rule form :at note} ...] from the outside in, ending at the
  clause that is false.  A spec helper of one expression is read through,
  `and` to the clause that fails, `every?` and `not-any?` to the element
  that breaks them.  nil when it holds or cannot be followed."
  [spec-ns helpers form env depth]
  (let [run (fn [f] (try (let [ks (vec (keys env))]
                           {:ok (apply (binding [*ns* (the-ns spec-ns)] (eval (list 'fn ks f)))
                                       (map env ks))})
                         (catch Throwable e {:thrown (or (ex-message e) (str e))})))
        holds? (fn [f] (let [r (run f)] (and (contains? r :ok) (boolean (:ok r)))))
        fn-body (fn [f] (when (and (seq? f) (contains? '#{fn fn*} (first f)) (vector? (second f))
                                   (= 1 (count (second f))) (= 3 (count f)))
                          [(first (second f)) (nth f 2)]))
        key-of (fn [coll-form x]
                 (let [c (:ok (run (if (and (seq? coll-form) (= 'vals (first coll-form))) (second coll-form) coll-form)))]
                   (when (map? c) (first (keep (fn [[k v]] (when (or (= v x) (= [k v] x)) k)) c)))))]
    (when (and (< depth 8) (seq? form))
      (let [h (first form)]
        (cond
          (and (contains? helpers h) (= (count (first (get helpers h))) (count (rest form))))
          (let [[params body] (get helpers h)]
            (broken-rule spec-ns helpers (walk/postwalk-replace (zipmap params (rest form)) body) env (inc depth)))

          (= 'and h)
          (some (fn [c] (when-not (holds? c)
                          (or (broken-rule spec-ns helpers c env (inc depth)) [{:rule c :env env}])))
                (rest form))

          (and (contains? '#{every? not-any?} h) (= 3 (count form)))
          (let [[_ f coll] form
                pf (:ok (run f))
                xs (:ok (run coll))
                bad (when (and (ifn? pf) (seqable? xs))
                      (first (filter #(let [b (try (boolean (pf %)) (catch Throwable _ (= 'every? h)))]
                                        (if (= 'every? h) (not b) b))
                                     (seq xs))))]
            (when (some? bad)
              (let [[y] (fn-body f)
                    at {:at (if (and (seq? coll) (= 'vals (first coll))) (second coll) coll)
                        :key (key-of coll bad) :elem bad :as y}]
                (if-let [[y body] (fn-body f)]
                  (let [env2 (assoc env y bad)]
                    (if (= 'every? h)
                      (cons at (or (broken-rule spec-ns helpers body env2 (inc depth)) [{:rule body :env env2}]))
                      [at {:rule body :env env2 :holds true}]))
                  [at {:rule (list f bad) :env env :holds (= 'not-any? h)}]))))

          :else nil)))))

(defn- why-not
  "Which rule of its refinement v breaks, when t is one: the clause that
  is false, where in v, and what its parts are.  nil otherwise."
  [t v tenv]
  (let [t (plain t)]
    (when-let [{:keys [base pred-form var spec-ns]} (refinement t tenv)]
      (cond
        (not (conforms? base v tenv)) (why-not base v tenv)
        (and pred-form spec-ns)
        (when-let [steps (seq (broken-rule spec-ns (one-line-helpers spec-ns) pred-form {var v} 0))]
          (let [show (fn [x] (let [s (pr-str x)] (if (> (count s) 160) (str (subs s 0 157) "...") s)))
                run (fn [f env] (try (let [ks (vec (keys env))]
                                       (pr-str (apply (binding [*ns* (the-ns spec-ns)] (eval (list 'fn ks f)))
                                                      (map env ks))))
                                     (catch Throwable e (str "threw: " (ex-message e)))))
                {:keys [rule env holds]} (last steps)]
            (str "it breaks " (pr-str rule) (when holds ", which must not hold")
                 (apply str (for [{:keys [at key elem as]} (butlast steps) :when at]
                              (str ", at " (pr-str at) (when (some? key) (str " key " (pr-str key)))
                                   ", " (if as (str as " = ") "the element ") (show elem))))
                 (apply str (for [a (rest rule)
                                  :when (and (seq? a) (not (contains? '#{fn fn*} (first a))))]
                              (str ", " (pr-str a) " => " (run a env)))))))))))

;; --- instrument --------------------------------------------------------------

(def ^:private originals (atom {}))

(defn- arg-names [v n]
  (let [al (first (filter #(= n (count (take-while (fn [p] (not= '& p)) %)))
                          (:arglists (meta v))))]
    (vec (or al (map #(symbol (str "arg" %)) (range n))))))

(defn- checked
  ([nm f sig tenv argn] (checked nm f sig tenv argn nil))
  ([nm f sig tenv argn {:keys [requires ensures assumed]}]
   (fn [& args]
     (if (and assumed (not *in-code*))
       ;; writ's own call, or the dependency calling itself
       (apply f args)
       (do
         (doseq [[i t a] (map vector (range) (:params sig) args)]
           (when-not (conforms? t a tenv)
             (fail! "`" nm "` argument " (inc i) " (" (nth argn i (str "arg" i)) ") expects "
                    (pr-str t) ", got " (pr-str a))))
         (when (and requires (not ((:f requires) args)))
           (fail! "`" nm "` requires " (pr-str (:test requires)) ", but is called with " (pr-str (vec args))))
         ;; a target fn runs as code, whoever called it; an assumed fn
         ;; runs as the dependency's own
         (let [r (binding [*in-code* (not assumed)] (apply f args))]
           (when-not (conforms? (:ret sig) r tenv)
             (fail! "`" nm "` returns " (pr-str (:ret sig)) ", but returned " (pr-str r)
                    " for arguments " (pr-str (vec args))
                    (when-let [w (try (why-not (:ret sig) r tenv) (catch Throwable _ nil))]
                      (str ": " w))))
           (when (and ensures (not ((:f ensures) (concat args [r]))))
             (fail! "`" nm "` returns " (pr-str r) " for arguments " (pr-str (vec args))
                    ", which breaks its :ensures " (pr-str (:test ensures))))
           r))))))

(defn- default-proof-ns [spec-ns]
  (let [n (name spec-ns)]
    (symbol (if (str/ends-with? n "-spec")
              (str (subs n 0 (- (count n) 5)) "-proof")
              (str n "-proof")))))

(defn- ns-resource [ns-sym]
  (let [base (-> (name ns-sym) (str/replace "-" "_") (str/replace "." "/"))]
    (or (io/resource (str base ".clj")) (io/resource (str base ".cljc")))))

(defn- proof-entry
  "The proof namespace of a spec: opts :proof names it (false for none),
  or it is found by name; nil when there is none."
  [spec-ns proof]
  (let [p (if (some? proof) proof (default-proof-ns spec-ns))]
    (when (and p (or (some? proof) (ns-resource p)))
      (require p)
      (let [pe (or (get @proofs p)
                   (fail! "`" p "` is not a proof namespace: it has no `(proof-of " spec-ns ")` form"))]
        (when-not (= spec-ns (:proves pe))
          (fail! "`" p "` proves `" (:proves pe) "`, not `" spec-ns "`"))
        (assoc pe :ns p)))))

(defn- entry
  ([spec-ns target] (entry spec-ns target nil))
  ([spec-ns target proof]
   (require spec-ns)
   (let [e (get @registry spec-ns)]
     (when-not e
       (fail! "`" spec-ns "` is not a spec namespace: it has no `(spec target-ns)` form"))
     (let [e (assoc (if target (assoc e :target target) e) ::ns spec-ns)]
       (require (:target e))
       (assoc e ::proof (proof-entry spec-ns proof))))))

(defn- assumed-var
  "The var of an assumed fn, its namespace loaded, or nil."
  [q]
  (try (requiring-resolve q) (catch Throwable _ nil)))

(defn- wrap!
  "Wrap the signed fns not already wrapped, and the fns the spec assumes
  signatures for; returns the vars it wrapped."
  [{:keys [target anns assumes] :as e}]
  (let [tenv (type-env-of e (::ns e))]
    (vec (concat
           (for [[nm sig] anns
                 :let [v (ns-resolve (the-ns target) nm)]
                 :when (and v (not (contains? @originals v)))]
             (let [f @v
                   ;; an ann's :requires and :ensures, read as the spec reads a
                   ;; law: its names are the target's fns, then the spec's own
                   compile (fn [form]
                             (when form
                               (let [q (qualify form (set (second form)) (set (keys (ns-publics (the-ns target))))
                                                (set (keys (ns-interns (the-ns (::ns e))))) target (::ns e))]
                                 {:test (nth form 2)
                                  :f (let [g (binding [*ns* (the-ns (::ns e))] (eval q))]
                                       #(apply g %))})))
                   c (get (:contracts e) nm)]
               (swap! originals assoc v f)
               (alter-var-root v (constantly (checked nm f sig tenv (arg-names v (count (:params sig)))
                                                      {:requires (compile (:requires c))
                                                       :ensures (compile (:ensures c))})))
               v))
           (for [[q sig] assumes
                 :let [v (assumed-var q)]
                 :when (and (var? v) (fn? @v) (not (contains? @originals v)))]
             (let [f @v]
               (swap! originals assoc v f)
               (alter-var-root v (constantly (checked q f sig tenv (arg-names v (count (:params sig)))
                                                      {:assumed true})))
               v))))))

(defn- unwrap! [vars]
  (doseq [v vars :when (contains? @originals v)]
    (alter-var-root v (constantly (get @originals v)))
    (swap! originals dissoc v)))

(defn instrument
  "Wrap every fn the spec signs with its runtime argument and return
  checks.  Undo with `unstrument`."
  ([spec-ns] (instrument spec-ns nil))
  ([spec-ns target]
   (let [e (entry spec-ns target)]
     (wrap! e)
     (:target e))))

(defn unstrument
  "Restore the fns `instrument` wrapped."
  ([spec-ns] (unstrument spec-ns nil))
  ([spec-ns target]
   (let [{:keys [target anns]} (entry spec-ns target)]
     (unwrap! (keep #(ns-resolve (the-ns target) %) (keys anns)))
     target)))

;; --- check ---------------------------------------------------------------------

(defn- format-failure [{:keys [law counterexample detail original trial seed error prover-bug proof explain found-by]}]
  (let [pad (apply max 0 (map (comp count str) (keys counterexample)))]
    (str (when prover-bug
           (str "writ bug: law `" law "` was proved (" proof ") but a test refutes it; "
                "please report this with the seed below.\n"))
         "law `" law "` fails"
         (if (seq counterexample)
           (str " for\n"
                (str/join "\n" (map (fn [[k v]] (str "  " k (apply str (repeat (- pad (count (str k))) " "))
                                                     " = " (pr-str v)))
                                    (sort-by (comp str key) counterexample))))
           "")
         "\n"
         (when explain (str "  " explain "\n"))
         (str/join "\n" (map (fn [[t v]] (str "  " (pr-str t) " => " v)) detail))
         (when error (str "  " error))
         (when (and original (not= original counterexample))
           (str "\n  (shrunk from " (pr-str original) ", failing on test " trial ")"))
         (if (= :solver found-by)
           "\n  (found by the solver, when no test did, and confirmed by running the code)"
           (when seed (str "\n  (replay with {:seed " seed "})"))))))

(defn- format-stuck
  "Where a failed proof search got stuck, for a report: the goal it could
  not close, in which induction case, and the facts it had.  A lemma that
  proves the goal from those facts would close it."
  [stuck]
  (let [one (fn [{:keys [case goal facts]}]
              (str "\n  stuck" (when (seq case) (str " in " (str/join ", within " (reverse case))))
                   " on\n      " goal
                   (when (seq facts)
                     (str "\n    given\n" (str/join "\n" (map #(str "      " %) facts))))))]
    (str (apply str (map one (take 2 stuck)))
         (when (seq stuck)
           "\n  A lemma that proves such a goal from what it is given would close it."))))

(defn- unqualify-form
  "form with each namespace-qualified symbol shown by its name."
  [form]
  (walk/postwalk #(if (and (symbol? %) (namespace %)) (symbol (name %)) %) form))

(def ^:private thin-tests
  "Fewer trials than this meeting a law's hypothesis is a thin test."
  20)

(defn format-report
  "The report as text for an agent or a person: what failed and why."
  [{:keys [ok target spec static laws gaps unspecified rejected calls flows machines proof graphs graph-missing
           lemmas off-graph uses problems questions silent baseline-problems]
    contras ::contradictions assumed ::assumed
    ambiguous ::ambiguous explain ::explain}]
  (str "writ.spec: " spec " against " target (if ok ": ok" ": FAILED")
       (when (seq baseline-problems) (str "\n\n" (str/join "\n" baseline-problems) "\n"))
       (when (and proof (pos? (:laws proof)))
         (str "\n  " (:proved proof) " of " (:laws proof) " laws proved"
              (when (and (:general proof) (pos? (:proved proof)))
                (str " (" (:general proof) " for every input, "
                     (- (:proved proof) (:general proof)) " on particular values)"))
              (when (= :proved (:require proof)) " (the spec requires proof)")
              (when-let [ts (seq (filter #(= :test (:evidence %)) laws))]
                (str "; tested, not proved: " (str/join ", " (map :law ts))
                     (when-let [n (some->> (seq (keep :trials ts)) (apply min))]
                       (str " (each on at least " n " inputs)"))))))
       ;; a law that, on its own, tells no wrong answer from the right one
       (apply str (for [{:keys [law fns]} silent]
                    (str "\n  law `" law "` tells none of " (str/join ", " (map #(str "`" % "`'s") fns))
                         " stand-ins from the real fn: on its own it holds of a constant or a"
                         " truncated answer too. Say what the result must be")))
       ;; a clause a test saw come out one way only tests one side of it
       (apply str (for [{:keys [law one-sided trials evidence]} laws
                        :when (= :test evidence)
                        [a side] one-sided]
                    (str "\n  law `" law "`: " (pr-str a) " was never " side " in " trials
                         " trials, nor at an input the solver found. A clause that never turns"
                         " tests one side only: build inputs that turn it, or drop it if it always holds")))
       ;; a test of a law whose hypothesis seldom holds says little
       (apply str (for [{:keys [law held trials evidence]} laws
                        :when (and (= :test evidence) held trials (< held thin-tests))]
                    (str "\n  law `" law "` is thinly tested: its hypothesis held in " held " of "
                         trials " trials. Build inputs that meet it: a refinement, or values"
                         " picked from the ones the law is about")))
       (apply str (for [{:keys [id text blocking]} questions :when (not blocking)]
                    (str "\n  open question `" id "`: " text)))
       ;; what every proof here rests on
       (when (seq assumed)
         (str "\n  assumes, tested but not proved: "
              (str/join ", " (for [{f :fn sig :sig a :assumption} assumed]
                               (if f (str f " " (sig-str sig)) (str a))))))
       (apply str (for [{d :spec n :imported sk :skipped} uses]
                    (str "\n  uses " d ": " n (if (= 1 n) " proved law" " proved laws") " to cite"
                         (apply str (for [[l why] sk]
                                      (str "\n    law `" l "` of " d " is not imported, being unproved: " why))))))
       (apply str (for [{l :lemma p :proof st :status} lemmas :when (= :proved st)]
                    (str "\n  lemma `" l "` proved " p)))
       (apply str (for [{l :law p :proof st :status} laws :when (= :proved st)]
                    (str "\n  law `" l "` proved " p)))
       (apply str (for [{l :law b :because st :status} laws :when b]
                    (if (= :proved st)
                      (str "\n  law `" l "` is marked {:require :tested}, but it is now proved;"
                           " drop the marker so a regression is caught")
                      (str "\n  law `" l "` is only tested: " b))))
       (when explain
         (apply str (for [{l :law st :status stuck :stuck} laws :when (and (= :tested st) (seq stuck))]
                      (str "\n  law `" l "`'s proof search" (subs (format-stuck stuck) 2)))))
       (when ok
         (apply str (for [{f :fn n :laws imps :rejected} rejected]
                      (str "\n  `" f "`: " n (if (= 1 n) " law, " " laws, ")
                           (count imps) " impostors rejected ("
                           (str/join ", " (for [[k c] (sort-by key (frequencies (map :kind imps)))]
                                            (str c " " (name k))))
                           ")"))))
       (when ok
         (apply str (for [{f :fn gs :calls} calls]
                      (str "\n  `" f "` "
                           (cond
                             (map? gs) (str/join "; " (concat
                                                        (when (seq (:through gs))
                                                          [(str "goes through " (str/join ", " (:through gs)))])
                                                        (when (seq (:not gs))
                                                          [(str "never reaches " (str/join ", " (:not gs)))])))
                             (seq gs) (str "calls exactly " (str/join ", " gs))
                             :else "calls nothing outside clojure.core")))))
       (when ok
         (apply str (for [{f :fn cs :chains} flows, c cs]
                      (str "\n  flow of `" f "`: " c))))
       (when ok
         (apply str (for [{m :machine n :states k :events} machines]
                      (str "\n  machine `" m "`: " (* n k) " transitions checked"))))
       (apply str (for [{g :graph n :edges st :status u ::unproved m ::obligations k ::steps run-n :runs held ::held} graphs
                        :when (= :ok st)
                        :let [m (or m 0) u (or u 0) k (or k 0)
                              edges (fn [k] (str k (if (= 1 k) " edge" " edges")))
                              flow (- n m)]]
                    (str "\n  graph `" g "`: "
                         (when run-n (str run-n " runs walked, "))
                         (cond (zero? m) (str (edges n) ", data flow checked against the signatures")
                               (zero? u) (str (edges m) " proved")
                               :else (str (- m u) " of " (edges m) " proved"))
                         (when (pos? k)
                           (str ", each of " (if (= 1 m) "its " "their ") k (if (= 1 k) " step" " steps")
                                " taken"))
                         (when (and (pos? m) (pos? flow))
                           (str ", " flow " more checked against the signatures"))
                         (when (seq held)
                           (str ", holding the invariant of " (str/join " and " (map pr-str held)))))))
       (when-not (:ok static) (str "\n\n" (:error static)))
       (apply str (for [{a :assumption why :why st :status :as r} assumed :when (= :failed st)]
                    (str "\n\n"
                         (or why
                             (str/replace-first (format-failure (assoc r :law a))
                                                (str "law `" a "` fails")
                                                (str "assumption `" a "` does not hold of the code it is about")))
                         (when-not why
                           "\n  An assumption is a claim about code the spec does not check; fix the claim."))))
       (apply str (map #(str "\n\n" %) problems))
       (apply str (for [{[a b] :laws at :at c :call} contras]
                    (str "\n\nlaws `" a "` and `" b "` cannot both hold: at "
                         (str/join ", " (for [[x v] at] (str x " = " (pr-str v))))
                         ", no value of " (pr-str (unqualify-form c)) " meets both, so no code passes them"
                         " together (the solver shows it, and its certificate is checked)."
                         "\n  Fixing the code cannot help; the spec's owner must say which law is meant.")))
       (apply str (for [{:keys [id text blocking]} questions :when blocking]
                    (str "\n\nthe spec is not finished: open question `" id "` blocks the next piece of work"
                         "\n  " text
                         "\n  Ask the spec's owner. Write the answer into the spec as laws or states,"
                         " then remove the question.")))
       (apply str (for [{n :name :keys [where whose]} ambiguous]
                    (str "\n\n`" n "` is defined by " where " and by " target
                         ", so a law cannot tell which one it means."
                         "\n  A law judges the code with the spec's own helpers, never the code's:"
                         "\n  rename " whose " `" n "`.")))
       (when graph-missing
         (str "\n\n`" spec "` declares no state graph. A spec starts from the problem's states"
              " and the steps between them:"
              "\n  (graph name {:states {state Type ...} :edges {state {[fn ArgType ...] #{state ...}}}})"
              "\n  Its states are types, refinements most often; each edge is a fn, proved to take"
              "\n  its state into one of the states it names. A transition table can be a"
              "\n  `machine` instead."))
       (apply str (for [{g :graph :keys [errors rules runs-failed]} graphs]
                    (str (apply str (map #(str "\n\n" %) errors))
                         (when (seq rules)
                           (str "\n\ngraph `" g "` breaks its own rules"
                                (apply str (map #(str "\n  " %) rules))))
                         (when (seq runs-failed)
                           (str "\n\ngraph `" g "` breaks on its runs"
                                (apply str (for [rf runs-failed]
                                             (str "\n  " (:reason rf)
                                                  (when (:path rf)
                                                    (str "\n    walked " (str/join " -> " (map pr-str (:path rf)))))
                                                  "\n    (replay with {:seed " (:seed rf) "})"))))))))
       (apply str (for [{m :machine st :status :keys [shown errors step]} machines
                        :when (= :failed st)]
                    (str (when (seq shown)
                           (str "\n\nmachine `" m "`: `" step "` does not follow its table"
                                (apply str (map #(str "\n  " %) shown))))
                         (when (seq errors)
                           (str "\n\nmachine `" m "`: the table breaks its own constraints"
                                (apply str (map #(str "\n  " %) errors)))))))
       (apply str (for [{f :fn gs :calls :keys [error missing extra unreached reached]} calls
                        :when (or error (seq missing) (seq extra) (seq unreached) (seq reached))]
                    (cond
                      error
                      (str "\n\n" error)

                      (map? gs)
                      (str "\n\nthe call graph of `" f "` is not the one the spec gives"
                           (apply str (for [g unreached]
                                        (str "\n  `" f "` does not reach `" g "`, which the spec says it goes through")))
                           (apply str (for [p reached]
                                        (str "\n  `" f "` reaches `" (peek p) "`, which the spec says it never does: "
                                             (str/join " -> " (cons f (rest p))))))
                           "\n  Call through the layers the spec names instead of around them.")

                      :else
                      (str "\n\nthe call graph of `" f "` is not the one the spec gives"
                           (apply str (for [g missing]
                                        (str "\n  `" f "` does not call `" g
                                             "`, which the spec says it calls")))
                           (apply str (for [g extra]
                                        (str "\n  `" f "` calls `" g
                                             "`, which the spec does not list")))
                           "\n  the spec says `" f "` calls "
                           (if (seq gs) (str "exactly " (str/join ", " gs)) "nothing outside clojure.core")
                           ". Call through the layers the spec names instead of around them."))))
       (apply str (for [{f :fn :keys [errors]} flows :when (seq errors)]
                    (str "\n\nthe flow of `" f "` is not the one the spec gives"
                         (apply str (map #(str "\n  " %) errors))
                         "\n  Pass each step what the step before it returns; the spec names the path"
                         " the data takes.")))
       ;; a target fn that returned a value outside its type is the fault
       ;; to fix first: every law that ran into it fails because of it, so
       ;; it is said once, with one of them, and the rest named after it
       (let [failed (filter #(= :failed (:status %)) laws)
             breach (fn [r] (some (fn [[_ v]] (when (string? v)
                                                (second (re-find #"Writ: `([^`]+)` returns ([^,]+), but returned" v))))
                                  (:detail r)))
             by-fn (group-by breach failed)]
         (str (apply str (for [[f rs] (sort-by (comp str key) (dissoc by-fn nil))
                               :let [ret (some (fn [r] (some (fn [[_ v]] (when (string? v)
                                                                            (nth (re-find #"Writ: `([^`]+)` returns ([^,]+), but returned" v) 2)))
                                                             (:detail r)))
                                               rs)]]
                           (str "\n\n`" f "` returns values outside " ret ": fix it first; laws that fail"
                                " because of it: " (str/join ", " (sort (map (comp str :law) rs)))
                                "\n" (format-failure (first (sort-by (comp count pr-str :counterexample) rs))))))
              (apply str (map #(str "\n\n" (format-failure %)) (get by-fn nil)))))
       (apply str (for [{l :lemma :as lr} lemmas :when (= :failed (:status lr))]
                    (str "\n\n" (str/replace-first (format-failure (assoc lr :law l)) "law `" "lemma `")
                         "\n  A lemma must hold: it is a law about the code, written to help prove the spec.")))
       (apply str (for [{l :lemma why :unproved st :status} lemmas :when (#{:unproved :tested} st)]
                    (str "\n\nlemma `" l "` holds in its tests but is not proved"
                         "\n  the prover: " (or why "no proof found")
                         "\n  A lemma must be proved before a law may cite it: give it a hint,"
                         "\n  or a lemma of its own.")))
       (apply str (for [{l :law why :unproved st :status need :require stuck :stuck} laws :when (= :unproved st)]
                    (str "\n\nlaw `" l "` is tested, not proved, and the "
                         (if need "law" "spec") " requires proof"
                         "\n  the prover: " (or why "no proof found")
                         (format-stuck stuck)
                         "\n  Prove it: state it in terms the prover models, or state the lemma"
                         "\n  it needs as a law of its own.  If it cannot be proved yet, say why"
                         "\n  on the law, and every report will show it:"
                         "\n  (law " l " {:require :tested :because \"...\"} ...)")))
       (apply str (for [{sg :suggestion :as x} (concat lemmas laws) :when sg]
                    (str "\n\n" (if (:lemma x) (str "lemma `" (:lemma x)) (str "law `" (:law x))) "` "
                         (cond
                           (:hint sg) (str "is proved with this hint in the proof namespace:\n  "
                                           (pr-str (:hint sg)))
                           (:lemma sg) (str "is proved with this lemma in the proof namespace; it passes"
                                            " its tests and the prover proves it:\n  " (pr-str (:lemma sg)))
                           :else (str "has no suggestion: " (:none sg))))))
       (apply str (map #(str "\n\nlaw `" (:law %) "` is vacuous: " (:why %)
                             ". A law must say what the code does.")
                       (filter #(= :vacuous (:status %)) laws)))
       (apply str (map (fn [{f :fn [s & more] :survivors}]
                         (str "\n\nthe spec does not pin down `" f "`: every law still holds when it "
                              s
                              (when (seq more)
                                (apply str (map #(str "\n  or when it " %) more)))
                              "\n  State what `" f "` must do, so that a law rejects this."))
                       gaps))
       (when (and ok (seq off-graph))
         (str "\n  not a step of any graph or machine: " (str/join ", " off-graph)))
       (apply str (for [f unspecified]
                    (str "\n\n`" f "` is public, but the spec gives it no signature, so nothing"
                         " checks it.\n  Sign it with `ann` if the plan has it; if it is a helper,"
                         " make it private with defn-.")))))

(def ^:private writ-sources
  "The sources a proof depends on, beside the code and the spec: writ's
  own translation, prover and solver."
  ["writ/lower.clj" "writ/types.clj" "writ/norm.clj" "writ/data.clj" "writ/spec.clj"
   "writ/prove.clj" "writ/prove/term.clj" "writ/prove/rewrite.clj" "writ/prove/translate.clj"
   "writ/prove/scheme.clj" "writ/prove/check.clj" "writ/prove/smt.clj" "writ/prove/symbolic.clj"
   "writ/solve.clj" "writ/solve/pre.clj" "writ/solve/search.clj" "writ/solve/simplex.clj"
   "writ/solve/cert.clj"])

(def ^:private writ-version
  (delay (apply str (map #(or (some-> (io/resource %) slurp) "") writ-sources))))

(defn- spit-whole!
  "Write text to file f whole: to a file of its own first, then renamed
  over f, so two checks writing one cache at once leave one of their
  files, never the two run together, and a reader never sees half of one."
  [f text]
  (let [f (io/file f)
        tmp (io/file (.getParentFile f) (str (.getName f) "." (java.util.UUID/randomUUID) ".tmp"))]
    (try (spit tmp text)
         (when-not (.renameTo tmp f)
           (throw (ex-info (str "could not write " f) {})))
         (finally (when (.exists tmp) (.delete tmp))))))

(defn- cache-file
  "One file per spec and target: a spec checked against several
  implementations keeps a cache for each."
  [dir [spec-ns target]]
  (io/file dir (str spec-ns "--" target ".edn")))

(defn- load-proofs
  "The proof cache for a spec and target, when it was made by this writ:
  {:laws {key result} :traces {law trace}}, or empty.  A law's key holds
  everything its proof can rest on -- the law, its hint, the lemmas it may
  cite, and the definitions it reaches, whole -- so a result is never taken
  for a different law or different code.  A trace is only a candidate:
  the checker replays it against the code as it is now."
  [dir spec-ns version]
  (or (try (let [f (cache-file dir spec-ns)]
             (when (.exists f)
               (let [c (edn/read-string (slurp f))]
                 (when (= version (:version c)) (select-keys c [:laws :traces])))))
           (catch Throwable _ nil))
      {:laws {} :traces {}}))

(defn- save-proofs! [dir spec-ns version cache]
  (try (.mkdirs (io/file dir))
       (spit-whole! (cache-file dir spec-ns) (pr-str (assoc cache :version version)))
       (catch Throwable _ nil)))

(defn- canonical-names
  "t with the names translation makes up -- loop definitions and their
  locals, numbered as they were made -- renumbered in the order they
  appear in t, so editing an earlier fn does not change a later one's."
  [t]
  (let [made? #(and (symbol? %) (re-find #"(%|\$loop)\d+$" (name %)))
        order (distinct (filter made? (tree-seq coll? seq t)))
        ren (zipmap order (map-indexed (fn [i s] (symbol (str "n%" i))) order))]
    (walk/postwalk #(if (made? %) (get ren % %) %) t)))

(defn- reach
  "The definitions law prop reaches, each once, in the order a walk from
  the prop meets them, and the plain data of the names it refers to: all
  its proof can read of the code."
  [ds prop]
  (let [syms (filter symbol? (tree-seq coll? seq prop))
        calls (fn [d] (keep #(when (and (vector? %) (contains? #{:app :dfn} (first %))) (second %))
                            (tree-seq coll? seq (:body d))))]
    (loop [todo (vec (filter #(contains? ds %) syms)), seen #{}, out []]
      (if-let [f (first todo)]
        (if (contains? seen f)
          (recur (subvec todo 1) seen out)
          (recur (into (subvec todo 1) (calls (get ds f))) (conj seen f) (conj out [f (get ds f)])))
        [(canonical-names out)
         (vec (for [x (distinct syms)
                    :when (and (namespace x) (not (contains? ds x)))
                    :let [v (try (resolve x) (catch Throwable _ nil))]
                    :when (and (var? v) (bound? v) (not (fn? @v)))]
                [x @v]))]))))

(defn- cached-contracts
  "The contracts proved for target, from the cache when they were proved
  from the same writ, code, signatures and data; they depend on nothing
  else, so a change to a law or a proof namespace keeps them."
  [dir target key prove]
  (let [f (when dir (io/file dir (str "contracts--" target ".edn")))
        hit (try (when (and f (.exists f))
                   (let [c (edn/read-string (slurp f))]
                     (when (= key (:key c)) (:rules c))))
                 (catch Throwable _ nil))]
    (or hit
        (let [rules (prove)
              data {:key key :rules rules}]
          ;; kept only when it reads back as itself
          (when f
            (try (let [text (pr-str data)]
                   (when (= data (edn/read-string text))
                     (.mkdirs (io/file dir))
                     (spit-whole! f text)))
                 (catch Throwable _ nil)))
          rules))))

(defn- completed
  "A solver's values for bindings bs, a record it gave only the keys its
  formula reads filled from a value of the record's type.  What it fills
  is checked like the rest, by the type and by running the law."
  [ctx bs cex]
  (when cex
    (merge cex
           (into {} (for [[x t] bs
                          :let [v (get cex x)]
                          :when (and (map? v) (not (conforms? t v (:tenv ctx))))
                          :let [g (try (gen/generate (type->gen t (:tenv ctx)) 0 (hash v))
                                       (catch Throwable _ nil))]
                          :when (map? g)]
                      [x (merge g v)])))))

(defn- refuted
  "The law's failure at the counterexample the solver found, confirmed by
  running the law there; nil when there is none, running it holds, or it
  is no value of the law's types.  The prover reads a refinement inside a
  record as its base type, so its model may pick a value the refinement
  rules out, a role no user has: a law says nothing there."
  [ctx r cex]
  (when cex
    (let [[bs body] (leading-foralls (:prop r))
          vars (mapv first bs)
          cex (completed ctx bs cex)]
      (when (and (every? #(contains? cex %) vars)
                 (every? (fn [[x t]] (conforms? t (get cex x) (:tenv ctx))) bs))
        (let [res (try (holds (assoc ctx :vars vars) body cex)
                       (catch Throwable _ nil))]
          (when (= :fail (:result res))
            (-> r
                (dissoc :unproved :trials :discarded)
                (assoc :status :failed :counterexample (select-keys cex vars)
                       :detail (:detail res) :found-by :solver))))))))

(defn- refine->defn
  "A refine form read as the defn of its predicate, which it defines."
  [f]
  (if (head? f "refine")
    (let [[_ nm [v _] pred] f]
      (list 'defn (symbol (str nm "?")) [v] pred))
    f))

(defn- erase-law
  "A law for the prover: each binder of a refined type ranges over the
  base type instead, with the refinement as a hypothesis."
  [prop refs spec-ns]
  (let [[bs body] (leading-foralls prop)
        gs (vec (keep (fn [[x t]] (guard t x refs spec-ns)) bs))]
    (if (empty? gs)
      prop
      (reduce (fn [acc [x t]] (list 'forall [x (erase t refs)] acc))
              (list '=> (if (next gs) (cons 'and gs) (first gs)) body)
              (reverse bs)))))

(defn- thrown? [r]
  (or (:error r) (some (fn [[_ v]] (str/starts-with? (str v) "threw:")) (:detail r))))

(defn- alpha=
  "Do two laws say the same, up to the names of their leading `forall`
  binders?"
  [p q]
  (let [canon (fn [p]
                (loop [p p, bs [], i 0]
                  (if (head? p "forall")
                    (let [[_ [x t] body] p
                          y (symbol (str "_" i))]
                      (recur (subst-var body x y) (conj bs t) (inc i)))
                    [bs p])))]
    (= (canon p) (canon q))))

(defn- assumed-names
  "name -> qualified name for the assumed fns, as a namespace with these
  aliases and refers names them: alias-qualified, referred, or in full."
  [{:keys [aliases refers] :as names} assumed]
  (merge (into {} (for [q assumed] [q q]))
         ;; a clojure.core fn the prover does not model, by its plain name
         ;; where the namespace reads it as core's; one it models keeps its
         ;; model
         (into {} (for [q assumed
                        :when (and (= "clojure.core" (namespace q))
                                   (not (contains? writ.prove.translate/core-fns (symbol (name q))))
                                   (core-name? names (symbol (name q))))]
                    [(symbol (name q)) q]))
         (into {} (for [[a lib] aliases, q assumed :when (= (str lib) (namespace q))]
                    [(symbol (str a) (name q)) q]))
         (into {} (for [[r q] refers :when (contains? assumed q)] [r q]))))

(defn- lib-pairs
  "The target and the project namespaces it requires, transitively, as
  prover pairs [ns forms refers]: refers maps each alias-qualified or
  referred name a namespace uses to the fn it names.  A required namespace
  whose source is not on the classpath -- clojure.core's, jolt's, a
  library's jar -- is left out, and a call into it stays outside, unless
  the spec assumes it: an assumed fn, named any way a namespace may name
  it, is a call the prover keeps, with no definition to unfold."
  ([target] (lib-pairs target #{}))
  ([target assumed]
  (loop [todo [target], seen #{}, out []]
    (if-let [n (first todo)]
      (if (contains? seen n)
        (recur (rest todo) seen out)
        (let [forms (try (book/read-forms (source-url n)) (catch Throwable _ nil))
              nsf (first (filter #(head? % "ns") forms))]
          (if (nil? nsf)
            (recur (rest todo) (conj seen n) out)
            (let [{:keys [aliases refers] :as names} (ns-names nsf)
                  libs (distinct (concat (vals aliases) (map (comp symbol namespace) (vals refers))))
                  project? (fn [lib] (not (re-find #"^(clojure|jolt)\." (str lib))))
                  deps (filter project? libs)
                  defs-in (fn [lib] (set (for [f (try (book/read-forms (source-url lib)) (catch Throwable _ nil))
                                               :when (and (seq? f) (contains? '#{defn defn-} (first f)))]
                                           (second f))))
                  ref-map (merge
                            (into {} (for [[a lib] aliases :when (project? lib)
                                           f (defs-in lib)]
                                       [(symbol (str a) (str f)) (symbol (str lib) (str f))]))
                            (into {} (for [[r q] refers :when (project? (symbol (namespace q)))] [r q]))
                            (assumed-names names assumed))]
              (recur (concat (rest todo) deps) (conj seen n) (conj out [n forms ref-map]))))))
      out))))

(defn- hint-candidates
  "Hints to try on a law over variables vs, cheapest first: induction on
  each, then with one or all of the others free in the hypothesis, each
  strategy on its own, and more fuel.  A hint's :use is kept."
  [vs hint]
  (let [keep-use #(merge (select-keys hint [:use]) %)]
    (distinct
      (map keep-use
           (concat (for [v vs] {:induct v})
                   (for [v vs, w vs :when (not= v w)] {:induct v :vary [w]})
                   (for [v vs :when (< 2 (count vs))] {:induct v :vary (vec (remove #{v} vs))})
                   [{:strategy :symbolic} {:strategy :induction} {:strategy :rewriting}]
                   [{:fuel 80000}])))))

(defn- suggest-proof
  "For a law that is tested and not proved, a hint that proves it, or a
  lemma: {:hint (hint ...)} or {:lemma (lemma ...)}, or {:none why}.  A
  lemma comes from the goals the search got stuck on; it is offered only
  once it has passed its tests, been proved itself, and proved the law.
  Nothing is added to the spec: the proof namespace stays the record."
  [r lemmas attempt** ctx rets hint {:keys [budget] :or {budget 40}}]
  (let [vs (mapv first (first (leading-foralls (:prop r))))
        tries (atom 0)
        spent? #(>= @tries budget)
        prove #(do (swap! tries inc) (attempt** %1 %2 nil %3))
        by-hint (first (for [h (hint-candidates vs hint)
                             :while (not (spent?))
                             :when (:proved (prove r lemmas h))]
                         h))]
    (if by-hint
      {:hint (list 'hint (:law r) by-hint)}
      (let [raw (:stuck-raw (attempt** r lemmas nil))
            cands (take 8 (prover/lemma-candidates raw rets))
            named (symbol (str (:law r) "-needs"))
            found (first
                    (for [{:keys [bindings hyps goal]} cands
                          :while (not (spent?))
                          :let [form (list 'forall (vec (mapcat identity bindings))
                                           (if (seq hyps) (list '=> (if (next hyps) (cons 'and hyps) (first hyps)) goal) goal))
                                prop (desugar form)
                                t (test-law ctx {:name named :prop prop} {:trials 100 :seed 1 :max-size 30})]
                          :when (contains? #{:tested :evaluated} (:status t))
                          :when (:proved (prove {:prop prop :lemma true :law named} lemmas nil))
                          :when (:proved (prove r (conj lemmas {:name named :prop prop}) nil))]
                      form))]
        (if found
          {:lemma (list 'lemma named found)}
          {:none (if (spent?) (str "none found within " budget " attempts") "none found")})))))

(def ^:private ^:dynamic *using*
  "The specs being checked for a spec that uses them, to refuse a cycle."
  #{})

(declare check)

(defn- imports-of
  "What spec-ns imports from the specs its :uses names: {:lemmas [{:name
  :prop}] :tenv :report [{:spec :imported :skipped}]}.  Each is checked
  (from its cache when that holds); a law of one that is proved is a
  lemma here, erased and qualified as it was there, and one only tested
  is not."
  [spec-ns e opts]
  (let [deps (:uses e)]
    (when (some #(contains? (conj *using* spec-ns) %) deps)
      (fail! "`" spec-ns "` uses " (pr-str (vec (filter #(contains? (conj *using* spec-ns) %) deps)))
             ", which uses it back: specs may not use each other in a cycle"))
    (reduce (fn [acc dep]
              (let [r (binding [*using* (conj *using* spec-ns)]
                        (check dep (-> (select-keys opts [:cache :cache-dir :seed :fuel])
                                       (assoc :adequacy false))))
                    proved (::proved-props r)
                    de (get @registry dep)
                    ;; a law that holds but is closed, or only witnessed, has
                    ;; nothing to instantiate: only an unproved forall is missed
                    skipped (vec (for [l (:laws r) :when (contains? #{:tested :unproved :failed} (:status l))]
                                   [(:law l) (or (:unproved l) (name (:status l)))]))]
                (-> acc
                    (update :lemmas into proved)
                    (update :tenv merge (type-env-of de dep))
                    (update :report conj {:spec dep :imported (count proved) :skipped skipped}))))
            {:lemmas [] :tenv {} :report []}
            deps)))

(defn- prove-laws
  "Try to prove each law that ran.  A tested law the prover proves becomes
  :proved; a law it cannot prove keeps :tested with the reason.  A law
  that is proved yet refuted by a value (not a throw) is a writ bug."
  [results opts target spec-ns tenv anns refs ctx]
  (if (= false (:prove opts))
    results
    (let [proof-ns (::proof-ns opts)
          ;; the target's dependencies, which a spec helper or a law may call
          ;; through the spec's own aliases
          assumed (::assumed opts)
          libs+refers (delay
                        (let [libs (lib-pairs target (set (keys (:sigs assumed))))
                              spec-forms (book/read-forms (source-url spec-ns))
                              {:keys [aliases] :as names} (ns-names (first (filter #(head? % "ns") spec-forms)))]
                          [libs spec-forms
                           (merge
                             (into {} (for [[a lib] aliases
                                            [n fs] libs :when (= n lib)
                                            f fs :when (and (seq? f) (contains? '#{defn defn-} (first f)))]
                                        [(symbol (str a) (str (second f))) (symbol (str lib) (str (second f)))]))
                             (assumed-names names (set (keys (:sigs assumed)))))]))
          anns (into {} (map (fn [[k sig]] [k (erase sig refs)])) anns)
          assumed-sigs (into {} (for [[q sig] (:sigs assumed)
                                      :let [sig (erase sig refs)]]
                                  [q {:params (mapv plain (:params sig)) :ret (plain (:ret sig))}]))
          sigs (into assumed-sigs
                     (for [[nm sig] anns]
                       [(symbol (str target) (str nm)) {:params (mapv plain (:params sig)) :ret (plain (:ret sig))}]))
          defs (delay (prover/definitions
                        (cond-> (let [[libs spec-forms spec-refers] @libs+refers]
                                  (conj libs [spec-ns (mapv refine->defn spec-forms) spec-refers]))
                          ;; a proof namespace's own defns, reading the
                          ;; target's fns it refers by their plain names --
                          ;; the fns of the target checked, when a stand-in
                          ;; is checked in place of the spec's own
                          proof-ns (conj [proof-ns (book/read-forms (source-url proof-ns))
                                          (into {} (for [[k v] (ns-refers (the-ns proof-ns))
                                                         :when (contains? #{target (:target (get @registry spec-ns))}
                                                                          (ns-name (:ns (meta v))))]
                                                     [k (symbol (name target) (name k))]))]))
                        sigs))
          ;; what each signed fn returns, proved from its code once: the
          ;; laws' lemmas are instantiated only at terms of their types
          cache-dir (when-not (= false (:cache opts)) (or (:cache-dir opts) ".writ-cache"))
          contracts (delay (let [[ds] @defs]
                             (into (cached-contracts cache-dir target
                                                     [@writ-version (book/read-forms (source-url target)) sigs tenv]
                                                     #(prover/prove-contracts {:defs ds :tenv tenv :sigs sigs}))
                                   ;; an assumed signature is taken at its word
                                   (prover/contract-rules tenv assumed-sigs))))
          ;; a proof found before, from the same law, lemmas and the code it
          ;; reaches, by the same writ, is the same proof
          cached (atom (if cache-dir (load-proofs cache-dir [spec-ns target] @writ-version) {:laws {} :traces {}}))
          fresh (atom false)]
      ;; a law proved here is a lemma for any law proved after it; one that
      ;; is only tested, or that a test refutes, never is.  Passes repeat
      ;; while they prove something new, so a law may cite one that comes
      ;; later in the spec, and no proof can lean on itself: each cites
      ;; only laws whose proofs were finished before it began
      (let [attempt** (fn [r lemmas replay & [hint]]
                      (try (let [[ds own] @defs
                                 hint (or hint (get (::hints opts) (:law r)))]
                             (prover/prove-law {:prop (erase-law (:prop r) refs spec-ns)
                                                :replay replay
                                                :prover (:prover opts)
                                                :hint hint
                                                :fuel (or (:fuel hint) (:fuel opts))
                                                :total (:total r)
                                                :lemma (:lemma r)
                                                :sigs sigs :contracts @contracts
                                                :defs ds :tenv tenv
                                                :target target :own (merge own (nth @libs+refers 2))
                                                ;; a lemma's types erased as the law's are, so a
                                                ;; refinement in both is the same base type
                                                :lemmas (mapv #(update % :prop erase-law refs spec-ns) lemmas)
                                                :rets (into {} (for [[f sig] sigs] [f (:ret sig)]))}))
                           (catch Throwable e
                             {:proved false :reason (str "the prover failed: " (ex-message e))})))
            ;; that a step never throws is proved only by running it
            ;; symbolically, which a recursive fn defeats; its landing is
            ;; then proved by any strategy, and the report says the rest
            ;; was tested
            attempt* (fn [r lemmas replay]
                       (let [pr (attempt** r lemmas replay)]
                         (if (or (:proved pr) (not (:total r)))
                           pr
                           (let [pr2 (attempt** (dissoc r :total) lemmas replay)]
                             (if (:proved pr2)
                               (update pr2 :summary str
                                       ", and it threw on no test (that it never throws is not proved)")
                               pr)))))
            attempt (fn [r lemmas]
                      (let [law-id (pr-str [(:prop r) (get (::hints opts) (:law r)) (:total r)])
                            k (pr-str [(:prop r) (get (::hints opts) (:law r)) (:total r) lemmas (:fuel opts) (:prover opts)
                                       (reach (first @defs) (:prop r)) tenv sigs @contracts])]
                        (or (when-let [pr (get-in @cached [:laws k])] (assoc pr :cached true))
                            ;; a search that failed is kept too: it can only
                            ;; say "not proved", and a counterexample in it is
                            ;; run on the code again before it is believed.
                            ;; The law's last proof is replayed first
                            (let [pr (attempt* r lemmas (get-in @cached [:traces law-id]))]
                              (swap! cached assoc-in [:laws k]
                                     (select-keys pr [:proved :summary :lemmas :reason :counterexample :stuck]))
                              (when (:trace pr) (swap! cached assoc-in [:traces law-id] (:trace pr)))
                              (reset! fresh true)
                              pr))))
            ;; an input that meets a law's hypotheses, from the solver: a
            ;; counterexample to their negation, run to confirm it
            ;; an input of a law's bindings bs that meets h, from the solver:
            ;; a counterexample to its negation, run to confirm it; one apart
            ;; from each input in seen
            meeting
            (fn [r bs h seen]
              (let [vars (mapv first bs)
                    apart (for [w seen] (cons 'or (for [x vars] (list 'not= x (get w x)))))
                    h* (if (seq apart) (list* 'and h apart) h)
                    none (reduce (fn [p [x t]] (list 'forall [x t] p)) (list 'not h*) (reverse bs))
                    cex (completed ctx bs (:counterexample (attempt** {:law (:law r) :prop none} [] nil)))]
                (when (and cex (every? #(contains? cex %) vars)
                           (every? (fn [[x t]] (conforms? t (get cex x) (:tenv ctx))) bs)
                           (= :pass (:result (try (holds (assoc ctx :vars vars) h* cex)
                                                  (catch Throwable _ nil)))))
                  (select-keys cex vars))))
            hyps-of (fn [body] (loop [p body, hs []]
                                 (if (head? p "=>") (recur (nth p 2) (conj hs (nth p 1))) hs)))
            hypothesis-witness
            (fn [r]
              (let [[bs body] (leading-foralls (:prop r))
                    hyps (hyps-of body)
                    h (if (= 1 (count hyps)) (first hyps) (cons 'and hyps))]
                ;; one found input, and then others apart from it: a
                ;; stand-in that agrees with the code at one input is told
                ;; apart at another
                (when (seq hyps)
                  (loop [seen []]
                    (let [w (when (< (count seen) 3) (meeting r bs h seen))]
                      (if w (recur (conj seen w)) (not-empty seen)))))))
            ;; a law only tested, run where a computed term it compares with
            ;; a number is that number or one either side: the inputs that
            ;; tell < from <=, which a generator reaches only by chance
            at-the-boundary
            (fn [r]
              (let [[bs body] (leading-foralls (:prop r))
                    vars (set (map first bs))
                    hyps (hyps-of body)
                    number (fn [x] (cond (integer? x) x
                                         (and (symbol? x) (namespace x))
                                         (let [v (try (some-> (resolve x) deref) (catch Throwable _ nil))]
                                           (when (integer? v) v))))
                    uses-var? (fn [x] (and (coll? x) (some vars (tree-seq coll? seq x))))
                    atoms (->> (tree-seq coll? seq body)
                               (keep (fn [f]
                                       (when (and (seq? f) (contains? '#{< <= > >= =} (first f)) (= 3 (count f)))
                                         (let [[_ a b] f]
                                           (cond (and (number a) (uses-var? b)) [b (number a)]
                                                 (and (number b) (uses-var? a)) [a (number b)])))))
                               distinct (take 3))]
                (first (for [[t c] atoms, n [(dec c) c (inc c)]
                             :let [w (meeting r bs (cons 'and (conj (vec hyps) (list '= t n))) [])
                                   bad (when w (refuted ctx r w))]
                             :when bad]
                         (assoc bad :boundary (list '= t n))))))
            ;; a clause the trials saw come out only one way, turned the
            ;; other by the solver: the law run there, and failing or not,
            ;; the clause counted as seen both ways
            turn-clauses
            (fn [r]
              (let [[bs body] (leading-foralls (:prop r))
                    hyps (hyps-of body)
                    cov (:coverage r)
                    one-sided (for [a (law-atoms body (map first bs))
                                    side [true false]
                                    :when (zero? (get-in cov [a side] 0))]
                                [a side])]
                (loop [[[a side] & more] (take 4 one-sided), r r]
                  (if-not a
                    r
                    (let [w (meeting r bs (cons 'and (conj (vec hyps) (if side a (list 'not a)))) [])
                          bad (when w (refuted ctx r w))]
                      (cond
                        bad (assoc bad :turned [a side])
                        w (recur more (update-in r [:coverage a side] (fnil inc 0)))
                        :else (recur more r)))))))
            open? (fn [r] (and (:prop r) (contains? #{:tested :failed} (:status r))
                               (not (:proof r)) (not (:unproved-final r))))
            ;; one law in a pass: its result, and the lemma it becomes
            ;; when it is proved.  It cites only the laws proved before the
            ;; pass began, so the laws of a pass are tried at once
            step (fn [lemmas r]
                       (if-not (open? r)
                         [r nil]
                         ;; a proved law that says the same is no proof of this one
                         ;; from the code, so it is left out of the search; when
                         ;; the search fails, that law is the proof
                         (let [same? #(alpha= (:prop %) (:prop r))
                               same (first (filter same? lemmas))
                               pr (attempt r (vec (remove same? lemmas)))
                               pr (if (or (:proved pr) (not same))
                                    pr
                                    {:proved true
                                     :summary (str "as law `" (:name same) "`, which says the same"
                                                   (when (:total r)
                                                     ", and it threw on no test (that it never throws is not proved)"))})]
                           (cond
                             (and (:proved pr) (= :tested (:status r)))
                             [(cond-> (-> r (dissoc :unproved :stuck)
                                                    (cond-> (and (:explain opts) (:attempts pr)) (assoc :attempts (:attempts pr)))
                                                    (assoc :status :proved :proof (:summary pr)))
                                          (:cached pr) (assoc :cached true)
                                          (:replayed pr) (assoc :replayed true)
                                          (seq (:lemmas pr)) (assoc :lemmas (:lemmas pr)))
                              {:name (:law r) :prop (:prop r)}]

                             ;; a hypothesis no test met: where the solver
                             ;; finds the law false, running it there says so
                             (and (:no-hypothesis r) (not (:proved pr)) (refuted ctx r (:counterexample pr)))
                             [(dissoc (refuted ctx r (:counterexample pr)) :no-hypothesis) nil]

                             ;; a law whose hypothesis never held would be
                             ;; true of every input and test nothing; the
                             ;; proof stands only when the solver finds an
                             ;; input that meets the hypothesis
                             (and (:proved pr) (:no-hypothesis r))
                             (if-let [w (hypothesis-witness r)]
                               [(cond-> (-> r (dissoc :counterexample :detail :no-hypothesis)
                                                      (assoc :status :proved
                                                             :hypothesis-witness w
                                                             :proof (str (:summary pr) ", and its hypothesis held at "
                                                                         (str/join " and " (map pr-str w))
                                                                         ", which the solver found: no generated input met it")))
                                            (:cached pr) (assoc :cached true)
                                            (seq (:lemmas pr)) (assoc :lemmas (:lemmas pr)))
                                {:name (:law r) :prop (:prop r)}]
                               [r nil])

                             (and (:proved pr) (not (thrown? r)))
                             [(assoc r :prover-bug true :proof (:summary pr)) nil]

                             (and (= :tested (:status r)) (refuted ctx r (:counterexample pr)))
                             [(refuted ctx r (:counterexample pr)) nil]

                             (= :tested (:status r))
                             [(cond-> (assoc r :unproved (:reason pr))
                                          (seq (:stuck pr)) (assoc :stuck (:stuck pr))
                                          (and (:explain opts) (:attempts pr)) (assoc :attempts (:attempts pr))
                                          ;; outside the model: no lemma changes that
                                          (str/starts-with? (str (:reason pr)) "outside")
                                          (assoc :unproved-final true))
                              nil]
                             :else [(assoc r :unproved-final true) nil]))))
            pass (fn [[rs lemmas]]
                   (let [steps (par-map #(step lemmas %) rs)]
                     [(mapv first steps) (into lemmas (keep second steps))]))]
        ;; the proved laws of the specs this one uses come first
        (loop [[rs lemmas] (pass [results (into (vec (::imports opts)) (:lemmas assumed))])]
          (let [[rs2 lemmas2] (pass [rs lemmas])]
            (if (= (count lemmas2) (count lemmas))
              (do (when (and cache-dir @fresh) (save-proofs! cache-dir [spec-ns target] @writ-version @cached))
                  (let [rs2 (mapv #(dissoc % :unproved-final) rs2)
                        rs2 (if (false? (:prove opts))
                              rs2
                              (par-map #(or (when (and (= :tested (:status %)) (not (:lemma %)))
                                           (or (try (at-the-boundary %) (catch Throwable _ nil))
                                               (try (turn-clauses %) (catch Throwable _ nil))))
                                         %)
                                    rs2))]
                    (if (:suggest opts)
                      (mapv #(if (and (= :tested (:status %)) (:unproved %)
                                      (not (str/starts-with? (str (:unproved %)) "outside")))
                               (let [sg (suggest-proof % lemmas2 attempt** ctx
                                                       (into {} (for [[nm sig] anns]
                                                                  [(symbol (str target) (str nm)) (plain (:ret sig))]))
                                                       (get (::hints opts) (:law %))
                                                       (if (map? (:suggest opts)) (:suggest opts) {}))]
                                 (cond-> % sg (assoc :suggestion sg)))
                               %)
                            rs2)
                      rs2)))
              (recur [rs2 lemmas2]))))))))

(def ^:private evidence-of
  {:proved :proof, :evaluated :proof, :witnessed :proof, :tested :test})

(defn- require-evidence
  "Mark each law with the evidence it got (:proof or :test) and what it
  needed.  A law that needs proof and was only tested is :unproved."
  [results laws level]
  (let [opts (into {} (map (juxt :name :opts)) laws)]
    (mapv (fn [r]
            (let [o (get opts (:law r))
                  need (or (:require o) level)
                  ev (evidence-of (:status r))
                  r (cond-> (merge r (select-keys o [:require :because]))
                      ev (assoc :evidence ev))]
              (if (and (= :proved need) (= :test ev))
                (assoc r :status :unproved)
                r)))
          results)))

(defn- proof-coverage [results level]
  {:require level
   :proved (count (filter #(= :proof (:evidence %)) results))
   ;; of those, the ones about every input: a closed law, run on the values
   ;; it names, is an example however it was proved
   :general (count (filter #(and (= :proof (:evidence %)) (::general %)) results))
   :tested (count (filter #(= :test (:evidence %)) results))
   :laws (count results)})

(defn- step-fns
  "The fns a spec's graphs and machines name as steps."
  [e]
  (-> (set (map :step (map second (:machines e))))
      (into (mapcat #(map :f (graph-edges %)) (:graphs e)))
      (into (for [[f _ chains] (:flows e), x (cons f (apply concat chains)) :when (symbol? x)] x))))

(defn- ambiguous-names
  "Names a law could read two ways: a public of the target that the spec,
  or its proof namespace, also defines.  A law's free name resolves to
  the target first, so the spec's helper would silently be replaced by
  the code it is meant to judge."
  [e spec-ns]
  (let [target (:target e)
        publics (set (keys (ns-publics (the-ns target))))
        by (fn [where whose nss]
             (for [n (sort (filter publics nss))] {:name n :where where :whose whose}))]
    (vec (concat (by "the spec" "the spec's" (keys (ns-interns (the-ns spec-ns))))
                 (when-let [p (:ns (::proof e))]
                   (by (str "the proof namespace " p) "the proof namespace's" (keys (proof-own p))))))))

;; --- obligations and records ------------------------------------------------------

;; --- laws that contradict ---------------------------------------------------------

(defn- calls-of
  "The distinct calls in form to fns in the set fs."
  [form fs]
  (set (filter #(and (seq? %) (contains? fs (first %))) (tree-seq coll? seq form))))

(defn- has-term? [form t] (some #(= t %) (tree-seq coll? seq form)))

(defn- ->formula
  "form as a writ.solve formula (or term, with `term?`) over the variable
  y standing for the call c: each part without c is evaluated by ev, so
  what is left is linear arithmetic and logic around c.  nil when some
  part is outside that."
  [form c ev term?]
  (letfn [(t [f]
            (cond
              (= f c) 'y
              (not (has-term? f c)) (let [v (ev f)] (when (int? v) v))
              (and (seq? f) (symbol? (first f)))
              (let [[op & xs] f, ts (map t xs), all? (every? some? ts)]
                (case (name (first f))
                  "+" (when all? (into [:+] ts))
                  "-" (when all? (if (next ts) (into [:-] ts) [:neg (first ts)]))
                  "inc" (when all? [:+ (first ts) 1])
                  "dec" (when all? [:- (first ts) 1])
                  "*" (when (and all? (= 2 (count ts)))
                        (let [[a b] ts]
                          (cond (int? a) [:* a b] (int? b) [:* b a])))
                  nil))
              :else nil))
          (p [f]
            (cond
              (not (has-term? f c)) (boolean (ev f))
              (and (seq? f) (symbol? (first f)))
              (let [op (name (first f)), xs (rest f)]
                (case op
                  ("and" "or") (let [ps (map p xs)] (when (every? some? ps) (into [(keyword op)] ps)))
                  "not" (when-let [q (p (first xs))] [:not q])
                  "=>" (let [[a b] (map p xs)] (when (and (some? a) (some? b)) [:=> a b]))
                  ("=" "<" "<=" ">" ">=" "not=")
                  (let [ts (map t xs)]
                    (when (and (every? some? ts) (< 1 (count ts)))
                      (if (= "not=" op) [:not (into [:=] ts)] (into [(keyword op)] ts))))
                  nil))
              :else nil))]
    (if term? (t form) (p form))))

(defn- contradictions
  "Pairs of laws no code could satisfy together.  For a failing law and
  another law about the same fn, each saying what one call of it returns,
  the call is replaced by an unknown result at generated inputs, every
  other part evaluated, and the solver asked whether any result meets
  both.  A pair is reported only with the solver's certificate that none
  does, checked, so it is never a guess from samples."
  [laws results signed ev gen-of rets seed]
  (let [status (into {} (map (juxt :law :status)) results)
        shape (fn [{:keys [name prop]}]
                (let [[bs body] (leading-foralls (desugar prop))
                      cs (calls-of body signed)]
                  (when (and (seq bs) (= 1 (count cs))
                             (= 1 (count (set (map first cs)))))
                    {:name name :binders bs :body body :call (first cs)})))
        shapes (keep shape laws)
        order (into {} (map-indexed (fn [i l] [(:name l) i])) laws)
        pairs (for [a shapes :when (= :failed (status (:name a)))
                    b shapes :when (and (not= (:name a) (:name b))
                                        (= (first (:call a)) (first (:call b))))
                    :let [bargs (rest (:call b)) bvars (set (map first (:binders b)))]
                    :when (and (= (count bargs) (count (rest (:call a))))
                               (every? bvars bargs) (apply distinct? bargs)
                               (= bvars (set bargs)))]
                [a b])
        at-value (fn [form bs vals] (reduce (fn [f [[x] v]] (subst-var f x (list 'quote v)))
                                            form (map vector bs vals)))
        found (for [[a b] pairs
                    :let [f (first (:call a))
                          ret (get rets f)]
                    :when (contains? '#{Int Nat} ret)
                    i (range 30)
                    :let [vals (mapv (fn [[_ t] j] (gen/generate (gen-of t) (min 30 (* 2 i)) (+ seed (* 97 i) j)))
                                     (:binders a) (range))
                          argv (try (mapv ev (rest (at-value (:call a) (:binders a) vals)))
                                    (catch Throwable _ nil))]
                    :when argv
                    ;; one call, f of the argument values, stands in both laws
                    :let [c (apply list f (map #(list 'quote %) argv))
                          body-a (walk/prewalk-replace {(at-value (:call a) (:binders a) vals) c}
                                                       (at-value (:body a) (:binders a) vals))
                          body-b (at-value (:body b) (map vector (rest (:call b))) argv)
                          safe-ev #(try (ev %) (catch Throwable _ ::none))
                          fa (->formula body-a c safe-ev false)
                          fb (->formula body-b c safe-ev false)]
                    :when (and (some? fa) (some? fb))
                    :let [form [:and fa fb (if (= 'Nat ret) [:>= 'y 0] true)]
                          res (try (solve/check form {'y :int} {:budget 2000}) (catch Throwable _ nil))]
                    :when (and (= :unsat (:result res))
                               (try (solve/verify form {'y :int} (:certificate res)) (catch Throwable _ false)))]
                {:laws (mapv :name (sort-by #(order (:name %)) [a b]))
                 :at (zipmap (map first (:binders a)) vals)
                 :failing (:name a)
                 :call (:call a)})]
    (vec (vals (reduce (fn [m c] (if (contains? m (:laws c)) m (assoc m (:laws c) c))) (sorted-map) found)))))


(defn- names-in [form]
  (set (filter symbol? (tree-seq coll? seq form))))

(defn- obligations*
  "Every obligation of a registry entry, each {:id :kind :of :fns :text},
  and :law for one a law of the check decides."
  [e]
  (let [refs (refines-of e)
        signed (set (keys (:anns e)))
        fns-of (fn [form] (into (sorted-set) (filter signed) (names-in form)))
        glaws (concat (ensures-laws e) (mapcat #(graph-obligations % refs (:invariants e)) (:graphs e)))
        law-oids (set (keep :oid glaws))]
    (vec (concat
           (for [{:keys [name prop]} (:laws e)]
             {:id (str "law." name) :kind :law :of name :law name :fns (fns-of prop) :text (pr-str prop)})
           (for [[f sig] (sort-by (comp str key) (:anns e))]
             {:id (str "signature." f) :kind :signature :of f :fns #{f} :text (sig-str sig)})
           (for [{:keys [name oid prop explain]} (ensures-laws e)]
             {:id oid :kind :ensures :of name :law name :fns (fns-of prop) :text explain})
           (for [[gname m :as g] (:graphs e)
                 o (concat
                     (for [{:keys [name oid prop explain]} (graph-obligations g refs (:invariants e))]
                       {:id oid :kind (keyword (first (str/split oid #"\."))) :of gname :law name
                        :fns (fns-of prop) :text explain})
                     ;; an edge into plain types has no law: it is data flow, checked
                     ;; against the signatures
                     (for [{:keys [from f]} (graph-edges g)
                           :let [id (str "edge." gname "." (name from) "." f)]
                           :when (not (contains? law-oids id))]
                       {:id id :kind :edge :of gname :fns (fns-of [f])
                        :text (str "a " f " from " (name from) " gives a value of its targets' type")})
                     (when (:start m)
                       [{:id (str "reach." gname) :kind :reach :of gname :fns #{}
                         :text "every state is reached from the start"}])
                     (when (vector? (:start m))
                       [{:id (str "start." gname) :kind :start :of gname :fns #{}
                         :text (str "the start " (pr-str (second (:start m))) " is in " (pr-str (first (:start m))))}])
                     (when (and (:start m) (seq (:final m)))
                       [{:id (str "final." gname) :kind :final :of gname :fns #{}
                         :text (str "a final state (" (str/join ", " (map pr-str (:final m)))
                                    ") is reached from every state, and every state it leaves is left")}])
                     (for [[a b] (:never m)]
                       {:id (str "never." gname "." (name a) "." (name b)) :kind :never :of gname :fns #{}
                        :text (str (pr-str a) " never leads to " (pr-str b))})
                     (for [[a b] (:before m)]
                       {:id (str "before." gname "." (name a) "." (name b)) :kind :before :of gname :fns #{}
                        :text (str (pr-str b) " is reached only through " (pr-str a))})
                     (for [[g' st _ pred] (:invariants e) :when (= g' gname)]
                       {:id (str "invariant." gname "." (name st)) :kind :invariant :of gname
                        :fns #{} :text (pr-str pred)})
                     (when (:runs m)
                       [{:id (str "runs." gname) :kind :runs :of gname
                         :fns (into (sorted-set) (map :f (graph-edges g)))
                         :text (str (:runs m) " runs from the start keep to the graph and reach every final state")}]))]
             o)
           (for [f (distinct (map first (:flows e)))]
             {:id (str "flow." f) :kind :flow :of f :fns #{f} :text (str "the path data takes through " f)})
           (for [[f gs] (:calls e)]
             {:id (str "calls." f) :kind :calls :of f :fns #{f} :text (pr-str gs)})
           (for [[mname m] (:machines e)]
             {:id (str "machine." mname) :kind :machine :of mname :fns #{(:step m)}
              :text (str (:step m) " steps by the table")})
           (for [{:keys [id text blocking]} (:questions e)]
             {:id (str "question." id) :kind :question :of id :fns #{} :text text :blocking blocking})
           (for [[q sig] (sort-by (comp str key) (:assumes e))]
             {:id (str "assume." q) :kind :assumption :of q :fns #{} :text (sig-str sig)})
           (for [{:keys [name prop]} (:assumptions e)]
             {:id (str "assume." name) :kind :assumption :of name :fns #{} :text (pr-str prop)})))))

(defn obligations
  "Every obligation the spec sets, from the spec alone, as data an agent
  can track: [{:id :kind :of :fns :text} ...].  An id reads kind.subject:
  law.name, signature.f, edge.graph.state.f, step.graph.state.f.target,
  guard.graph.state.f (and .n for each clause), refused.graph.state.f,
  frame.graph.state.f, ensures.f,
  invariant.graph.state, reach.graph, start.graph, final.graph,
  never.graph.a.b, before.graph.a.b, runs.graph, flow.f, calls.f,
  machine.m, question.q, assume.ns/f and assume.name.  :fns are the
  signed fns it names.  The target
  need not exist."
  [spec-ns]
  (require spec-ns)
  (obligations* (or (get @registry spec-ns) (fail! "`" spec-ns "` is not a spec namespace"))))

(defn- obligation-status
  "What a check's report says of each obligation: :met, :failed,
  :unproved (it needs proof, and is only tested) or, for a question,
  :open or :blocking."
  [os {:keys [laws static graphs flows calls machines assumptions]}]
  (let [by-law (into {} (map (juxt :law :status)) laws)
        graph-ok (into {} (map (juxt :graph #(= :ok (:status %)))) graphs)
        ok-of (fn [rs k] (into {} (map (juxt k #(= :ok (:status %)))) rs))
        flow-ok (ok-of flows :fn) call-ok (ok-of calls :fn) machine-ok (ok-of machines :machine)
        held (into {} (map (juxt #(or (:fn %) (:assumption %)) #(= :held (:status %)))) assumptions)
        met #(if % :met :failed)]
    (vec (for [{:keys [id kind of law blocking]} os]
           (cond-> {:id id
                    :status (cond
                              law (case (get by-law law)
                                    (:proved :tested :evaluated :witnessed) :met
                                    :unproved :unproved
                                    :failed)
                              (= :question kind) (if blocking :blocking :open)
                              (= :assumption kind) (met (get held of))
                              (= :signature kind) (met (:ok static))
                              (= :flow kind) (met (get flow-ok of))
                              (= :calls kind) (met (get call-ok of))
                              (= :machine kind) (met (get machine-ok of))
                              :else (met (get graph-ok of)))}
                   law (assoc :law law))))))

(defn- source-hash [ns-sym]
  (try (hash/sha256 (slurp (source-url ns-sym))) (catch Throwable _ nil)))

(defn- record-of
  "What a check found, as the record `attest` compares: the sources by
  their hashes, each law as written with the evidence it needs and got,
  each question and each obligation's status.  Nothing that varies from
  run to run with the same seed, such as the proof cache, is in it."
  [e spec-ns laws r level]
  (let [written (into {} (map (juxt :name :prop)) laws)]
    {:spec spec-ns
     :target (:target e)
     :ok (:ok r)
     :hashes (cond-> {:spec (source-hash spec-ns) :target (source-hash (:target e))}
               (:ns (::proof e)) (assoc :proof (source-hash (:ns (::proof e)))))
     :laws (vec (for [{:keys [law status evidence because] :as res} (:laws r)]
                  (cond-> {:law law :prop (get written law) :status status
                           :require (or (:require res) level)}
                    evidence (assoc :evidence evidence)
                    because (assoc :because because))))
     :questions (mapv #(select-keys % [:id :text :blocking]) (:questions r))
     ;; what the proofs rest on, as written
     :assumptions (let [props (into {} (map (juxt :name :prop)) (:assumptions e))]
                    (vec (for [a (:assumptions r)]
                           (if (:fn a)
                             {:fn (:fn a) :sig (:sig a)}
                             {:assumption (:assumption a) :prop (get props (:assumption a))}))))
     :obligations (:obligations r)
     ;; each signature and refinement as written, so one loosened shows
     :anns (into (sorted-map) (for [[f sig] (:anns e)]
                                [f (cond-> {:params (:params sig) :ret (:ret sig)}
                                     (get (:contracts e) f) (assoc :contract (get (:contracts e) f)))]))
     :refines (into (sorted-map) (for [{:keys [name base pred]} (:refines e)]
                                   [name {:base base :pred pred}]))}))

(declare check)

(defn- as-record
  "A record from what `attest` is given: a record, a path to one, or a
  spec namespace, checked afresh so its record says what is true now."
  [x]
  (cond
    (map? x) x
    (string? x) (edn/read-string (slurp x))
    ;; a check that stops at its static rules checks no law
    (symbol? x) (or (::record (check x {}))
                    {:spec x :ok false :laws [] :questions [] :obligations []})
    :else (fail! "`attest` compares records: a record, a path to one, or a spec namespace, had "
                 (pr-str x))))

(defn attest
  "Compare an earlier record of a spec with a later one: {:ok :weakened
  [...]}.  Each argument is a record, a path to one (as check :record
  writes it) or a spec namespace, checked afresh -- never a report taken
  on trust.  The later spec is weaker when a law is gone (:removed) or
  written differently (:restated), needs less evidence than it did
  (:require-lowered) or has less (:evidence-dropped), when another
  obligation is gone, when a blocking question stopped being one
  (:no-longer-blocking), when it assumes something it did not, or assumes
  it differently (an :assumption or :fn :added or :restated), or when
  what passed then fails now (:claimed-pass).  Changing the code is not weakening the spec; a
  restated law the spec's owner agreed to is accepted by taking a new
  record."
  [old new]
  (let [old (as-record old)
        new (as-record new)
        rank {:proved 2 :tested 1}
        ev-rank {:proof 2 :test 1}
        now (into {} (map (juxt :law identity)) (:laws new))
        law-ids (set (map #(str "law." (:law %)) (concat (:laws old) (:laws new))))
        weakened
        (vec (concat
               (when (and (:ok old) (not (:ok new)))
                 [{:what :claimed-pass
                   :why "the earlier record passed, but the check fails now"}])
               (for [{:keys [law prop require evidence]} (:laws old)
                     :let [n (get now law)
                           what (cond
                                  (nil? n) :removed
                                  (not= prop (:prop n)) :restated
                                  (< (rank (:require n) 0) (rank require 0)) :require-lowered
                                  (< (ev-rank (:evidence n) 0) (ev-rank evidence 0)) :evidence-dropped)]
                     :when what]
                 (cond-> {:law law :what what}
                   (= :restated what) (assoc :was prop :now (:prop n))))
               (let [ids (set (map :id (:obligations new)))]
                 (for [{:keys [id law]} (:obligations old)
                       :when (and (not (contains? ids id)) (not (contains? law-ids id))
                                  ;; a law's own obligation is reported as the law
                                  (not law)
                                  (not (str/starts-with? id "question."))
                                  ;; assuming less is no weakening
                                  (not (str/starts-with? id "assume.")))]
                   {:obligation id :what :removed}))
               ;; every proof rests on what the spec assumes: more of it, or
               ;; other of it, is a weaker spec
               (let [key-of #(or (:fn %) (:assumption %))
                     before (into {} (map (juxt key-of identity)) (:assumptions old))]
                 (for [a (:assumptions new)
                       :let [k (key-of a) o (get before k)]
                       :when (not= o a)]
                   (cond-> {:what (if o :restated :added)}
                     (:fn a) (assoc :fn k)
                     (:assumption a) (assoc :assumption k))))
               (let [now-blocking (into {} (map (juxt :id :blocking)) (:questions new))]
                 (for [{:keys [id blocking]} (:questions old)
                       :when (and blocking (false? (get now-blocking id)))]
                   {:question id :what :no-longer-blocking}))
               ;; a signature or a refinement gone, or written otherwise:
               ;; looser, as far as writ can tell, until its owner agrees
               (for [[f sig] (:anns old)
                     :let [n (get (:anns new) f)]
                     :when (not= sig n)]
                 (cond-> {:ann f :what (if n :changed :removed) :was sig}
                   n (assoc :now n)))
               (for [[nm r] (:refines old)
                     :let [n (get (:refines new) nm)]
                     :when (not= r n)]
                 (cond-> {:refinement nm :what (if n :changed :removed) :was r}
                   n (assoc :now n)))))]
    {:ok (empty? weakened) :weakened weakened}))

(defn- weakening-text
  "One line of what attest found weaker."
  [{:keys [law obligation question fn assumption ann refinement what was now]}]
  (str (cond law (str "law `" law "`")
             obligation (str "obligation " obligation)
             question (str "question `" question "`")
             ann (str "the ann of `" ann "`")
             refinement (str "refinement `" refinement "`")
             fn (str "the assumed signature of `" fn "`")
             assumption (str "assumption `" assumption "`")
             :else "the check")
       " is " (str/replace (name what) "-" " ")
       (when (and was now) (str ": was " (pr-str was) ", now " (pr-str now)))))

(declare reachable-from)

(defn- assumption-results
  "What each assumption came to, run while the assumed fns are wrapped:
  a signature needs its fn to resolve, outside the target; a law about
  them must not call the target, and is tested against the real fns.
  Each {:fn q :sig} or {:assumption name}, with :status :held or :failed
  and, when it failed, :why or a law's failure.  A law that held carries
  :prop, qualified, for the prover to cite."
  [e ctx publics interns target spec-ns {:keys [trials seed max-size]}]
  (let [forms-of #(book/read-forms (source-url %))
        graph (delay (try (wide-graph spec-ns (forms-of spec-ns) forms-of) (catch Throwable _ {})))]
  (vec (concat
         (for [[q sig] (sort-by (comp str key) (:assumes e))]
           (cond
             (= (namespace q) (str target))
             {:fn q :sig sig :status :failed
              :why (str "the spec assumes a signature for `" q "`, the target's own fn: give it one with"
                        " `ann`, and say what it does with laws, which are checked")}
             (nil? (assumed-var q))
             {:fn q :sig sig :status :failed
              :why (str "the spec assumes a signature for `" q "`, which does not resolve: require"
                        " its namespace in the spec, and name it through an alias")}
             :else {:fn q :sig sig :status :held}))
         (for [{:keys [name prop]} (:assumptions e)]
           (try
             (let [p (desugar prop)
                   _ (lw/check-prop-shape! p)
                   qp (qualify p #{} publics interns target spec-ns)
                   of-target? #(and (symbol? %) (= (namespace %) (str target)))
                   syms (filter symbol? (tree-seq coll? seq qp))
                   ;; directly, or through the spec's helpers and the
                   ;; project fns they call
                   path (or (some #(when (of-target? %) [%]) syms)
                            (some (fn [h] (when (contains? @graph h)
                                            (some #(reach-path @graph h %)
                                                  (filter of-target? (reachable-from @graph h)))))
                                  syms))]
               (if path
                 {:assumption name :status :failed
                  :why (str "assumption `" name "` calls `" (clojure.core/name (peek path)) "`, a fn of " target
                            (when (next path)
                              (str ", through " (str/join " -> " (cons (clojure.core/name (first path)) (rest path)))))
                            ": an assumption is about code writ does not check, and the target is"
                            " checked. Say what it does with a law")}
                 (let [r (test-law ctx {:name name :prop qp} {:trials trials :seed seed :max-size max-size})]
                   (if (= :failed (:status r))
                     (assoc r :assumption name)
                     {:assumption name :status :held :prop qp :evidence (:status r)}))))
             (catch Throwable ex
               {:assumption name :status :failed :why (str "assumption `" name "`: " (or (ex-message ex) (str ex)))})))))))

;; --- more trials for a law that is only tested --------------------------------------

(def ^:private more-trials-default
  "The trials a law the prover could not prove gets beyond its first
  run, and the most time they may take, per law."
  {:trials 900 :ms 20000})

(defn- more-trials
  "A law that is only tested runs again, a hundred trials at a time
  with the seeds after its own, until it has had :trials more or :ms
  have passed.  So does one whose hypothesis no trial met, where the
  solver found no input either: a rare hypothesis is met in more trials.
  A failure among them is the law's result, with the seed that replays
  it.  :held counts the trials whose hypothesis held."
  [ctx r opts]
  (let [{extra :trials ms :ms} (merge more-trials-default
                                     (when (map? (:more-trials opts)) (:more-trials opts)))
        starved? (and (= :failed (:status r)) (:no-hypothesis r))]
    (if (or (not (or (= :tested (:status r)) starved?)) (:lemma r) (not (:prop r))
            (false? (:more-trials opts)) (not (pos? extra)))
      r
      (let [t0 (System/currentTimeMillis)
            base (or (:seed r) 0)
            first-run (or (:trials r) (:trials opts) 100)
            [bs body] (leading-foralls (:prop r))
            atoms (law-atoms body (map first bs))
            ;; every clause seen both ways, often enough: more trials of the
            ;; same would say little more
            covered? (fn [cov ran held] (and (seq atoms) (>= ran 300) (>= held thin-tests)
                                        (every? #(and (<= 5 (get-in cov [% true] 0)) (<= 5 (get-in cov [% false] 0)))
                                                atoms)))]
        (loop [k 1, ran first-run, held (if starved? 0 (- first-run (or (:discarded r) 0))),
               cov (or (:coverage r) {})]
          (if (or (> (* 100 k) extra) (> (- (System/currentTimeMillis) t0) ms) (covered? cov ran held))
            (cond
              (not starved?) (assoc r :trials ran :discarded (- ran held) :held held :coverage cov
                                    :one-sided (vec (for [a atoms, side [false true]
                                                          :when (zero? (get-in cov [a side] 0))]
                                                      [a side])))
              (pos? held) (-> r (dissoc :counterexample :detail :no-hypothesis)
                              (assoc :status :tested :trials ran :discarded (- ran held) :held held
                                     :coverage cov))
              :else r)
            (let [t (try (test-law ctx {:name (:law r) :prop (:prop r)}
                                   {:trials 100 :seed (+ base k) :max-size (or (:max-size opts) 50)})
                         ;; as the first run: a law that cannot be run fails with the reason
                         (catch Throwable ex
                           {:status :failed :counterexample {} :detail [] :seed (+ base k)
                            :error (or (ex-message ex) (str ex))}))]
              (if (and (= :failed (:status t)) (not (:no-hypothesis t)))
                (merge (dissoc r :unproved :stuck :trials :discarded :no-hypothesis)
                       (select-keys t [:status :counterexample :original :trial :seed :detail :error])
                       {:after-trials ran})
                (recur (inc k) (+ ran 100)
                       (+ held (if (:no-hypothesis t) 0 (- (or (:trials t) 100) (or (:discarded t) 0))))
                       (merge-with (partial merge-with +) cov (:coverage t)))))))))))

(defn- reachable-from
  "Every fn of graph g that f reaches through calls."
  [g f]
  (loop [todo [f], seen #{}]
    (if-let [x (first todo)]
      (recur (into (vec (rest todo)) (remove seen (get g x))) (into seen (get g x)))
      seen)))

(declare check*)

(defn check
  "Check a spec namespace against its target (or opts :target).  Returns a
  report map; :ok says whether everything held and :message explains any
  failure.  opts: :target, :trials (test.check runs per law, default 100),
  :seed (default random; each law's report carries the one it used) and
  :max-size (the largest generated size, default 50), :adequacy (false
  skips the gap check; :mutants adds mutants of each fn's source to its
  stand-ins), :prove (false skips the prover), :fuel (the
  rewrites the prover may make on one attempt, default 20000) and :require
  (:proved or :tested, in place of the spec's own), :prover (knobs of
  the prover over writ.prove/default-config, for a bench to try) and
  :explain (true
  gives each law the prover tried its :attempts, and the report the
  goals a tested law's proof got stuck on) and :parallel (false runs the
  laws one at a time, on the calling thread)."
  ([spec-ns] (check spec-ns {}))
  ([spec-ns opts]
   (binding [*parallel* (and *parallel* (not (false? (:parallel opts))))]
     (check* spec-ns opts))))

(defn- check*
  [spec-ns opts]
   (when (and (contains? opts :record) (not (string? (:record opts))))
     (fail! "`check` :record is a path to write the report to, had: " (pr-str (:record opts))))
   (let [{:keys [trials seed max-size] :or {trials 100 max-size 50}} opts
         t0 (System/nanoTime)
         clock (atom (zipmap [:static :tests :prover :more-trials :adequacy :graphs] (repeat 0)))
         ;; each phase's time, in ms, for the report's :timings
         timed (fn [k f] (let [t (System/nanoTime)]
                           (try (f) (finally (swap! clock update k + (quot (- (System/nanoTime) t) 1000000))))))
         timings #(assoc @clock :total (quot (- (System/nanoTime) t0) 1000000))
         e (entry spec-ns (:target opts) (:proof opts))
         {:keys [target anns data laws]} e
         proof-e (::proof e)
         lemma-names (set (map :name (:lemmas proof-e)))
         ;; lemmas first, so a law proved after them may cite them
         laws (into (mapv #(assoc % :lemma true) (:lemmas proof-e)) laws)
         static (timed :static #(static-check e))
         ambiguous (when (:ok static) (ambiguous-names e spec-ns))
         base (cond-> {:spec spec-ns :target target
                       :static (if (:ok static) {:ok true} static)
                       :unspecified (vec (sort (for [[nm private?] (:defns static)
                                                      :when (and (not private?) (not (contains? anns nm)))]
                                                  nm)))}
                (seq ambiguous) (assoc :ambiguous (mapv :name ambiguous) ::ambiguous ambiguous))]
     (if (or (not (:ok static)) (seq ambiguous))
       (let [r (assoc base :ok false :laws [] :gaps [] :calls [] :flows [] :machines [] :graphs [])]
         (assoc r :message (format-report r) :timings (timings)))
       (let [refs (refines-of e)
             tenv (type-env-of e spec-ns)
             data-tenv (tenv-of data)
             laws (-> (vec laws)
                      (into (ensures-laws e))
                      (into (mapcat #(graph-obligations % refs (:invariants e)) (:graphs e))))
             publics (set (keys (ns-publics (the-ns target))))
             interns (set (keys (ns-interns (the-ns spec-ns))))
             proof-own* (proof-own (:ns proof-e))
             opaque (into (set publics) interns)
             numeric-fns (into #{} (keep (fn [[k s]] (when (contains? '#{Nat Int Float Double}
                                                                      (plain (:ret s)))
                                                       k)))
                               anns)
             ctx {:ev (evaluator spec-ns) :tenv (assoc tenv ::seeds (code-seeds target))
                  ;; the values drawn with a fixed seed, made once a check
                  :draws (atom {})}
             ;; the spec's own one-expression fns, which an exists over
             ;; an integer's bounds is read through
             helpers (into {} (for [f (book/read-forms (source-url spec-ns))
                                    :when (and (seq? f) (contains? '#{defn defn-} (first f)))
                                    :let [{:keys [name params body]} (defn-parts f)]
                                    :when (and (vector? params) (not-any? #{'&} params)
                                               (every? symbol? params) (= 1 (count body))
                                               (not (contains? publics name)))]
                                [name [params (first body)]]))
             ;; only what this check wrapped is unwrapped after it, so a
             ;; caller's own instrument stays in place
             wrapped (wrap! e)
             assumed (timed :tests
                            #(try (assumption-results e ctx publics interns target spec-ns
                                                      {:trials trials :seed seed :max-size max-size})
                                  (catch Throwable ex (unwrap! wrapped) (throw ex))))
             results (timed :tests #(try
                       (par-map
                         (fn [{:keys [name prop explain graph total lemma step-of witness guard-law example]}]
                            (let [p (eliminate-exists (desugar prop) helpers)]
                              (try
                                (lw/check-prop-shape! p)
                                (let [qp (qualify p #{} publics interns target spec-ns
                                                  (if lemma proof-own* {}))]
                                  ;; a lemma is proof, not contract: one about
                                  ;; clojure.core alone is a fact the proof uses
                                  (cond
                                    ;; a guard's own laws are about the spec's
                                    ;; test, not the code: that some value passes it
                                    (and (not lemma) (not guard-law) (not (calls-target? qp target)))
                                    {:law name :status :vacuous
                                     :why (str "it calls no fn of " target)}

                                    (and (not lemma) (not guard-law) (try-prove p data-tenv opaque numeric-fns))
                                    {:law name :status :vacuous
                                     :why (str "writ.norm proves it without looking at the "
                                               "implementation, so any code satisfies it")}

                                    :else
                                    (cond-> (let [t (System/nanoTime)
                                                  r (test-law ctx {:name name :prop qp :witness witness}
                                                              {:trials trials :seed seed :max-size max-size})]
                                              (assoc r :prop qp :test-ms (quot (- (System/nanoTime) t) 1000000)))
                                      explain (assoc :explain explain)
                                      graph (assoc :graph graph)
                                      step-of (assoc :step-of step-of)
                                      guard-law (assoc :guard-law true)
                                      example (assoc :example example)
                                      total (assoc :total true)
                                      lemma (assoc :lemma true))))
                                ;; a law that cannot be run (a malformed
                                ;; proposition, a type with no generator)
                                ;; fails with the reason, not the whole check
                                (catch Throwable ex
                                  {:law name :status :failed :counterexample {} :detail []
                                   :error (or (ex-message ex) (str ex))}))))
                         laws)
                       (finally (unwrap! wrapped))))
             level (or (:require opts) (:require e) :tested)
             _ (check-level! "`check`" level)
             results (mapv #(cond-> % (contains? lemma-names (:law %)) (assoc :lemma true)) results)
             imports (imports-of spec-ns e opts)
             results (-> (timed :prover #(prove-laws results (assoc opts ::hints (:hints proof-e) ::proof-ns (:ns proof-e)
                                                   ::imports (:lemmas imports)
                                                   ;; what held is given to the prover
                                                   ::assumed {:sigs (into {} (for [{f :fn sig :sig st :status} assumed
                                                                                   :when (and f (= :held st))]
                                                                               [f sig]))
                                                              :lemmas (vec (for [{a :assumption p :prop st :status} assumed
                                                                                 :when (and a (= :held st))]
                                                                             {:name a :prop p}))})
                                     target spec-ns (merge (:tenv imports) data-tenv) anns refs ctx))
                         ;; a law the prover could not prove rests on its
                         ;; tests alone, so it gets more of them
                         ((fn [rs] (timed :more-trials
                                          #(let [wrapped (wrap! e)]
                                             (try (par-map (fn [r] (more-trials ctx r opts)) rs)
                                                  (finally (unwrap! wrapped)))))))
                         (require-evidence
                           ;; a lemma is there to be cited, so it must be proved
                           (mapv #(if (:lemma %) (assoc-in % [:opts :require] :proved) %) laws)
                           level))
             unq (fn unq [f]
                   (cond (and (symbol? f) (contains? #{(name target) (name spec-ns)} (namespace f)))
                         (symbol (name f))
                         (seq? f) (apply list (map unq f))
                         (vector? f) (mapv unq f)
                         :else f))
             results (mapv (fn [r] (if (:detail r)
                                     (update r :detail (fn [d] (mapv (fn [[t v]] [(unq t) v]) d)))
                                     r))
                           results)
             sound? (not-any? #(contains? #{:failed :vacuous} (:status %)) results)
             per-fn (if (and sound? (not= false (:adequacy opts)))
                      (timed :adequacy #(adequacy ctx target
                                (sort (filter #(contains? publics %) (keys anns)))
                                ;; a step's witness is found by search, so a stand-in
                                ;; that misses it may only be unlucky: it pins nothing
                                anns (concat (keep #(when-let [p (:prop %)]
                                                      (cond-> (vary-meta p assoc ::law
                                                                         ;; an exists never rejects a stand-in
                                                                         (when-not (or (:graph %) (:guard-law %)
                                                                                       (quant? (second (leading-foralls p)))
                                                                                       (head? p "exists"))
                                                                           (:law %))
                                                                         ::example (:example %))
                                                        (:hypothesis-witness %)
                                                        (vary-meta assoc ::witness (:hypothesis-witness %))))
                                                   (remove #(or (:lemma %) (:step-of %)) results))
                                             (for [m (:machines e)]
                                               (qualify (machine-prop m e) #{} publics interns
                                                        target spec-ns)))
                                trials (or seed 42)
                                ;; mutants of the fn's source, on request: they cost
                                ;; a static check each
                                (when (= :mutants (:adequacy opts))
                                  (fn [nm sig] (mutants e target nm sig ctx (or seed 42) 12)))))
                      [])
             gaps (vec (for [{f :fn s :survivors} per-fn :when (seq s)]
                         {:fn f :survivors s}))
             lemma-results (mapv #(-> % (dissoc :prop :lemma) (set/rename-keys {:law :lemma}))
                                 (filter :lemma results))
             proved-props (vec (for [r results
                                     :when (and (:prop r) (= :proved (:status r)) (not (:lemma r)))]
                                 {:name (symbol (str spec-ns) (str (:law r)))
                                  :prop (erase-law (:prop r) refs spec-ns)}))
             contras (when (some #(= :failed (:status %)) results)
                       (let [signed (set (map #(symbol (name target) (name %)) (keys anns)))]
                         (contradictions
                           (for [r results :when (and (:prop r) (not (:lemma r)))]
                             {:name (:law r) :prop (:prop r)})
                           results signed
                           #(binding [*ns* (the-ns spec-ns)] (eval %))
                           #(type->gen % (:tenv ctx))
                           (into {} (for [[f sig] anns]
                                      [(symbol (name target) (name f)) (plain (:ret sig))]))
                           (or seed 0))))
             ;; whether each law is about every input, read before :prop goes
             results (mapv #(cond-> (dissoc % :prop) (head? (:prop %) "forall") (assoc ::general true))
                           (remove :lemma results))
             target-forms (book/read-forms (source-url target))
             forms-of (memoize #(book/read-forms (source-url %)))
             call-results (check-calls e target-forms forms-of)
             flow-results (check-flows e target-forms forms-of)
             machine-results (mapv #(check-machine % e target) (:machines e))
             graph-results (timed :graphs #(mapv (fn [g]
                                   (let [q #(qualify % #{} publics interns target spec-ns)
                                         errs (vec (concat (graph-flow-errors g anns refs)
                                                           (graph-start-errors g spec-ns tenv q (:invariants e))
                                                           (invariant-errors g (:invariants e))
                                                           (vacuous-invariants g (:invariants e) refs data-tenv)))
                                         rules (graph-rule-errors g)
                                         run-seed (or seed (rand-int 1000000))
                                         walked (graph-runs g spec-ns tenv (:invariants e) q run-seed)
                                         reached (let [[_ gm] g
                                                       st (:start gm)
                                                       start (if (vector? st) (first st) st)
                                                       es (for [{:keys [from key tos]} (graph-edges g), t tos]
                                                            [from key t])]
                                                   (when start (reachable es start)))
                                         run-errs (vec (concat
                                                         (map #(assoc % :seed run-seed) (:failures walked))
                                                         (when (and walked (empty? (:failures walked))
                                                                    (seq (:visited walked)))
                                                           (for [f (:final (second g))
                                                                 :when (and (contains? reached f)
                                                                            (not (contains? (:visited walked) f)))]
                                                             {:seed run-seed
                                                              :reason (let [shut (sort (for [[[st fe] {:keys [refused passed]}] (:refusals walked)
                                                                                             :when (and (pos? refused) (zero? passed))]
                                                                                         (str "the guard of " fe " from " (pr-str st)
                                                                                              " refused all " refused " of its steps, half of them"
                                                                                              " searching " (* 3 guard-draws) " draws for arguments it takes")))]
                                                                        (str "no run of " (:runs (second g)) " reached "
                                                                             (pr-str f) " in " (or (:depth (second g)) default-depth)
                                                                             " steps; a run from the start should reach every final state"
                                                                             (if (seq shut)
                                                                               (str ": " (str/join "; " shut)
                                                                                    ". Check that the guard can hold from the states a run reaches")
                                                                               ", so walk more runs, or longer ones (:depth)")))}))))
                                         obls (filter #(= (first g) (:graph %)) results)]
                                     (let [ok? (and (empty? errs) (empty? rules) (empty? run-errs))]
                                       (cond-> {:graph (first g) :states (count (:states (second g)))
                                                :edges (count (graph-edges g))
                                                :status (if ok? :ok :failed)
                                              ::obligations (count obls)
                                              ::steps (count (filter #(and (= (first g) (:step-of %)) (not (:guard-law %))
                                                                           (= :witnessed (:status %)))
                                                                     results))
                                              ::unproved (count (remove #(= :proof (:evidence %)) obls))}
                                                (and ok? (:runs (second g))) (assoc :runs (:runs (second g)))
                                                (and ok? (some #(= (first g) (first %)) (:invariants e)))
                                                (assoc ::held (vec (distinct (for [[g' st] (:invariants e)
                                                                                   :when (= g' (first g))] st))))
                                                (seq errs) (assoc :errors errs)
                                                (seq rules) (assoc :rules rules)
                                                (seq run-errs) (assoc :runs-failed run-errs)))))
                                 (:graphs e)))
             graphless (and (empty? (:graphs e)) (empty? (:machines e)))
             problems (vec (for [[g st] (:invariants e)
                                 :when (not-any? #(= g (first %)) (:graphs e))]
                             (str "invariant `" g " " st "` names a graph the spec does not have")))
             r (assoc base :laws results :gaps gaps :calls call-results :flows flow-results
                           :uses (:report imports)
                           ;; the proved laws, erased and qualified, for a spec that uses this one
                           ::proved-props proved-props
                           :lemmas lemma-results
                           :graph-missing graphless
                           :problems problems
                           :contradictions (mapv #(dissoc % :call) contras)
                           ::contradictions contras
                           :questions (vec (:questions e))
                           :assumptions (mapv #(dissoc % :prop :counterexample :detail :original :trial :law) assumed)
                           ::assumed assumed
                           :graphs (mapv #(dissoc % ::unproved ::obligations ::steps ::held :runs-failed) graph-results)
                           :proof (proof-coverage results level)
                           :machines (mapv #(dissoc % :shown :step) machine-results)
                           :rejected (mapv #(select-keys % [:fn :laws :rejected]) per-fn)
                           ;; a law of the spec's own that, on its own, tells no
                           ;; stand-in of any fn it calls from the real one
                           :silent (let [with (filter #(pos? (or (:impostors %) 0)) per-fn)
                                         credited (set (mapcat :credited with))]
                                     (vec (for [l (sort-by str (distinct (mapcat :about with)))
                                                :when (not (contains? credited l))]
                                            {:law l :fns (vec (sort-by str (keep #(when (contains? (:about %) l) (:fn %))
                                                                                 with)))})))
                           :off-graph (vec (sort-by str (remove (step-fns e)
                                                                (filter #(contains? publics %) (keys anns)))))
                           :ok (and sound? (empty? gaps) (empty? (:unspecified base))
                                    (not-any? #(= :unproved (:status %)) results)
                                    (every? #(= :proved (:status %)) lemma-results)
                                    (every? #(= :ok (:status %)) call-results)
                                    (every? #(= :ok (:status %)) flow-results)
                                    (every? #(= :ok (:status %)) machine-results)
                                    (every? #(= :ok (:status %)) graph-results)
                                    (empty? problems)
                                    (not-any? :blocking (:questions e))
                                    (every? #(= :held (:status %)) assumed)
                                    (not graphless)))
                 r (assoc r :obligations (obligation-status (obligations* e) r))
                 r (assoc r ::record (record-of e spec-ns laws r level))
                 ;; a spec held to a baseline fails when it is weaker than it
                 baseline (:baseline e)
                 r (if (and baseline (not= baseline (:record opts)))
                     (let [f (io/file baseline)]
                       (if-not (.exists f)
                         (assoc r :ok false
                                :baseline-problems [(str "the spec is held to the baseline " baseline
                                                         ", which does not exist; write it from a check its owner"
                                                         " agrees with: (writ.spec/check '" spec-ns " {:record \""
                                                         baseline "\"})")])
                         (let [weak (remove #(= :claimed-pass (:what %))
                                            (:weakened (attest (edn/read-string (slurp f)) (::record r))))]
                           (if (seq weak)
                             (assoc r :ok false
                                    :baseline-problems (into [(str "the spec is weaker than its baseline " baseline
                                                                   "; its owner takes a new record to accept a change:")]
                                                             (map #(str "  " (weakening-text %)) weak)))
                             r))))
                     r)]
         (do (when-let [path (:record opts)]
               (spit path (pr-str (::record r))))
             (assoc r :message (format-report (assoc r :machines machine-results
                                                     :graphs graph-results
                                                     ::explain (:explain opts)))
                    :timings (timings)))))))
(defn check!
  "`check`, throwing with the report's message when anything fails."
  ([spec-ns] (check! spec-ns {}))
  ([spec-ns opts]
   (let [r (check spec-ns opts)]
     (if (:ok r)
       r
       (throw (ex-info (:message r) {:writ/error true :report r}))))))
