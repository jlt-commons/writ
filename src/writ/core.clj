(ns writ.core
  "Public entry points.

  The macros `defn`, `data`, `match`, `law` and `proof` are re-exported from
  writ.defn.  `check-book` runs every rule over a quoted vector of forms; use it
  in a test or a build step to gate a namespace."
  (:refer-clojure :exclude [defn])
  (:require [writ.check :as ck]
            [writ.book :as book]
            [writ.defn :as d]))

(clojure.core/defn check-defn
  "Check one `defn` form.  An annotated `w/defn` form runs the full w/defn
  pipeline (kinds, match, types) against the declared datatypes;
  a plain defn runs the checker without the book's ordering rule.
  Returns {:ok true} or throws."
  [form]
  (book/check-standalone form))

(clojure.core/defn check-all
  "Check a seq of `defn` forms.  Returns {:ok true} or throws on the first bad one."
  [forms]
  (doseq [f forms] (book/check-standalone f))
  {:ok true})

(clojure.core/defn check-book
  "Run every rule over a quoted vector of forms.  Returns {:ok true} or throws."
  [forms]
  (book/check-book forms))

(clojure.core/defn check-files
  "Read the given source files and check them as one book.  Returns {:ok true}
  or throws."
  [& paths]
  (apply book/check-files paths))

(clojure.core/defmacro defn [& args] (list* 'writ.defn/defn args))
(clojure.core/defmacro data [& args] (list* 'writ.defn/data args))
(clojure.core/defmacro match [& args] (list* 'writ.defn/match args))
(clojure.core/defmacro law [& args] (list* 'writ.defn/law args))
(clojure.core/defmacro proof [& args] (list* 'writ.defn/proof args))
