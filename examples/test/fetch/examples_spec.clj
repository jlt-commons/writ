(ns fetch.examples-spec
  "A spec for fetch.core written as examples: a few statuses and what each
  should give. Every law holds, and a test suite like this would pass. But
  every law fixes the status to a literal, so the spec says nothing about
  any other status, and writ reports that: a `classify` that agrees on
  these statuses and answers anything at all elsewhere satisfies it.
  core_spec.clj states the bands instead."
  (:require [writ.spec :refer [spec data ann graph law]]))

(spec fetch.core)

(data Class Done Redirect Transient Failed)

(ann classify [Nat -> Class])

(graph statuses
  {:states {:status Nat, :class Class}
   :edges  {:status {[classify] #{:class}}}})

(law ok-is-done (= [:Done] (classify 200)))
(law moved-is-a-redirect (= [:Redirect] (classify 301)))
(law throttled-is-transient (= [:Transient] (classify 429)))
(law unavailable-is-transient (= [:Transient] (classify 503)))
(law not-found-has-failed (= [:Failed] (classify 404)))
