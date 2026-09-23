(ns writ.spec-demo.classify-weak-spec
  "classify-spec without its one quantified law over n. Every law still
  holds, but they only ever call classify-read with n = 0, -1, -2 or -127,
  so nothing says what 5 or -50 means."
  (:require [writ.spec :refer [spec ann law]]))

(spec writ.spec-demo.classify)

(ann classify-read [Int Bool -> Keyword])

(law zero-is-decided-by-the-eof-flag
  (forall [e Bool] (= (classify-read 0 e) (if e :eof :idle))))

(law error-sentinel (forall [e Bool] (= :error (classify-read -1 e))))
(law again-sentinel (forall [e Bool] (= :again (classify-read -2 e))))
(law eof-sentinel (forall [e Bool] (= :eof (classify-read -127 e))))
