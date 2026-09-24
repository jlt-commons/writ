(ns writ.spec-demo.classify-spec
  "The contract for writ.spec-demo.classify. The sentinels are pinned by
  closed laws because a generated Int never reaches -127, and one
  quantified law says what every other count means."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.classify)

(ann classify-read [Int Bool -> Keyword])

(graph reading
  {:states {:count Int, :status Keyword}
   :edges  {:count {[classify-read Bool] #{:status}}}})

(law zero-is-decided-by-the-eof-flag
  (forall [e Bool] (= (classify-read 0 e) (if e :eof :idle))))

(law data-exactly-when-positive
  (forall [n Int, e Bool] (= (= :data (classify-read n e)) (pos? n))))

(law error-sentinel (forall [e Bool] (= :error (classify-read -1 e))))
(law again-sentinel (forall [e Bool] (= :again (classify-read -2 e))))
(law eof-sentinel (forall [e Bool] (= :eof (classify-read -127 e))))
