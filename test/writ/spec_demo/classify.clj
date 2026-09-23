(ns writ.spec-demo.classify
  "What the return value of a non-blocking read means. A positive count is
  data and three negative sentinels are decided by the code, but a 0 is
  ambiguous: only the EOF flag tells a finished stream from an idle one.
  Plain Clojure: the contract lives in writ.spec-demo.classify-spec.")

(defn classify-read [n eof?]
  (cond
    (pos? n) :data
    (= n -1) :error
    (= n -2) :again
    (= n -127) :eof
    eof? :eof
    :else :idle))
