(ns writ.spec-demo.tagged
  "A message answers a request only when it carries the request's tag, a
  string no two values generated apart share.")

(defn answer
  "[:Hit v] when msg is [tag v] for a tag of three characters or more,
  else [:Miss]."
  [msg tag]
  (if (and (string? tag) (<= 3 (count tag)) (vector? msg) (= 2 (count msg)) (= tag (first msg)))
    [:Hit (second msg)]
    [:Miss]))
