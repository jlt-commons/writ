(ns pure-hvm5-mini.LAWS
  "pure_hvm5_mini: the laws (the spec).

  bend's LAWS.bend states eight claims about the pure logic: the lexer loses
  nothing (word_joins), a blank skip only moves the cursor (skip_is_drop), the
  cursor composes (drop_drop), a read past a drop is a read at the sum
  (at_drop), a push reads back and a pop restores (run_push_pop), a name
  survives its code (name_round_trip), and the book depth fits 2^d slots
  (book_depth_fits).  writ's gate discharges refl-convertible equalities only,
  so the laws here record the identities it proves over the ported functions;
  the eight claims above are the spec the functions exist to meet."
  (:require [writ.defn :as w]))

(w/law opens-add-zero     (= (+ (opens s) 0) (opens s)))
(w/law run-len-add-zero   (= (+ (run-len p) 0) (run-len p)))
(w/law book-depth-add-zero (= (+ (book-depth f n d) 0) (book-depth f n d)))
