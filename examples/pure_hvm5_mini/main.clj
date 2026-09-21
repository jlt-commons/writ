(ns pure-hvm5-mini.main
  "pure_hvm5_mini: the interaction-net machinery bend's HVM5 evaluator is
  proved over -- the source cursor and the packed run words.

  Ported from bend's demos/pure_hvm5_mini.  bend's file is the whole HVM5
  interpreter (1916 lines: IO, arrays, a parser, a reducer); writ has no
  mutable arrays and no IO monad, so what is ported here is the pure part its
  LAWS.bend actually quantifies over: the string cursor (str_at/str_drop), the
  word printer's brace count (opens), the packed run words (run_len/run_push/
  run_pop), the name code, and the book's depth.  LAWS.clj holds the
  obligations, PROOF.clj the proofs.

  A bend String is a linked list of SCon/SNil cells; here it is an ordinary
  Clojure String, whose first/rest give the same head-and-tail recursion."
  (:require [writ.defn :as w]))

;; the display-name alphabet (hvm5.c's): a name code is base 64 over it.
(def alphabet
  "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$")

;; the code at position n, 0 past the end.
(w/defn str-at [s :- String n :- Nat] :- Nat
  (int (nth s n 0)))

;; the string past n characters.
(w/defn str-drop [s :- String n :- Nat] :- String
  (apply str (drop n s)))

;; the word and the rest re-joined.  bend takes the pair (word, rest); here
;; they are the two arguments.
(w/defn word-cat [w :- String u :- String] :- String
  (apply str (concat w u)))

;; how many "{" a string holds.
(w/defn ^{:writ/descend true} opens [^:many s :- String] :- Nat
  (if (empty? s)
    0
    (+ (if (= (first s) \{) 1 0)
       (opens (rest s)))))

;; the index of c in s, or the length of s when c is absent.
(w/defn ^{:writ/descend true} alpha [^:many s :- String ^:many c :- Char ^:many i :- Nat] :- Nat
  (if (empty? s)
    i
    (if (= (first s) c)
      i
      (alpha (rest s) c (inc i)))))

;; a name's code: six bits per character, first character highest.
(w/defn ^{:writ/descend true} name-code [^:many s :- String ^:many acc :- Nat] :- Nat
  (if (empty? s)
    acc
    (name-code (rest s)
               (+ (bit-shift-left acc 6) (alpha alphabet (first s) 0)))))

;; a run word: the top byte counts the bits, the low 24 hold them.
(w/defn run-word [n :- Nat bits :- Nat] :- Nat
  (bit-or (bit-shift-left n 24) (bit-and bits 16777215)))

;; the number of bits a run word holds.
(w/defn run-len [p :- Nat] :- Nat
  (bit-shift-right p 24))

;; bit b pushed outermost onto the run word p.
(w/defn run-push [^:many p :- Nat b :- Nat] :- Nat
  (run-word (inc (bit-shift-right p 24))
            (bit-or (bit-shift-left (bit-and p 16777215) 1) b)))

;; the run word without its outermost bit.
(w/defn run-pop [^:many p :- Nat] :- Nat
  (bit-or (bit-shift-left (dec (bit-shift-right p 24)) 24)
          (bit-shift-right (bit-and p 16777215) 1)))

;; the depth of an array with room for n entries; f is the bits left to try.
(w/defn ^{:writ/descend true} book-depth [^:many f :- Nat ^:many n :- Nat ^:many d :- Nat] :- Nat
  (if (zero? f)
    d
    (if (<= n (bit-shift-left 1 d))
      d
      (book-depth (dec f) n (inc d)))))
