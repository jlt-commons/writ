(ns writ.rng
  "test.check's splittable random numbers, the same numbers, made without
  bignums.

  test.check draws every value from JavaUtilSplittableRandom: SplitMix64,
  a 64-bit state and gamma mixed by 64-bit multiplies and shifts.  Chez's
  fixnums are 61 bits wide, so on jolt every one of those steps made a
  bignum, and generating a law's inputs spent most of its time there.
  Here a 64-bit word is two 32-bit halves, each a fixnum, a product is put
  together from 16-bit pieces, and the mixing runs as Scheme on fixnums
  alone; nothing leaves fixnum range until a caller asks for a long.  The
  algorithm is test.check's, step for step, and its draws are the same
  draw for draw: a seed replays the same inputs, here and anywhere else
  test.check runs.

  `install!` makes clojure.test.check.random/make-random, given a seed,
  return one of these."
  (:require [clojure.test.check.random :as random]
            [jolt.scheme :as scheme]))

(def ^:private mixer
  "Scheme procedures over a generator's four halves, gamma hi and lo and
  state hi and lo, picked by number: 0 split, which writes six halves
  into a jolt array -- the first generator's state, the second's gamma
  and state -- 1 rand-long and 2 rand-double."
  (scheme/eval-string "
(let ()
  (define m32 #xFFFFFFFF)
  (define m16 #xFFFF)
  ;; x * y mod 2^32, and the high 32 bits of x * y, for x, y below 2^32
  (define (mul32 x y)
    (let ([x0 (fxlogand x m16)] [x1 (fxsrl x 16)] [y0 (fxlogand y m16)] [y1 (fxsrl y 16)])
      (fxlogand (fx+ (fx* x0 y0) (fxsll (fxlogand (fx+ (fx* x1 y0) (fx* x0 y1)) m16) 16)) m32)))
  (define (mulhi32 x y)
    (let* ([x0 (fxlogand x m16)] [x1 (fxsrl x 16)] [y0 (fxlogand y m16)] [y1 (fxsrl y 16)]
           [mid (fx+ (fx* x1 y0) (fx* x0 y1))]
           [t (fx+ (fx* x0 y0) (fxsll (fxlogand mid m16) 16))])
      (fx+ (fx* x1 y1) (fxsrl mid 16) (fxsrl t 32))))
  ;; a 64-bit word is (values hi lo)
  (define (add64 ah al bh bl)
    (let ([l (fx+ al bl)])
      (values (fxlogand (fx+ ah bh (fxsrl l 32)) m32) (fxlogand l m32))))
  (define (mul64 ah al bh bl)
    (values (fxlogand (fx+ (mulhi32 al bl) (mul32 ah bl) (mul32 al bh)) m32) (mul32 al bl)))
  ;; x xor (x >>> n)
  (define (xorshift h l n)
    (if (fx< n 32)
        (values (fxlogxor h (fxsrl h n))
                ;; h's low n bits, moved to the top of lo
                (fxlogxor l (fxlogor (fxsrl l n) (fxsll (fxlogand h (fx- (fxsll 1 n) 1)) (fx- 32 n)))))
        (values h (fxlogxor l (fxsrl h (fx- n 32))))))
  (define (mix-64 h l)
    (let*-values ([(h l) (xorshift h l 30)]
                  [(h l) (mul64 h l #xbf58476d #x1ce4e5b9)]
                  [(h l) (xorshift h l 27)]
                  [(h l) (mul64 h l #x94d049bb #x133111eb)])
      (xorshift h l 31)))
  (define (bit-count x) (let loop ([x x] [n 0]) (if (fx= x 0) n (loop (fxlogand x (fx- x 1)) (fx+ n 1)))))
  (define (mix-gamma h l)
    (let*-values ([(h l) (xorshift h l 33)]
                  [(h l) (mul64 h l #xff51afd7 #xed558ccd)]
                  [(h l) (xorshift h l 33)]
                  [(h l) (mul64 h l #xc4ceb9fe #x1a85ec53)]
                  [(h l) (xorshift h l 33)])
      (let ([l (fxlogor l 1)])
        (let-values ([(ch cl) (xorshift h l 1)])
          (if (fx> 24 (fx+ (bit-count ch) (bit-count cl)))
              (values (fxlogxor h #xaaaaaaaa) (fxlogxor l #xaaaaaaaa))
              (values h l))))))
  (define (split out gh gl sh sl)
    (let*-values ([(h1 l1) (add64 sh sl gh gl)]
                  [(h2 l2) (add64 h1 l1 gh gl)]
                  [(gh2 gl2) (mix-gamma h2 l2)]
                  [(mh ml) (mix-64 h1 l1)])
      (let ([v (jolt-array-vec out)])
        (vector-set! v 0 h2) (vector-set! v 1 l2) (vector-set! v 2 gh2)
        (vector-set! v 3 gl2) (vector-set! v 4 mh) (vector-set! v 5 ml))
      out))
  (define (rand-long gh gl sh sl)
    (let*-values ([(h l) (add64 sh sl gh gl)] [(h l) (mix-64 h l)])
      (+ (* (if (>= h #x80000000) (- h #x100000000) h) #x100000000) l)))
  ;; the top 53 bits, x >>> 11, times 2^-53
  (define (rand-double gh gl sh sl)
    (let*-values ([(h l) (add64 sh sl gh gl)] [(h l) (mix-64 h l)])
      (fl* (fixnum->flonum (fx+ (fx* h #x200000) (fxsrl l 11))) (expt 2.0 -53))))
  (lambda (k) (case k [(0) split] [(1) rand-long] [(2) rand-double])))"))

(def ^:private sr-split (mixer 0))
(def ^:private sr-long (mixer 1))
(def ^:private sr-double (mixer 2))

(deftype SplittableRandom [gh gl sh sl]
  random/IRandom
  (rand-long [_] (sr-long gh gl sh sl))
  (rand-double [_] (sr-double gh gl sh sl))
  (split [_]
    (let [v (sr-split (object-array 6) gh gl sh sl)]
      [(SplittableRandom. gh gl (aget v 0) (aget v 1))
       (SplittableRandom. (aget v 2) (aget v 3) (aget v 4) (aget v 5))]))
  (split-n [this n]
    ;; a series of two-way splits, the second of each kept, as test.check's
    (case (long n)
      0 []
      1 [this]
      (let [n-dec (dec n)]
        (loop [sh sh sl sl ret (transient [])]
          (if (= n-dec (count ret))
            (persistent! (conj! ret (SplittableRandom. gh gl sh sl)))
            (let [v (sr-split (object-array 6) gh gl sh sl)]
              (recur (aget v 0) (aget v 1)
                     (conj! ret (SplittableRandom. (aget v 2) (aget v 3) (aget v 4) (aget v 5)))))))))))

(defn make-random
  "The generator test.check makes from seed, the golden gamma its own."
  [seed]
  (let [u (if (neg? seed) (+ seed 18446744073709551616) seed)]
    (SplittableRandom. 0x9e3779b9 0x7f4a7c15 (quot u 0x100000000) (mod u 0x100000000))))

(defonce ^:private original (atom nil))

(defn install!
  "Make test.check's make-random, given a seed, return these; without one
  it is as it was."
  []
  (when-not @original
    (reset! original @#'random/make-random)
    (let [f @original]
      (alter-var-root #'random/make-random
                      (constantly (fn ([] (f)) ([seed] (make-random seed))))))))
