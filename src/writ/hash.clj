(ns writ.hash
  "SHA-256 of a string's UTF-8 bytes, as 64 hex digits, in plain Clojure:
  a check's record names the sources it checked by their hashes, and
  jolt provides no digest of its own.")

(def ^:private k
  [0x428a2f98 0x71374491 0xb5c0fbcf 0xe9b5dba5 0x3956c25b 0x59f111f1 0x923f82a4 0xab1c5ed5
   0xd807aa98 0x12835b01 0x243185be 0x550c7dc3 0x72be5d74 0x80deb1fe 0x9bdc06a7 0xc19bf174
   0xe49b69c1 0xefbe4786 0x0fc19dc6 0x240ca1cc 0x2de92c6f 0x4a7484aa 0x5cb0a9dc 0x76f988da
   0x983e5152 0xa831c66d 0xb00327c8 0xbf597fc7 0xc6e00bf3 0xd5a79147 0x06ca6351 0x14292967
   0x27b70a85 0x2e1b2138 0x4d2c6dfc 0x53380d13 0x650a7354 0x766a0abb 0x81c2c92e 0x92722c85
   0xa2bfe8a1 0xa81a664b 0xc24b8b70 0xc76c51a3 0xd192e819 0xd6990624 0xf40e3585 0x106aa070
   0x19a4c116 0x1e376c08 0x2748774c 0x34b0bcb5 0x391c0cb3 0x4ed8aa4a 0x5b9cca4f 0x682e6ff3
   0x748f82ee 0x78a5636f 0x84c87814 0x8cc70208 0x90befffa 0xa4506ceb 0xbef9a3f7 0xc67178f2])

(def ^:private h0
  [0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a 0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19])

(defn- u32 [x] (bit-and x 0xFFFFFFFF))

(defn- rotr [x n]
  (u32 (bit-or (unsigned-bit-shift-right x n) (bit-shift-left x (- 32 n)))))

(defn- padded
  "The message's bytes, 0..255, padded to a multiple of 64 with its bit
  length last."
  [bs]
  (let [n (count bs)
        zeros (mod (- 55 n) 64)
        bits (* 8 n)]
    (vec (concat bs [0x80] (repeat zeros 0)
                 (for [i (range 7 -1 -1)] (bit-and (unsigned-bit-shift-right bits (* 8 i)) 0xFF))))))

(defn- schedule [block]
  (let [w (vec (for [i (range 16)]
                 (reduce (fn [acc j] (bit-or (bit-shift-left acc 8) (nth block (+ (* 4 i) j)))) 0 (range 4))))]
    (reduce (fn [w i]
              (let [a (nth w (- i 15)) b (nth w (- i 2))
                    s0 (bit-xor (rotr a 7) (rotr a 18) (unsigned-bit-shift-right a 3))
                    s1 (bit-xor (rotr b 17) (rotr b 19) (unsigned-bit-shift-right b 10))]
                (conj w (u32 (+ (nth w (- i 16)) s0 (nth w (- i 7)) s1)))))
            w (range 16 64))))

(defn- compress [hs block]
  (let [w (schedule block)
        [a b c d e f g h]
        (reduce (fn [[a b c d e f g h] i]
                  (let [s1 (bit-xor (rotr e 6) (rotr e 11) (rotr e 25))
                        ch (bit-xor (bit-and e f) (bit-and (u32 (bit-not e)) g))
                        t1 (u32 (+ h s1 ch (nth k i) (nth w i)))
                        s0 (bit-xor (rotr a 2) (rotr a 13) (rotr a 22))
                        maj (bit-xor (bit-and a b) (bit-and a c) (bit-and b c))
                        t2 (u32 (+ s0 maj))]
                    [(u32 (+ t1 t2)) a b c (u32 (+ d t1)) e f g]))
                hs (range 64))]
    (mapv (fn [x y] (u32 (+ x y))) hs [a b c d e f g h])))

(defn sha256
  "The SHA-256 of string s, as 64 lowercase hex digits."
  [s]
  (let [bs (map #(bit-and % 0xFF) (.getBytes (str s) "UTF-8"))]
    (apply str (map #(format "%08x" %)
                    (reduce compress h0 (partition 64 (padded bs)))))))
