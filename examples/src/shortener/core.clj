(ns shortener.core
  "A URL shortener's logic, with no sockets and no storage.

  The links are a map from short code to URL. `handle` takes the links and
  a request, and returns the links after it with a reply:

    [:Created code]      a URL was shortened to `code`
    [:Found url]         a code leads to `url`
    [:Text status text]  anything else

  The layers are fixed, and the spec's `calls` forms hold them in place:
  `handle` only routes and dispatches; `shorten` owns validation and code
  assignment; the codec is `encode-id` and `decode-id`. None of it touches
  shortener.store, which is shortener.server's business."
  (:require [clojure.string :as str]))

(def alphabet "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")

(def max-digits 11)

(defn encode-id
  "The base-62 code for id `n`: its digits, most significant first, with no
  leading zeros. Eleven digits cover any 64-bit id."
  [n]
  (loop [fuel max-digits, n n, code ""]
    (let [code (str (nth alphabet (mod n 62)) code)
          n (quot n 62)]
      (if (and (pos? fuel) (pos? n))
        (recur (dec fuel) n code)
        code))))

(defn- digit [c]
  (str/index-of alphabet (str c)))

(defn valid-code? [s]
  (and (<= 1 (count s) max-digits)
       (every? #(some? (digit %)) s)))

(defn decode-id
  "The id a code stands for. Only a valid code has one."
  [code]
  (reduce (fn [n c] (+ (* n 62) (digit c))) 0 code))

(defn normalize-url [s]
  (str/trim s))

(defn valid-url? [s]
  (and (or (str/starts-with? s "http://") (str/starts-with? s "https://"))
       (< (count (str/replace s #"^https?://" "")) 2000)
       (pos? (count (str/replace s #"^https?://" "")))
       (not (re-find #"\s" s))))

(defn- code-for
  "The code `url` already has, or nil."
  [links url]
  (some (fn [[code u]] (when (= u url) code)) links))

(defn route [method path]
  (cond
    (and (= :get method) (= "/" path)) [:Index]
    (and (= :post method) (= "/" path)) [:Shorten]
    (and (= :get method) (str/starts-with? path "/") (valid-code? (subs path 1)))
    [:Follow (subs path 1)]
    :else [:Missing]))

(defn shorten
  "The links with `body`'s URL in them, and the reply. A URL already
  shortened keeps its code."
  [links body]
  (let [url (normalize-url body)]
    (cond
      (not (valid-url? url)) [links [:Text 400 "not an http(s) URL\n"]]
      (code-for links url) [links [:Created (code-for links url)]]
      :else (let [code (encode-id (count links))]
              [(assoc links code url) [:Created code]]))))

(defn follow [links code]
  (if (contains? links code)
    [:Found (get links code)]
    [:Text 404 "no such link\n"]))

(def usage
  "POST a URL to / to shorten it; GET /<code> to follow it.\n")

(defn handle [links method path body]
  (let [r (route method path)]
    (case (first r)
      :Index [links [:Text 200 usage]]
      :Shorten (shorten links body)
      :Follow (let [[_ code] r] [links (follow links code)])
      :Missing [links [:Text 404 "not found\n"]])))
