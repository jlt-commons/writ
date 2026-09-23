(ns shortener.core-spec
  "The contract for shortener.core.

  The laws say what the shortener does: a code decodes to the id it came
  from, a short link leads back to its URL, shortening is idempotent, and
  a bad URL changes nothing. The `calls` forms say how it is built, which
  no law can see: the request path goes through one layer per concern,
  and the core never reaches shortener.store. writ lets calls into other
  namespaces through its purity check, so a store write from the core
  would pass every law; the call graph is what catches it.

  A link store the laws use is always one the shortener could have built:
  `store-of` shortens a generated list of URLs into an empty store."
  (:require [clojure.string :as str]
            [shortener.core :refer [handle]]
            [writ.spec :refer [spec data ann law calls]]))

(spec shortener.core)

(data Route Index Shorten (Follow String) Missing)
(data Reply (Created String) (Found String) (Text Nat String))

(ann encode-id     [Nat -> String])
(ann decode-id     [String -> Nat])
(ann valid-code?   [String -> Bool])
(ann valid-url?    [String -> Bool])
(ann normalize-url [String -> String])
(ann route         [Keyword String -> Route])
(ann shorten       [(Map String String) String -> (Tuple (Map String String) Reply)])
(ann follow        [(Map String String) String -> Reply])
(ann handle        [(Map String String) Keyword String String
                    -> (Tuple (Map String String) Reply)])

;; --- the call graph ------------------------------------------------------------

(calls handle        [route shorten follow])
(calls shorten       [normalize-url valid-url? code-for encode-id])
(calls follow        [])
(calls route         [valid-code? str/starts-with?])
(calls valid-code?   [digit])
(calls decode-id     [digit])
(calls encode-id     [])
(calls normalize-url [str/trim])

;; --- vocabulary -------------------------------------------------------------------

(defn big
  "An id past what a generated Nat reaches, so codes of several digits
  are tried too."
  [a b c]
  (+ a (* b 62) (* c 62 62 62 62 62)))

(defn web-url [s]
  (str "https://example.com/" (str/replace s #"\s" "")))

(defn store-of [paths]
  (reduce (fn [links p] (first (handle links :post "/" (web-url p)))) {} paths))

(defn status [[_ reply]]
  (case (first reply) :Created 201 :Found 302 :Text (second reply)))

(defn code-of [[_ reply]] (when (= :Created (first reply)) (second reply)))

(defn visit
  "Follow the link a shortening created."
  [[links reply]]
  (second (handle links :get (str "/" (second reply)) "")))

;; --- codes ------------------------------------------------------------------------

(law a-code-decodes-to-its-id
  (forall [a Nat, b Nat, c Nat]
    (= (big a b c) (decode-id (encode-id (big a b c))))))

(law a-code-is-canonical
  (forall [a Nat, b Nat, c Nat]
    (and (valid-code? (encode-id (big a b c)))
         (or (= "0" (encode-id (big a b c)))
             (not= \0 (first (encode-id (big a b c))))))))

(law codes-are-anchored (and (= "0" (encode-id 0)) (= "10" (encode-id 62))
                             (= "Z" (encode-id 61))))

(law a-code-is-short-alphanumeric
  (forall [s String]
    (= (valid-code? s)
       (boolean (and (<= 1 (count s) 11) (every? #(re-matches #"[0-9a-zA-Z]" (str %)) s))))))

;; --- urls --------------------------------------------------------------------------

(law only-web-urls-are-kept
  (forall [s String]
    (and (valid-url? (web-url s))
         (not (valid-url? (str "ftp://example.com/" s)))
         (not (valid-url? (str "https://exa mple.com/" s)))
         (not (valid-url? "https://")))))

(law surrounding-space-is-dropped
  (forall [s String] (= (normalize-url (str "  " (web-url s) "\n")) (web-url s))))

;; --- routes --------------------------------------------------------------------------

(law every-code-has-a-route
  (forall [a Nat, b Nat, c Nat]
    (= [:Follow (encode-id (big a b c))] (route :get (str "/" (encode-id (big a b c)))))))

(law the-fixed-routes
  (forall [s String]
    (and (= [:Index] (route :get "/"))
         (= [:Shorten] (route :post "/"))
         (= [:Missing] (route :post (str "/x" s)))
         (= [:Missing] (route :get (str "/!" s))))))

;; --- the shortener -------------------------------------------------------------------

(law a-short-link-leads-back
  (forall [paths (List String), p String]
    (= [:Found (web-url p)] (visit (handle (store-of paths) :post "/" (web-url p))))))

(law shortening-twice-gives-the-same-code
  (forall [paths (List String), p String]
    (= (code-of (handle (store-of paths) :post "/" (web-url p)))
       (code-of (handle (store-of (conj (vec paths) p)) :post "/" (web-url p))))))

(law different-urls-get-different-codes
  (forall [paths (List String), p String, q String]
    (=> (not= (web-url p) (web-url q))
        (not= (code-of (handle (store-of (conj (vec paths) q)) :post "/" (web-url p)))
              (code-of (handle (store-of paths) :post "/" (web-url q)))))))

(law a-bad-url-changes-nothing
  (forall [paths (List String), s String]
    (= [(store-of paths) [:Text 400 "not an http(s) URL\n"]]
       (handle (store-of paths) :post "/" (str "ftp://" s)))))

(law an-unknown-code-is-not-found
  (forall [paths (List String), a Nat]
    (=> (<= (count (store-of paths)) a)
        (= 404 (status (handle (store-of paths) :get (str "/" (encode-id a)) ""))))))

(law other-methods-are-not-found
  (forall [m Keyword, path String, paths (List String)]
    (=> (not (contains? #{:get :post} m))
        (and (= [:Missing] (route m path))
             (= 404 (status (handle (store-of paths) m path "")))))))

(law the-index-explains-itself
  (= 200 (status (handle {} :get "/" ""))))
