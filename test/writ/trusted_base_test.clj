(ns writ.trusted-base-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [writ.hash :as hash]))

(deftest trusted-base-manifest-pins-current-sources
  (let [manifest (edn/read-string (slurp "docs/trusted-base.edn"))
        files (:files manifest)
        paths (mapv :path files)]
    (is (= 1 (:version manifest)))
    (is (= paths (vec (sort paths))))
    (is (= (count paths) (count (distinct paths))))
    (doseq [{:keys [path sha256]} files]
      (testing path
        (is (.exists (io/file path)))
        (is (= sha256 (hash/sha256 (slurp path))))))))

(deftest changed-trusted-content-does-not-match-its-pinned-hash
  (let [{:keys [path sha256]} (first (:files (edn/read-string (slurp "docs/trusted-base.edn"))))
        changed (str (slurp path) "\n;; deliberate trusted-base drift\n")]
    (is (not= sha256 (hash/sha256 changed)))))
