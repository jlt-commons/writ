(ns examples-test
  "Every example book, checked end to end.

  Each PROOF namespace exposes a `verify` that reads its main/LAWS/PROOF files
  and runs them through writ's rule engine, so a failure here is a real rule
  violation in the example, not just a compile error."
  (:require [clojure.test :refer [deftest is testing]]
            [proof-numerics.PROOF :as numerics]
            [proof-typed-eval.PROOF :as typed-eval]
            [proof-insertion-sort.PROOF :as insertion-sort]
            [pure-par-sum.PROOF :as par-sum]
            [pure-par-sort.PROOF :as par-sort]
            [pure-hvm5-mini.PROOF :as hvm5]
            [io-http-fetch.PROOF :as http-fetch]
            [io-hello-world.PROOF :as hello-world]
            [io-tcp-echos.PROOF :as tcp-echos]
            [io-http-server.PROOF :as http-server]
            [io-rollback-netcode.PROOF :as netcode]
            [app-pong-game-2d.PROOF :as pong]
            [app-triangle-2d.PROOF :as triangle]
            [app-ray-tracer-3d.PROOF :as ray-tracer]
            [app-slash-boss-3d.PROOF :as slash-boss]
            [app-win-is-bug-2d.PROOF :as win-is-bug]
            [theory-kinds.PROOF :as theory-kinds]
            [theory-discipline.PROOF :as theory-discipline]))

(deftest proof-numerics
  (testing "proof_numerics discharges every law"
    (is (= {:ok true} (numerics/verify)))))

(deftest proof-typed-eval
  (testing "proof_typed_eval discharges every law"
    (is (= {:ok true} (typed-eval/verify)))))

(deftest proof-insertion-sort
  (testing "proof_insertion_sort discharges every law"
    (is (= {:ok true} (insertion-sort/verify)))))

(deftest pure-par-sum
  (testing "pure_par_sum discharges every law"
    (is (= {:ok true} (par-sum/verify)))))

(deftest pure-par-sort
  (testing "pure_par_sort discharges every law"
    (is (= {:ok true} (par-sort/verify)))))

(deftest pure-hvm5-mini
  (testing "pure_hvm5_mini discharges every law"
    (is (= {:ok true} (hvm5/verify)))))

(deftest io-http-fetch
  (testing "io_http_fetch discharges every law"
    (is (= {:ok true} (http-fetch/verify)))))

(deftest io-hello-world
  (testing "io_hello_world discharges every law"
    (is (= {:ok true} (hello-world/verify)))))

(deftest io-tcp-echos
  (testing "io_tcp_echos discharges every law"
    (is (= {:ok true} (tcp-echos/verify)))))

(deftest io-http-server
  (testing "io_http_server discharges every law"
    (is (= {:ok true} (http-server/verify)))))

(deftest io-rollback-netcode
  (testing "io_rollback_netcode discharges every law"
    (is (= {:ok true} (netcode/verify)))))

(deftest app-pong-game-2d
  (testing "app_pong_game_2d discharges every law"
    (is (= {:ok true} (pong/verify)))))

(deftest app-triangle-2d
  (testing "app_triangle_2d discharges every law"
    (is (= {:ok true} (triangle/verify)))))

(deftest app-ray-tracer-3d
  (testing "app_ray_tracer_3d discharges every law"
    (is (= {:ok true} (ray-tracer/verify)))))

(deftest app-slash-boss-3d
  (testing "app_slash_boss_3d discharges every law"
    (is (= {:ok true} (slash-boss/verify)))))

(deftest app-win-is-bug-2d
  (testing "app_win_is_bug_2d discharges every law"
    (is (= {:ok true} (win-is-bug/verify)))))

(deftest theory-kinds
  (testing "theory_kinds exercises the kind rule and the richer law surface"
    (is (= {:ok true} (theory-kinds/verify)))))

(deftest theory-discipline
  (testing "theory_discipline exercises the closed gaps: local and pattern
            quantities, mandatory descent, recur, parametric kinds and match,
            scrutinee provenance, ordered citations and def ordering"
    (is (= {:ok true} (theory-discipline/verify)))))
