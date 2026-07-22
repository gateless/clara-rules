(ns clara.test-activation-cache
  "Tests for caching rule activation output across sessions.

  clara-rules only provides the key (clara.rules.activation-cache.core) and the
  engine hook: on a cache hit the stored RHS output is replayed and the RHS is
  skipped; on a miss the RHS runs and its output is recorded. The cache
  itself is caller-supplied — here a plain clojure.core.cache basic cache in an
  atom stands in for whatever the caller provides."
  (:require [clara.rules :refer [defrule defquery mk-session insert insert-all
                                 fire-rules fire-rules-async query insert!
                                 insert-unconditional! retract retract!]]
            [clara.rules.activation-cache.core :as ac]
            [clojure.core.cache.wrapped :as cache]
            [clojure.data.fressian :as fres]
            [clara.rules.testfacts :refer [->Temperature ->Cold ->Hot]]
            [futurama.core :refer [!<!!]]
            [clojure.test :refer :all])
  (:import [clara.rules.testfacts Temperature Cold Hot]))

;; Side-effect counters that RHS bodies can resolve in this namespace. Each test
;; resets the ones it uses. See the note in clara.test-rules about RHS bodies
;; only being able to reach vars in their defining namespace.
(def cold-runs (atom 0))
(def actions-runs (atom 0))

(defn- fresh-cache
  "A caller-style activation cache: an atom-wrapped CacheProtocol. A basic cache
  is enough to exercise the engine's lookup/hit/miss integration."
  []
  (cache/basic-cache-factory {}))

;; ---------------------------------------------------------------------------
;; Cache key
;; ---------------------------------------------------------------------------

(deftest test-build-cache-key-equality-and-round-trip
  (let [activation {:node {:production {:name "r" :env {} :props {:cache true}}}
                    :token {:bindings {:?t 10} :matches []}}
        k1 (ac/build-cache-key activation)
        k2 (ac/build-cache-key activation)
        different (ac/build-cache-key (assoc-in activation [:token :bindings :?t] 20))]
    (is (= k1 k2) "same node+token yields equal keys")
    (is (not= k1 different) "different bindings yield different keys")
    ;; A key that survives serialization must compare = to a freshly-built one,
    ;; otherwise it can never hit.
    (is (= k1 (fres/read (fres/write k1)))
        "key round-trips through fressian to an equal value")))

(deftest test-build-cache-key-with-fact-record-binding
  ;; Real bindings hold fact records, not plain scalars. The key must compare =
  ;; by value and survive serialization for those too, or a rule bound to a fact
  ;; can never hit.
  (let [act (fn [t] {:node {:production {:name "r" :env {} :props {:cache true}}}
                     :token {:bindings {:?t t} :matches []}})
        k (ac/build-cache-key (act (->Temperature 10 "MCI")))]
    (is (= k (ac/build-cache-key (act (->Temperature 10 "MCI"))))
        "equal fact-record bindings yield equal keys")
    (is (not= k (ac/build-cache-key (act (->Temperature 20 "MCI"))))
        "different fact-record bindings yield different keys")
    (is (= k (fres/read (fres/write k)))
        "a key holding a fact record round-trips through fressian to an equal value")))

;; ---------------------------------------------------------------------------
;; Engine integration
;; ---------------------------------------------------------------------------

(defrule cold-rule
  "Opted in via the :cache prop."
  {:cache true}
  [Temperature (= ?t temperature)]
  =>
  (swap! cold-runs inc)
  (insert! (->Cold ?t)))

(defrule cold-rule-no-cache
  "Not opted in: no :cache prop."
  [Temperature (= ?t temperature)]
  =>
  (swap! cold-runs inc)
  (insert! (->Cold ?t)))

(defrule actions-rule
  "Opted in and using every action kind: logical insert, unconditional insert,
  and retraction."
  {:cache true}
  [Temperature (= ?t temperature)]
  [Cold (= ?c temperature)]
  =>
  (swap! actions-runs inc)
  (insert-unconditional! (->Hot ?t))
  (retract! (->Cold ?c)))

(defquery cold-query [] [Cold (= ?c temperature)])
(defquery hot-query [] [Hot (= ?h temperature)])

(defn- cold-temps [session]
  (sort (map :?c (query session cold-query))))

(deftest test-hit-replays-without-running-rhs
  (reset! cold-runs 0)
  (let [base (mk-session [cold-rule cold-query])
        ca (fresh-cache)
        run (fn [] (-> base (insert (->Temperature 10 "MCI"))
                       (fire-rules {:activation-cache ca})))
        s1 (run)
        after-1 @cold-runs
        s2 (run)
        after-2 @cold-runs]
    (is (= [10] (cold-temps s1)))
    (is (= 1 after-1) "RHS runs on the first (miss) fire")
    (is (= [10] (cold-temps s2)) "the cached RHS output is still inserted on a hit")
    (is (= 1 after-2) "the RHS is skipped on a hit")))

(deftest test-logical-insertion-truth-maintenance-survives-hit
  ;; cold-rule uses a logical insert!. A replayed logical insertion must be
  ;; justified by the current activation's token, so retracting the supporting
  ;; fact after a cache hit still retracts the logically-inserted fact.
  (reset! cold-runs 0)
  (let [base (mk-session [cold-rule cold-query])
        ca (fresh-cache)
        ;; First fire is a miss: the RHS runs and its logical insertion is recorded.
        _ (-> base (insert (->Temperature 10 "MCI")) (fire-rules {:activation-cache ca}))
        ;; Second fire is a hit: the logical insertion is replayed without the RHS.
        s (-> base (insert (->Temperature 10 "MCI")) (fire-rules {:activation-cache ca}))]
    (is (= 1 @cold-runs) "RHS ran only on the miss")
    (is (= [10] (cold-temps s)) "the logically-inserted Cold is present after a hit")
    (let [s2 (-> s (retract (->Temperature 10 "MCI")) (fire-rules {:activation-cache ca}))]
      (is (= [] (cold-temps s2))
          "logically-inserted Cold is retracted when its support is removed after a cache hit"))))

(deftest test-opt-out-rule-never-caches
  (reset! cold-runs 0)
  (let [base (mk-session [cold-rule-no-cache cold-query])
        ca (fresh-cache)
        run (fn [] (-> base (insert (->Temperature 10 "MCI"))
                       (fire-rules {:activation-cache ca})))]
    (run)
    (run)
    (is (= 2 @cold-runs) "a rule without :cache runs every time")))

(deftest test-no-cache-supplied-behaves-normally
  (reset! cold-runs 0)
  (let [base (mk-session [cold-rule cold-query])
        s (-> base (insert (->Temperature 10 "MCI")) (fire-rules))]
    (is (= [10] (cold-temps s)))
    (is (= 1 @cold-runs) "without a cache opt, firing is unchanged")))

(deftest test-all-action-kinds-replay-on-hit
  (reset! actions-runs 0)
  (let [base (mk-session [actions-rule cold-query hot-query])
        ca (fresh-cache)
        run (fn []
              (let [s (-> base (insert-all [(->Temperature 42 "MCI") (->Cold -1)])
                          (fire-rules {:activation-cache ca}))]
                {:hot (sort (map :?h (query s hot-query)))
                 :cold (map :?c (query s cold-query))}))
        r1 (run)
        after-1 @actions-runs
        r2 (run)
        after-2 @actions-runs]
    (is (= {:hot [42] :cold []} r1)
        "miss: unconditional insert adds Hot, retraction removes Cold")
    (is (= 1 after-1))
    (is (= r1 r2) "unconditional insert and retract replay to the same state on a hit")
    (is (= 1 after-2) "the RHS is skipped on a hit even with unconditional/retract actions")))

(deftest test-hit-replays-without-running-rhs-async
  (reset! cold-runs 0)
  (let [base (mk-session [cold-rule cold-query])
        ca (fresh-cache)
        run (fn [] (-> base (insert (->Temperature 10 "MCI"))
                       (fire-rules-async {:activation-cache ca})
                       (!<!!)))
        s1 (run)
        after-1 @cold-runs
        s2 (run)
        after-2 @cold-runs]
    (is (= [10] (cold-temps s1)))
    (is (= 1 after-1) "RHS runs on the first (miss) async fire")
    (is (= [10] (cold-temps s2)) "the cached RHS output is still inserted on an async hit")
    (is (= 1 after-2) "the RHS is skipped on an async hit")))

;; ---------------------------------------------------------------------------
;; :activation-cache-key-fn override
;; ---------------------------------------------------------------------------

(deftest test-cache-key-fn-receives-activation-and-preserves-hit-miss
  ;; A key-fn that delegates to the default must see the activation map and keep
  ;; normal hit/miss behavior: two identical fires still run the RHS only once.
  (reset! cold-runs 0)
  (let [captured (atom nil)
        key-fn (fn [activation]
                 (reset! captured activation)
                 (ac/build-cache-key activation))
        base (mk-session [cold-rule cold-query])
        ca (fresh-cache)
        run (fn [] (-> base (insert (->Temperature 10 "MCI"))
                       (fire-rules {:activation-cache ca :activation-cache-key-fn key-fn})))
        _ (run)
        after-1 @cold-runs
        _ (run)
        after-2 @cold-runs]
    (is (contains? @captured :node) "the key-fn receives the activation's :node")
    (is (contains? @captured :token) "the key-fn receives the activation's :token")
    (is (= 1 after-1) "RHS runs on the first (miss) fire")
    (is (= 1 after-2)
        "delegating to build-cache-key preserves normal hit/miss (RHS skipped on hit)")))

(deftest test-cache-key-fn-overrides-default-keying
  ;; A constant key-fn collides activations with different bindings into one
  ;; entry, so the second fire (temp=20) hits the entry cached for temp=10 and
  ;; skips the RHS. The default key would treat them as distinct -> two runs.
  (reset! cold-runs 0)
  (let [base (mk-session [cold-rule cold-query])
        ca (fresh-cache)
        key-fn (fn [_] :constant-key)
        fire (fn [t] (-> base (insert (->Temperature t "MCI"))
                         (fire-rules {:activation-cache ca :activation-cache-key-fn key-fn})))]
    (fire 10)
    (is (= 1 @cold-runs) "first fire is a miss and runs the RHS")
    (fire 20)
    (is (= 1 @cold-runs)
        "constant key-fn collides different bindings, so the second fire hits and skips the RHS (the default key would miss -> 2)")))

(deftest test-cache-key-fn-overrides-default-keying-async
  (reset! cold-runs 0)
  (let [base (mk-session [cold-rule cold-query])
        ca (fresh-cache)
        key-fn (fn [_] :constant-key)
        fire (fn [t] (-> base (insert (->Temperature t "MCI"))
                         (fire-rules-async {:activation-cache ca :activation-cache-key-fn key-fn})
                         (!<!!)))]
    (fire 10)
    (is (= 1 @cold-runs) "first async fire is a miss and runs the RHS")
    (fire 20)
    (is (= 1 @cold-runs)
        "constant key-fn makes the second async fire hit and skip the RHS")))
