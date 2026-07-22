(ns clara.test-default-props
  "Tests for the :default-props mk-session option: a map of rule properties
  merged into every rule (productions with an :rhs) beneath each rule's own
  props. Precedence is session-default < namespace-level < rule-level, so a rule
  can override or opt out of a default. Queries are unaffected.

  Includes an integration test showing :default-props {:cache true} enables
  activation caching (see clara.rules.activation-cache.core) for a rule that
  never declared :cache."
  (:require [clara.rules :refer [defrule defquery mk-session insert fire-rules
                                 query insert!]]
            [clara.rules.engine :as eng]
            [clara.rules.compiler :as com]
            [clojure.core.cache.wrapped :as cache]
            [clara.rules.testfacts :refer [->Temperature ->Cold]]
            [clojure.test :refer :all])
  (:import [clara.rules.testfacts Temperature Cold]))

;; RHS side-effect counter. A rule's RHS can only reach vars in its defining
;; namespace, so the counter and the rules live here. Each test resets it.
(def rhs-runs (atom 0))

(defrule plain-rule
  "No :cache prop of its own; relies on whatever :default-props supplies."
  [Temperature (= ?t temperature)]
  =>
  (swap! rhs-runs inc)
  (insert! (->Cold ?t)))

(defrule opted-out-rule
  "Explicitly opts out of caching; must win over a session default."
  {:cache false}
  [Temperature (= ?t temperature)]
  =>
  (swap! rhs-runs inc)
  (insert! (->Cold ?t)))

(defquery cold-query [] [Cold (= ?c temperature)])

(defn- fresh-cache []
  (cache/basic-cache-factory {}))

(defn- cold-temps [session]
  (sort (map :?c (query session cold-query))))

(defn- rule-props
  "Map of rule-name -> final props for the rules (production nodes) in a session."
  [session]
  (->> (eng/components session)
       :rulebase
       :production-nodes
       (map (fn [n] [(get-in n [:production :name])
                     (get-in n [:production :props])]))
       (into {})))

(defn- query-props
  "The props on every query node in a session (queries should never receive
  default props)."
  [session]
  (->> (eng/components session)
       :rulebase
       :query-nodes
       vals
       (map (comp :props :query))))

(def ^:private plain-rule-name "clara.test-default-props/plain-rule")
(def ^:private opted-out-rule-name "clara.test-default-props/opted-out-rule")

;; ---------------------------------------------------------------------------
;; Merge + precedence
;; ---------------------------------------------------------------------------

(deftest test-default-props-merged-into-rule-without-props
  (let [s (mk-session [plain-rule cold-query] :default-props {:cache true})]
    (is (= {:cache true} (get (rule-props s) plain-rule-name))
        "a rule that declared no props receives the session default")))

(deftest test-rule-props-override-session-defaults
  (let [s (mk-session [opted-out-rule cold-query] :default-props {:cache true})]
    (is (= {:cache false} (get (rule-props s) opted-out-rule-name))
        "a rule's own prop wins over the session default")))

(deftest test-multiple-default-props-merged
  (let [s (mk-session [plain-rule cold-query] :default-props {:cache true :salience 5})]
    (is (= {:cache true :salience 5} (get (rule-props s) plain-rule-name))
        "every key in :default-props is merged into a rule that declared none")))

(deftest test-queries-unaffected
  (let [s (mk-session [plain-rule cold-query] :default-props {:cache true})]
    (is (every? nil? (query-props s))
        "queries never receive default props")))

(deftest test-no-default-props-leaves-props-unchanged
  (let [s (mk-session [plain-rule cold-query])]
    (is (nil? (get (rule-props s) plain-rule-name))
        "without :default-props a rule keeps its (absent) props")))

;; ---------------------------------------------------------------------------
;; Integration with activation caching
;; ---------------------------------------------------------------------------

(deftest test-default-cache-enables-caching-behaviorally
  (reset! rhs-runs 0)
  (let [base (mk-session [plain-rule cold-query] :default-props {:cache true})
        ca (fresh-cache)
        run (fn [] (-> base (insert (->Temperature 10 "MCI"))
                       (fire-rules {:cache ca})))
        s1 (run)
        after-1 @rhs-runs
        s2 (run)
        after-2 @rhs-runs]
    (is (= [10] (cold-temps s1)))
    (is (= 1 after-1) "RHS runs on the first (miss) fire")
    (is (= [10] (cold-temps s2)) "the cached RHS output is replayed on a hit")
    (is (= 1 after-2)
        "RHS is skipped on a hit because :default-props {:cache true} opted the rule in")))

(deftest test-without-default-props-rule-is-not-cached
  (reset! rhs-runs 0)
  (let [base (mk-session [plain-rule cold-query])
        ca (fresh-cache)
        run (fn [] (-> base (insert (->Temperature 10 "MCI"))
                       (fire-rules {:cache ca})))]
    (run)
    (run)
    (is (= 2 @rhs-runs)
        "without :default-props the rule never opts in, so its RHS runs every time")))

;; ---------------------------------------------------------------------------
;; add-production-load-data (the function mk-session uses to stamp load order
;; and merge default props). Tested directly on raw production maps, which the
;; defrule/defquery vars yield via their 0-arity.
;; ---------------------------------------------------------------------------

(defn- load-order [production]
  (:clara.rules.compiler/rule-load-order (meta production)))

(deftest test-add-production-load-data-adds-load-order-in-sequence
  (let [result (com/add-production-load-data [(plain-rule) cold-query] {})]
    (is (= [0 1] (map load-order result))
        "each production is stamped with its position as load order")))

(deftest test-add-production-load-data-merges-defaults-into-rules-only
  (let [[rule qry] (com/add-production-load-data [(plain-rule) cold-query]
                                                 {:default-props {:cache true}})]
    (is (some? (:rhs rule)) "first production is the rule")
    (is (= {:cache true} (:props rule)) "default props merged into the rule")
    (is (nil? (:rhs qry)) "second production is the query")
    (is (nil? (:props qry)) "the query is left untouched")))

(deftest test-add-production-load-data-existing-props-win
  (let [[rule] (com/add-production-load-data [(opted-out-rule)]
                                             {:default-props {:cache true}})]
    (is (= {:cache false} (:props rule))
        "a rule's own props take precedence over the session default")))

(deftest test-add-production-load-data-without-default-props
  (testing "empty :default-props merges nothing but still stamps load order"
    (let [[rule] (com/add-production-load-data [(plain-rule)] {})]
      (is (nil? (:props rule)))
      (is (= 0 (load-order rule)))))
  (testing "absent :default-props key merges nothing"
    (let [[rule] (com/add-production-load-data [(plain-rule)] {:some-other :opt})]
      (is (nil? (:props rule))))))
