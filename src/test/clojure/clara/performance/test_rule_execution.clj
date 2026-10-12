(ns clara.performance.test-rule-execution
  (:require [clara.rules.accumulators :as acc]
            [clara.rules :as r]
            [clojure.test :refer :all]
            [clara.tools.testing-utils :refer [def-rules-test run-performance-test]]))

(defrecord AFact [id])
(defrecord BFact [id])
(defrecord ParentFact [a-id b-id])

(def counter (atom {:a-count 0
                    :b-count 0}))

(def number-of-facts 1500)

(def-rules-test test-get-in-perf
  {:rules [rule [[[?parent <- ParentFact]
                  [?as <- (acc/all) :from [AFact (= (:a-id ?parent) id)]]
                  [?bs <- (acc/all) :from [BFact (= (:b-id ?parent) id)]]]
                 '(do (swap! counter update :a-count inc))]]
   :sessions [session [rule] {}]}
  (let [parents (for [x (range number-of-facts)]
                  (->ParentFact x (inc x)))
        a-facts (for [id (range number-of-facts)]
                  (->AFact id))
        b-facts (for [id (range number-of-facts)]
                  (->BFact id))

        facts (doall (concat parents
                             a-facts
                             b-facts))]
    (run-performance-test {:description "Slow get-in perf"
                           :func #(-> session
                                      (r/insert-all facts)
                                      r/fire-rules)
                           :iterations 5
                           :mean-assertion (partial > 10000)})))

(defrecord Threshold [v])
(defrecord Temperature [temperature])

;; Each Threshold is a token in the AccumulateWithJoinFilterNode, and all Temperature facts share one binding group.
;; Inserting or retracting in small batches makes the node update the result of every token for each batch.
(def threshold-facts (mapv #(->Threshold (* 100 (inc %))) (range 10)))
(def temperature-batches (partition-all 10 (mapv ->Temperature (range 1000))))

(defn- run-accum-join-filter-perf
  [session accumulator-name]
  (let [thresholds-fired (-> session
                             (r/insert-all threshold-facts)
                             r/fire-rules)
        all-fired (reduce (fn [s batch]
                            (r/fire-rules (r/insert-all s batch)))
                          thresholds-fired
                          temperature-batches)]
    (run-performance-test {:description (str "AccumulateWithJoinFilterNode " accumulator-name " incremental insert")
                           :func #(reduce (fn [s batch]
                                            (r/fire-rules (r/insert-all s batch)))
                                          thresholds-fired
                                          temperature-batches)
                           :iterations 5
                           :verbose true
                           :mean-assertion (partial > 500)})
    (run-performance-test {:description (str "AccumulateWithJoinFilterNode " accumulator-name " incremental retract")
                           :func #(reduce (fn [s batch]
                                            (r/fire-rules (apply r/retract s batch)))
                                          all-fired
                                          temperature-batches)
                           :iterations 5
                           :verbose true
                           :mean-assertion (partial > 500)})))

(def-rules-test test-accum-join-filter-perf
  {:rules [all-rule [[[Threshold (= ?v v)]
                      [?ts <- (acc/all) :from [Temperature (< temperature ?v)]]]
                     '(identity ?ts)]
           count-rule [[[Threshold (= ?v v)]
                        [?n <- (acc/count) :from [Temperature (< temperature ?v)]]]
                       '(identity ?n)]]
   :sessions [all-session [all-rule] {}
              count-session [count-rule] {}]}
  (run-accum-join-filter-perf all-session "acc/all")
  (run-accum-join-filter-perf count-session "acc/count"))
