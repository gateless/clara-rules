(ns clara.test-engine
  "Test suite for the Clara rules engine with async rules and queries.
   This test suite benchmarks the performance of async rules and queries
   using a parallel compute engine."
  {:author "Jose Gomez"
   :salience 1000}
  (:require [clara.rules :refer [mk-session
                                 fire-rules
                                 fire-rules-async
                                 query
                                 defrule defquery
                                 insert-all
                                 insert!]]
            [clara.rules.dsl :as dsl]
            [clojure.core.async :refer [go timeout <!]]
            [futurama.core :refer [async !<! !<!!]]
            [clojure.test :refer [deftest testing is]]
            [criterium.core :refer [report-result
                                    with-progress-reporting
                                    quick-benchmark]]))

(dsl/add-allowed-ns-props! :foo)

(defrule test-slow-rule-1
  "this rule does some async work using go block"
  {:foo "bar"}
  [:number [{:keys [value]}]
   (= value ?value)
   (pos? ?value)]
  =>
  (go
    (<! (timeout 50))
    (insert! {:type :result
              :value (+ ?value 100)})))

(defrule test-slow-rule-2
  "this rule does some async work using async block"
  [:result [{:keys [value]}]
   (= value ?value)
   (pos? ?value)]
  =>
  (async
   (!<! (timeout 50))
   (insert! {:type :output
             :value (inc ?value)})))

(defrule test-override-rule
  "rule-level props must override namespace-level props"
  {:salience 42 :cache true}
  [:number [{:keys [value]}]
   (= value ?value)]
  =>
  (insert! {:type :override-noop
            :value ?value}))

(deftest test-engine-namespace-props
  (testing "rule properties and namespace properties are merged correctly"
    (is (= {:author "Jose Gomez"
            :salience 1000
            :foo "bar"}
           (:props (test-slow-rule-1)))))
  (testing "namespace properties are not lost in rules"
    (is (= {:author "Jose Gomez"
            :salience 1000}
           (:props (test-slow-rule-2)))))
  (testing "rule-level props override conflicting namespace-level props"
    (is (= {:author "Jose Gomez"   ; ns prop retained (no conflict)
            :salience 42           ; rule wins over ns :salience 1000
            :cache true}           ; :cache set at the rule level
           (:props (test-override-rule))))))

(deftest test-build-rule-prop-merge
  (testing ":cache is an allowed namespace property"
    (is (contains? dsl/allowed-ns-props-set :cache)))
  (testing "rule props override namespace props, and disjoint ns props are kept"
    ;; Mirrors how the defrule macro invokes build-rule, passing the namespace
    ;; properties as a trailing map (see clara.rules/defrule).
    (let [rule (dsl/build-rule 'r
                               '[{:salience 10 :cache true}
                                 [:number (= value ?value)]
                                 => (do nil)]
                               {} nil
                               {:salience 999 :author "ns" :cache false})]
      (is (= {:salience 10 :author "ns" :cache true}
             (:props rule))))))

(defquery test-slow-query
  []
  [:output [{:keys [value]}] (= value ?value)])

(def session-50
  (let [fact-seq (repeat 50 {:type :number
                             :value 199})
        session (-> (mk-session 'clara.test-engine :fact-type-fn :type :cache false)
                    (insert-all fact-seq))]
    session))

(def session-10000
  (let [fact-seq (repeat 10000 {:type :number
                                :value 199})
        session (-> (mk-session 'clara.test-engine :fact-type-fn :type)
                    (insert-all fact-seq))]
    session))

(deftest parallel-compute-engine-performance-test
  (testing "parallel compute with large batch size for non-blocking io - 50 facts - 100 batch size"
    (let [result (with-progress-reporting
                   (quick-benchmark
                    (-> (!<!! (fire-rules-async session-50 {:parallel-batch-size 100}))
                        (query test-slow-query)
                        (count))
                    {:verbose true}))
          [mean [lower upper]] (:mean result)]
      (is (<= 0.1 lower mean upper 0.2)) ;;; our lower and mean values should be between 100ms and 200ms
      (report-result result)))
  (testing "parallel compute with large batch size for non-blocking io - 10000 facts - 20000 batch size"
    (let [result (with-progress-reporting
                   (quick-benchmark
                    (-> (!<!! (fire-rules-async session-10000 {:parallel-batch-size 20000}))
                        (query test-slow-query)
                        (count))
                    {:verbose true}))
          [mean [lower upper]] (:mean result)]
      (is (<= 0.1 lower mean upper 2.0)) ;;; our lower and mean values should be between 100ms and 1000ms, but CI sometimes is slow
      (report-result result))))
