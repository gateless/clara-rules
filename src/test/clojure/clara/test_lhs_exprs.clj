(ns clara.test-lhs-exprs
  "Tests for LHS expressions that defrule and defquery compile at load time.
  Each var holds its compiled LHS fns in :clara.rules/exprs, keyed by condition data.
  mk-session uses these fns in place of eval, and equal condition data shares one fn."
  (:require [clara.rules :refer [defrule defquery mk-session insert insert! fire-rules query]]
            [clara.rules.accumulators :as acc]
            [clara.rules.dsl :as dsl]
            [clara.rules.engine :as eng]
            [clara.rules.testfacts :refer [->Temperature ->WindSpeed ->Cold]]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing]])
  (:import [clara.rules.testfacts Temperature WindSpeed Cold]))

(defrule cold-rule
  [Temperature (< temperature 0) (= ?t temperature)]
  =>
  (insert! (->Cold ?t)))

(defrule cold-and-windy-rule
  [Temperature (< temperature 0) (= ?t temperature)]
  [WindSpeed (< ?t windspeed)]
  [:test (some? ?t)]
  =>
  (insert! (->Cold (dec ?t))))

(defrule exists-rule
  [:exists [Temperature (< temperature 0)]]
  [WindSpeed (= ?w windspeed)]
  =>
  (insert! (->Cold ?w)))

(defquery cold-count-query
  []
  [?n <- (acc/count) :from [Cold]])

(defrule complex-negation-rule
  [Temperature (= ?t temperature)]
  [:not [:or [WindSpeed (= ?t windspeed)]
         [Cold (= ?t temperature)]]]
  =>
  (insert! (->Cold (* 10 ?t))))

(defquery cold-query
  []
  [Cold (= ?t temperature)])

(defrule temperature-and-cold-rule
  [Temperature (= ?t temperature)]
  [Cold (= ?t temperature)]
  =>
  nil)

(defquery temperature-query
  []
  [Temperature (= ?t temperature)])

(defn- precompiled-fns
  [& vars]
  (set (mapcat (comp vals :clara.rules/exprs meta) vars)))

(defn- expr-fns
  "Returns {expr-node-type #{fn}} for the compiled expressions of a session."
  [session]
  (reduce-kv (fn [m [_ expr-node-type] [f]]
               (update m expr-node-type (fnil conj #{}) f))
             {}
             (-> session eng/components :rulebase :node-expr-fn-lookup)))

(defn- eval-in-scratch-ns
  [form]
  (binding [*ns* (create-ns 'clara.test-lhs-exprs.scratch)]
    (refer-clojure)
    (eval form)))

(deftest test-lhs-error-at-load-time
  (testing "an LHS that does not compile fails when defrule is evaluated"
    (is (thrown? Exception
                 (eval-in-scratch-ns
                  '(clara.rules/defrule bad-rule
                     [clara.rules.testfacts.Temperature (= ?t (no-such-fn temperature))]
                     =>
                     nil)))))
  (testing "an LHS that does not compile fails when defquery is evaluated"
    (is (thrown? Exception
                 (eval-in-scratch-ns
                  '(clara.rules/defquery bad-query
                     []
                     [clara.rules.testfacts.Temperature (= ?t (no-such-fn temperature))]))))))

(deftest test-precompiled-lhs-fns-are-used
  (let [session (mk-session [cold-rule cold-and-windy-rule exists-rule cold-count-query]
                            :cache false
                            :compiler-cache false)
        precompiled (precompiled-fns #'cold-rule #'cold-and-windy-rule #'exists-rule #'cold-count-query)
        fns (expr-fns session)]
    (testing "every expression type of these productions is present"
      (is (= #{:alpha-expr :join-filter-expr :test-expr :accum-expr :action-expr}
             (set (keys fns)))))
    (testing "each LHS fn is a precompiled fn, even with the compiler cache disabled"
      (doseq [expr-node-type [:alpha-expr :join-filter-expr :test-expr :accum-expr]
              f (get fns expr-node-type)]
        (is (contains? precompiled f) (str expr-node-type " was not precompiled"))))
    (testing "each RHS fn is the rule var, even with the compiler cache disabled"
      (is (set/subset? #{#'cold-rule #'cold-and-windy-rule #'exists-rule}
                       (:action-expr fns))))
    (testing "the session gives the expected results"
      (is (= [{:?n 3}]
             (-> session
                 (insert (->Temperature -5 "MCI") (->WindSpeed 10 "MCI"))
                 (fire-rules)
                 (query cold-count-query)))))))

(deftest test-shared-condition-uses-one-fn
  (let [session (mk-session [cold-rule cold-and-windy-rule] :cache false)
        temperature-alphas (-> session eng/components :rulebase :alpha-roots (get Temperature))]
    (testing "both rules share the alpha node of the Temperature condition"
      (is (= 1 (count temperature-alphas))))
    (testing "the shared node uses the precompiled fn of one of the rules"
      (is (contains? (precompiled-fns #'cold-rule #'cold-and-windy-rule)
                     (:activation (first temperature-alphas)))))))

(deftest test-fact-type-is-part-of-the-key
  (testing "one rule keeps a fn for each fact type when the constraints are equal"
    (let [precompiled (precompiled-fns #'temperature-and-cold-rule)
          alpha-fns (:alpha-expr (expr-fns (mk-session [temperature-and-cold-rule] :cache false)))]
      (is (= 2 (count precompiled) (count alpha-fns)))
      (is (every? precompiled alpha-fns))))
  (testing "conditions that differ only in the fact type keep their own fns"
    (let [session (-> (mk-session [cold-query temperature-query] :cache false)
                      (insert (->Cold 1) (->Temperature 2 "MCI"))
                      (fire-rules))]
      (is (= [{:?t 1}] (query session cold-query)))
      (is (= [{:?t 2}] (query session temperature-query))))))

(deftest test-expr-keys-hold-no-classes
  (testing "a key holds class names, so it reads back from serialized data before the fact classes are loaded"
    (is (not-any? class?
                  (mapcat #(tree-seq coll? seq %)
                          (keys (:clara.rules/exprs (meta #'cold-and-windy-rule))))))))

(deftest test-fallback-to-eval
  (testing "a complex negation still compiles and fires"
    (is (= [{:?t 30}]
           (-> (mk-session [complex-negation-rule cold-query] :cache false)
               (insert (->Temperature 3 "MCI"))
               (fire-rules)
               (query cold-query)))))
  (testing "a rule built at runtime has no var and still compiles and fires"
    (let [rule (dsl/parse-rule [[Temperature (= ?t temperature)]]
                               (insert! (->Cold ?t)))]
      (is (= [{:?t 7}]
             (-> (mk-session [rule cold-query] :cache false)
                 (insert (->Temperature 7 "MCI"))
                 (fire-rules)
                 (query cold-query)))))))
