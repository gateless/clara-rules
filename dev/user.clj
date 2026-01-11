(ns user
  (:require [criterium.core :refer [report-result
                                    quick-benchmark
                                    with-progress-reporting] :as crit]
            [clara.rules :refer [defrule defquery defhierarchy
                                 insert! insert-all!
                                 insert insert-all
                                 fire-rules
                                 query
                                 mk-session
                                 clear-ns-vars!]]
            [clara.rules.accumulators :as acc]
            [clara.rules.engine :as eng]
            [clara.tools.inspect :as inspect]
            [clojure.core.cache.wrapped :as cache]))

(comment
  (clear-ns-vars!)
  (add-tap #'println)
  (remove-tap #'println))

(defhierarchy foobar
  :thing/foo :thing/that
  :thing/bar :thing/that)

(defrule return-a-thing
  [:thing/that [{:keys [value]}] (= value ?value)]
  =>
  (insert! {:type :thing/result
            :value ?value}))

(defrule return-a-thang
  [?thang <- :thang/that [{:keys [value]}] (= value ?value)]
  [?thing <- :thing/that [{:keys [value]}] (= value ?value)]
  [?zulu <- (acc/all) :from [:zulu/that]]
  [:test (and (some? ?thing)
              (some? ?thang)
              (some? ?zulu))]
  =>
  (insert! {:type :thang/result
            :value ?value}))

(defquery query-a-thing
  []
  [?output <- :thing/result])

(defquery query-a-thang
  []
  [?output <- :thang/result])

(comment
  (do
    (def facts1
      [{:type :thing/foo
        :value 1}
       {:type :thing/bar
        :value 2}
       {:type :thang/that
        :value 3}
       {:type :zulu/that
        :value 4}
       {:type :zulu/that
        :value 5}
       {:type :unmatched-it
        :value 100}])

    (def facts2
      [{:type :thing/that
        :value 3}])

    (def session
      (-> (mk-session 'user :fact-type-fn :type)
          (insert-all facts1)
          (fire-rules)
          (insert-all facts2)
          (fire-rules)))

    (def components
      (eng/components session))

    (def get-alphas-fn
      (-> components :rulebase :get-alphas-fn)))

  (-> components :memory keys)

  (->> components :memory :alpha-memory
       vals
       (mapcat vals)
       (mapcat identity)
       (map :fact))
  (->> components :memory :beta-memory
       vals
       (mapcat vals)
       (mapcat identity)
       (mapcat :matches)
       (map first))
  (->> components :memory :accum-memory
       vals
       (mapcat vals)
       (mapcat vals)
       (mapcat first))
  (-> components :memory :production-memory)

  (get-alphas-fn facts1)
  (get-alphas-fn facts2)

  (query session query-a-thing)
  (query session query-a-thang)

  (inspect/inspect-facts session))

(def session-cache
  (cache/lru-cache-factory {}))

;; Cache of compiled expressions
(def compiler-cache
  (cache/soft-cache-factory {}))

(defmacro mk-types
  [n]
  (let [facts (for [n (range n)]
                {:fact-type {:t (symbol (format "FactType%s" n))
                             :c (symbol (format "%s.FactType%s" (ns-name *ns*) n))}
                 :fact-record {:t (symbol (format "FactRecord%s" n))
                               :c (symbol (format "%s.FactRecord%s" (ns-name *ns*) n))}})
        type-declarations (for [{{:keys [t]} :fact-type} facts]
                            `(deftype ~t []))
        record-declarations (for [{{:keys [t]} :fact-record} facts]
                              `(defrecord ~t []))]
    `(do
       ~@type-declarations
       ~@record-declarations)))

(defmacro mk-rules
  [n]
  (let [facts (for [n (range n)]
                {:decl-name (symbol (format "rule-%s" n))
                 :fact-type {:t (symbol (format "FactType%s" n))
                             :c (symbol (format "%s.FactType%s" (ns-name *ns*) n))}
                 :fact-record {:t (symbol (format "FactRecord%s" n))
                               :c (symbol (format "%s.FactRecord%s" (ns-name *ns*) n))}})
        fact-rules (for [{:keys [fact-type
                                 fact-record]} facts]
                     `(hash-map
                       :ns-name (ns-name *ns*)
                       :lhs [{:type ~(:c fact-type)
                              :constraints []}
                             {:type ~(:c fact-record)
                              :constraints []}]
                       :rhs '(println (str "class:" ~n ~fact-type ~fact-record))))
        decl-rules (for [{:keys [decl-name
                                 fact-type
                                 fact-record]} facts]
                     `(defrule ~decl-name
                        [~(:c fact-type)]
                        [~(:c fact-record)]
                        =>
                        (println (str "class:" ~n ~fact-type ~fact-record))))]
    `(do
       ~@decl-rules
       (vector
        ~@fact-rules))))

(comment
  (clear-ns-vars!)
  (mk-types 2500)
  (def rules
    (mk-rules 2500))
  (keys @session-cache)
  (when-let [v (first (.cache ^clojure.core.cache.SoftCache @compiler-cache))]
    (.getValue v))
  (count @session-cache)
  (count (.cache ^clojure.core.cache.SoftCache @compiler-cache))

  (time
   (mk-session 'user [(conj rules {:ns-name (ns-name *ns*)
                                   :lhs [{:type :foobar1
                                          :constraints []}]
                                   :rhs `(println ~(str :foobar))})]
               :cache session-cache
               :compiler-cache compiler-cache)))
