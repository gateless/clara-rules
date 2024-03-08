(ns clara.miss-manners.manners-test
  (:require [clara.rules :refer [defrule defquery
                                 insert! insert-unconditional!] :as r]
            [clara.rules.accumulators :as acc]
            [clara.miss-manners.manners-data :as d]
            [clojure.set :as set]))

(r/clear-ns-productions!)

(defquery party-solution-query
  []
  [?output <- :party/solution])

(defquery party-solution-node-query
  []
  [?output <- :party/solution-node])

(defrule guest-rule
  [?guest-data <- (acc/all) :from [:party/guest-data [{:keys [name]}] (= name ?name)]]
  =>
  (insert! {:fact/type :party/guest
            :name ?name
            :sex (some :sex ?guest-data)
            :hobby-set (set (map :hobby ?guest-data))}))

(defrule guest-compatility-rule
  [:party/guest [{:keys [name sex hobby-set]}]
   (= name ?name) (= sex ?sex) (= hobby-set ?hobby-set)]
  [?name-set <- (acc/distinct :name)
   :from [:party/guest [{:keys [sex hobby-set]}]
          (not= ?sex sex)
          (seq (set/intersection ?hobby-set hobby-set))]]
  =>
  (insert! {:fact/type :party/guest-compatibility
            :name ?name
            :compatible-name-set ?name-set}))

(defrule guest-compatility-map-rule
  [?quest-compatibility-seq <- (acc/all) :from [:party/guest-compatibility]]
  =>
  (insert! {:fact/type :party/guest-compatibility-map
            :value (->> ?quest-compatibility-seq
                        (map (juxt :name :compatible-name-set))
                        (into {}))}))

#_(defrule party-solution-root-rule
    [:party/guest-compatibility-map [{:keys [value]}] (= value ?guest-compatibility)]
    =>
    (let [[name & name-seq] (keys ?guest-compatibility)
          remaining-name-set (set name-seq)]
      (insert! {:fact/type :party/solution-node
                :name name
                :remaining-name-set remaining-name-set
                :compatible-name-set (get ?guest-compatibility name)
                :party-head name
                :party-tail name
                :party-size 1
                :party-seat-solution [name]})))

#_(defrule party-solution-node-rule
    [:not [:party/solution]]
    [:party/seats-data [{:keys [size]}] (= size ?seat-count)]
    [:party/guest-compatibility-map [{:keys [value]}] (= value ?guest-compatibility)]
    [?node <- :party/solution-node
     [{:keys [remaining-name-set compatible-name-set]}]
     (seq (set/intersection compatible-name-set remaining-name-set))]
    =>
    (let [{:keys [remaining-name-set
                  compatible-name-set
                  party-head
                  party-size
                  party-seat-solution]} ?node]
      (doseq [name (set/intersection compatible-name-set remaining-name-set)]
        (insert-unconditional!
         {:fact/type :party/solution-node
          :name name
          :remaining-name-set (disj remaining-name-set name)
          :compatible-name-set (get ?guest-compatibility name #{})
          :party-head (or party-head name)
          :party-tail name
          :party-size (inc party-size)
          :party-seat-solution (conj party-seat-solution name)}))))

#_(defrule party-solution-rule
    [:not [:party-solution]]
    [:party/seats-data [{:keys [size]}] (= size ?seat-count)]
    [:party/guest-compatibility-map [{:keys [value]}]
     (= value ?guest-compatibility)]
    [:party/solution-node [{:keys [party-size party-head party-tail party-seat-solution]}]
     (= party-size ?seat-count)
     (contains? (get ?guest-compatibility party-head) party-tail)
     (= party-seat-solution ?solution)]
    =>
    (insert-unconditional! {:fact/type :party/solution
                            :solution ?solution}))

(defn party-solution?
  [compatibility-map seat-count {:keys [party-size
                                        party-head
                                        party-tail
                                        party-seat-solution]}]
  (when (= party-size seat-count)
    (let [compatible-name-set (get compatibility-map party-head)]
      (when (contains? compatible-name-set party-tail)
        party-seat-solution))))

(defn party-branch?
  [{:keys [remaining-name-set
           compatible-name-set]}]
  (seq (set/intersection compatible-name-set remaining-name-set)))

(defn party-children
  [compatibility-map {:keys [remaining-name-set
                             compatible-name-set
                             party-head
                             party-size
                             party-seat-solution]}]
  (for [name (set/intersection compatible-name-set remaining-name-set)]
    {:name name
     :remaining-name-set (disj remaining-name-set name)
     :compatible-name-set (get compatibility-map name #{})
     :party-head (or party-head name)
     :party-tail name
     :party-size (inc party-size)
     :party-seat-solution (conj party-seat-solution name)}))

(defrule party-solution-rule
  [:party/seats-data [{:keys [size]}] (= size ?seat-count)]
  [:party/guest-compatibility-map [{:keys [value]}] (= value ?guest-compatibility)]
  =>
  (let [[name & name-seq] (keys ?guest-compatibility)
        remaining-name-set (set name-seq)
        root-node {:name name
                   :remaining-name-set remaining-name-set
                   :compatible-name-set (get ?guest-compatibility name)
                   :party-head name
                   :party-tail name
                   :party-size 1
                   :party-seat-solution [name]}
        is-solution? (partial party-solution? ?guest-compatibility ?seat-count)
        get-children (partial party-children ?guest-compatibility)
        solution (some
                  is-solution?
                  (tree-seq party-branch?
                            get-children
                            root-node))]
    (when solution
      (insert! {:fact/type :party/solution
                :solution solution}))))

(time
 (-> (r/mk-session 'clara.miss-manners.manners-test :fact-type-fn :fact/type)
     (r/insert-all d/manners-128-guest-facts)
     (r/fire-rules)
     (r/query party-solution-query)
     (first)
     :?output
     :solution))
