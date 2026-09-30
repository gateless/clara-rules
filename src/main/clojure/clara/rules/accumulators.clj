(ns clara.rules.accumulators
  "A set of common accumulators usable in Clara rules."
  (:require [clara.rules.engine :as eng]
            [schema.core :as s]
            [clara.rules.accumulators.gb-tree :as gb-tree])
  (:refer-clojure :exclude [min max distinct count]))

(defn accum
  "Creates a new accumulator. Users are encouraged to use a pre-defined
   accumulator in this namespace if one fits their needs. (See min, max, all,
   distinct, and others in this namespace.) This function
   exists for cases where a custom accumulator is necessary.

   The following properties are accepted.

   * An initial-value to be used with the reduced operations.
   * A reduce-fn that can be used with the Clojure Reducers library to reduce items.
   * An optional combine-fn that can be used with the Clojure Reducers library to combine reduced items.
   * An optional retract-fn that can remove a retracted fact from a previously reduced computation.
   * An optional convert-return-fn that converts the reduced data into something useful to the caller.
     Simply uses identity by default.
    "
  [{:keys [initial-value reduce-fn combine-fn retract-fn convert-return-fn] :as accum-map}]

  ;; Validate expected arguments are present.
  (s/validate {(s/optional-key :initial-value) s/Any
               (s/optional-key :combine-fn) s/Any
               (s/optional-key :convert-return-fn) s/Any
               :reduce-fn s/Any
               (s/optional-key :retract-fn) s/Any}
              accum-map)

  (eng/map->Accumulator
   (merge {;; Default conversion does nothing, so use identity.
           :convert-return-fn identity}
          accum-map)))

(defn drop-first [value]
  (fn [rf]
    (let [filtering (volatile! true)]
      (fn
        ([] (rf))
        ([accum] (rf accum))
        ([accum value']
         (if (and @filtering
                  (= value value'))
           (do
             (vreset! filtering false)
             accum)
           (rf accum value')))))))

(defn- drop-one-of
  "Removes one instance of the given value from the sequence."
  [items value]
  (into (empty items)
        (drop-first value)
        items))

(defn reduce-to-accum
  "Creates an accumulator using a given reduce function with optional initial value and
   conversion to the final result.

   For example, a a simple function that return a Temperature fact with the highest value:

     (acc/reduce-to-accum
        (fn [previous value]
           (if previous
              (if (> (:temperature value) (:temperature previous))
                 value
                 previous)
              value)))

   Note that the above example produces the same result as
   (clara.rules.accumulators/max :temperature :returns-fact true),
   and users should prefer to use built-in accumulators when possible. This funciton exists to easily
   convert arbitrary reduce functions to an accumulator.

   Callers may optionally pass in an initial value (which defaults to nil),
   a function to transform the value returned by the reduce (which defaults to identity),
   and a function to combine two reduced results (which uses the reduce-fn to add new 
   items to the same reduced value by default)."

  ([reduce-fn]
   (reduce-to-accum reduce-fn nil))
  ([reduce-fn initial-value]
   (reduce-to-accum reduce-fn initial-value identity))
  ([reduce-fn initial-value convert-return-fn]
   (reduce-to-accum reduce-fn initial-value convert-return-fn nil))
  ([reduce-fn initial-value convert-return-fn combine-fn]
   (accum (cond-> {:initial-value initial-value
                   :reduce-fn reduce-fn
                   :convert-return-fn convert-return-fn}
            combine-fn (assoc :combine-fn combine-fn)))))

(def ^:private grouping-fn (fnil conj []))

(defn grouping-by
  "Return a generic grouping accumulator. Behaves like clojure.core/group-by.

  * `field` - required - The field of a fact to group by.
  * `convert-return-fn` - optional - Converts the resulting grouped
  data. Defaults to clojure.core/identity."
  ([field]
   (grouping-by field identity))
  ([field convert-return-fn]
   {:pre [(ifn? convert-return-fn)]}
   (reduce-to-accum
    (fn [m x]
      (let [v (field x)]
        (update m v grouping-fn x)))
    {}
    convert-return-fn)))

(defn- comparison-based
  "Creates a comparison-based result such as min or max"
  [field comparator returns-fact]
  (let [reduce-fn (fn [previous value]
                    (if previous
                      (if (comparator (field previous) (field value))
                        previous
                        value)
                      value))

        convert-return-fn (if returns-fact
                            identity
                            field)]
    (accum
     {:reduce-fn reduce-fn
      :convert-return-fn convert-return-fn})))

(defn min
  "Returns an accumulator that returns the minimum value of a given field.

   The caller may provide the following options:

   * :returns-fact Returns the fact rather than the field value if set to true. Defaults to false."
  [field & {:keys [returns-fact]}]
  (comparison-based field < returns-fact))

(defn max
  "Returns an accumulator that returns the maximum value of a given field.

   The caller may provide the following options:

   * :returns-fact Returns the fact rather than the field value if set to true. Defaults to false."
  [field & {:keys [returns-fact]}]
  (comparison-based field > returns-fact))

(defn average
  "Returns an accumulator that returns the average value of a given field."
  [field]
  (accum
   {:initial-value [0 0]
    :reduce-fn (fn [[value count] item]
                 [(+ value (field item)) (inc count)])
    :retract-fn (fn [[value count] retracted]
                  [(- value (field retracted)) (dec count)])
    :combine-fn (fn [[value1 count1] [value2 count2]]
                  [(+ value1 value2) (+ count1 count2)])
    :convert-return-fn (fn [[value count]]
                         (if (= 0 count)
                           nil
                           (/ value count)))}))

(defn sum
  "Returns an accumulator that returns the sum of values of a given field"
  [field & {:keys [default-value] :or {default-value 0}}]
  (accum
   {:initial-value 0
    :reduce-fn (fn [total item]
                 (+ total (or (field item) default-value)))
    :retract-fn (fn [total item]
                  (- total (or (field item) default-value)))
    :combine-fn +}))

(defn count
  "Returns an accumulator that simply counts the number of matching facts"
  []
  (accum
   {:initial-value 0
    :reduce-fn (fn [count value] (inc count))
    :retract-fn (fn [count retracted] (dec count))
    :combine-fn +}))

(defn exists
  "Returns an accumulator that accumulates to true if at least one fact
   exists and nil otherwise, the latter causing the accumulator condition to not match."
  []
  (assoc (count) :convert-return-fn (fn [v]
                                      ;; This specifically needs to return nil rather than false if the pos? predicate is false so that
                                      ;; the accumulator condition will fail to match; the accumulator will consider
                                      ;; boolean false a valid match.  See https://github.com/cerner/clara-rules/issues/182#issuecomment-217142418
                                      ;; and the following comments for the original discussion around suppressing nil accumulator
                                      ;; return values but propagating boolean false.
                                      (when (pos? v)
                                        true))))

(defn distinct
  "Returns an accumulator producing a distinct set of facts.
   If given a field, returns a distinct set of values for that field."
  ([] (distinct identity))
  ([field]
   (accum
    {:initial-value {}
     :reduce-fn (fn [freq-map value] (update freq-map (field value) (fnil inc 0)))
     :retract-fn (fn [freq-map retracted-item]
                   (let [item-field (field retracted-item)
                         current (get freq-map item-field)]
                     (if (= 1 current)
                       (dissoc freq-map item-field)
                       (update freq-map item-field dec))))
     :convert-return-fn (comp set keys)})))

(defn all
  "Returns an accumulator that preserves all accumulated items.
   If given a field, returns all values in that field."
  ([]
   (accum
    {:initial-value []
     :reduce-fn (fn [items value] (conj items value))
     :retract-fn (fn [items retracted] (drop-one-of items retracted))}))
  ([field]
   (accum
    {:initial-value []
     :reduce-fn (fn [items value] (conj items (field value)))
     :retract-fn (fn [items retracted] (drop-one-of items (field retracted)))})))

;; The sorting accumulators below keep their state in the sorted bag and the sorted map from
;; clara.rules.accumulators.gb-tree, not in Clojure sorted collections.
;;
;; A Clojure sorted collection holds its comparator, and a comparator is code. Accumulator
;; state goes into working memory, and working memory must serialize. A var or a named fn
;; serializes only by name, and an anonymous fn does not serialize at all. The earlier
;; accumulators kept unsorted data in memory and sorted it only in convert-return-fn.
;;
;; The gb-tree collections hold data only. Each operation takes the comparator as an
;; argument, so the comparator stays in the accumulator functions, which Clara builds again
;; from the rules. The state stays sorted in memory, and it serializes as plain data.
;;
;; The state is a bag, not a set, because facts with equal sort keys must all stay. A
;; retraction removes the fact that is = to the retracted fact. sorted-grouping-by returns a
;; sorted map view, which holds the group comparator and serializes as an ordinary map.
(defn sorting-by
  "Return a generic sorting accumulator. Behaves like clojure.core/sort-by.
  * `field` - required - The field of a fact to sort by.
  * `comparator` - optional - The comparator for sort by, defaults to `clojure.core/compare`.
  * `convert-return-fn` - optional - Converts the resulting sorted data. Defaults to clojure.core/identity."
  [field & {:keys [comparator
                   convert-return-fn]
            :or {comparator compare
                 convert-return-fn identity}}]
  {:pre [(ifn? convert-return-fn)]}
  (let [cmp #(comparator (field %1) (field %2))]
    (accum
     {:reduce-fn #(gb-tree/insert cmp %1 %2)
      :combine-fn #(gb-tree/merge-bags cmp %1 %2)
      :initial-value gb-tree/empty-bag
      :retract-fn #(gb-tree/remove-item cmp %1 %2)
      :convert-return-fn (comp convert-return-fn gb-tree/bag-vec)})))

(defn sorted-grouping-by
  "Return a generic sorted grouping accumulator. Behaves like clojure.core/group-by into a map
  as if created by `clojure.core/sorted-map-by`, and each group of values is sorted as if by `clojure.core/sort-by`.
  * `group-field` - required - The field of a fact to group facts by.
  * `sort-field` - required - The field of a fact to sort facts by.
  * `group-comparator` - optional - The comparator to compare sorted groups, defaults to `clojure.core/compare`.
  * `sort-comparator` - optional - The comparator to compare sorted values, defaults to `clojure.core/compare`.
  * `convert-return-fn` - optional - Converts the resulting grouped data. Defaults to clojure.core/identity."
  [group-field sort-field & {:keys [group-comparator
                                    sort-comparator
                                    convert-return-fn]
                             :or {group-comparator compare
                                  sort-comparator compare
                                  convert-return-fn identity}}]
  {:pre [(ifn? convert-return-fn)]}
  ;; group-comparator can be a var, and a var is not a java.util.Comparator.
  (let [gcmp (fn [a b] (group-comparator a b))
        scmp #(sort-comparator (sort-field %1) (sort-field %2))]
    ;; The map and the bags in memory hold no comparator, so they serialize as data. Only
    ;; the returned view holds gcmp, and it serializes as an ordinary map.
    (accum
     {:reduce-fn (fn [accum fact]
                   (let [gf (group-field fact)
                         g (gb-tree/map-get gcmp accum gf gb-tree/empty-bag)]
                     (gb-tree/map-assoc gcmp accum gf (gb-tree/insert scmp g fact))))
      :combine-fn (fn [a b]
                    (gb-tree/map-merge-with gcmp #(gb-tree/merge-bags scmp %1 %2) a b))
      :initial-value gb-tree/empty-map
      :retract-fn (fn [accum fact]
                    (let [gf (group-field fact)]
                      (if-let [g (gb-tree/map-get gcmp accum gf)]
                        (let [g (gb-tree/remove-item scmp g fact)]
                          (if (pos? (gb-tree/bag-count g))
                            (gb-tree/map-assoc gcmp accum gf g)
                            (gb-tree/map-dissoc gcmp accum gf)))
                        accum)))
      :convert-return-fn (comp convert-return-fn
                               (fn [accum]
                                 (gb-tree/sorted-map-view
                                  gcmp
                                  (gb-tree/map-update-vals accum gb-tree/bag-vec))))})))
