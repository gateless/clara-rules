(ns clara.test-gb-tree
  (:require [clojure.test :refer [deftest is testing]]
            [clara.rules.accumulators.gb-tree :refer :all :as gb])
  (:import [clara.rules.accumulators.gb_tree Node GBBag GBMap]
           [clojure.lang RT]
           [java.util Random]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)

(def ^:private natural RT/DEFAULT_COMPARATOR)

(def ^:private descending #(compare %2 %1))

;; Items are [key tag]. Only the key takes part in the order.
(def ^:private by-first #(compare (first %1) (first %2)))

(defn- into-bag [cmp b xs]
  (reduce #(insert cmp %1 %2) b xs))

(defn- bag-of [cmp & xs]
  (into-bag cmp empty-bag xs))

(defn- height ^long [node]
  (if (nil? node)
    0
    (let [^Node x node] (inc (max (height (.-l x)) (height (.-r x)))))))

(defn- check-shape [^GBBag b]
  (is (== (.-nkeys b) (#'gb/size (.-root b))))
  (is (<= (.-nkeys b) (.-peak b)))
  (is (<= (height (.-root b)) (inc (long (#'gb/limit (max 2 (.-peak b)))))))
  (is (== (.-cnt b) (bag-reduce (fn [^long a _] (inc a)) 0 b))))

(deftest basics
  (let [b (bag-of natural 3 1 2 1 nil)]
    (is (= [nil 1 1 2 3] (bag-seq b)))
    (is (= [3 2 1 1 nil] (bag-rseq b)))
    (is (= 5 (bag-count b)))
    (is (nil? (bag-seq empty-bag)))
    (is (nil? (bag-rseq empty-bag)))
    (is (= 0 (bag-count empty-bag)))))

(deftest remove-item-test
  (let [b (bag-of natural 1 1 2)]
    (is (= [1 2] (bag-seq (remove-item natural b 1))))
    (is (= [1 1] (bag-seq (remove-item natural b 2))))
    (is (identical? b (remove-item natural b 5)))
    (is (identical? empty-bag (remove-item natural empty-bag 5)))
    (is (nil? (bag-seq (reduce #(remove-item natural %1 %2) b [1 1 2])))))
  (testing "items that compare equal stay verbatim, and only the newest = item goes"
    (let [b (bag-of by-first [1 :a] [2 :x] [1 :b] [1 :a] [1 :c])
          rm #(remove-item by-first %1 %2)]
      (is (= [[1 :a] [1 :b] [1 :a] [1 :c] [2 :x]] (bag-seq b)))
      (is (= [[2 :x] [1 :c] [1 :a] [1 :b] [1 :a]] (bag-rseq b)))
      (is (= [[1 :a] [1 :b] [1 :c] [2 :x]] (bag-seq (rm b [1 :a]))))
      (is (= [[1 :b] [1 :c] [2 :x]] (bag-seq (-> b (rm [1 :a]) (rm [1 :a])))))
      (is (= [[1 :a] [1 :a] [1 :c] [2 :x]] (bag-seq (rm b [1 :b]))))
      (is (= [[1 :a] [1 :b] [1 :a] [2 :x]] (bag-seq (rm b [1 :c]))))
      (is (identical? b (rm b [1 :z])))
      (is (identical? b (rm b [3 :a])))
      (is (= 4 (bag-count (rm b [1 :a]))))
      (is (= [[2 :x]] (bag-seq (reduce rm b [[1 :a] [1 :b] [1 :a] [1 :c]])))))))

(deftest comparators
  (is (= [3 2 2 1] (bag-seq (bag-of descending 1 2 3 2))))
  (testing "items that compare equal all stay, in insertion order"
    (is (= ["b" "B" "a"] (bag-seq (bag-of #(compare (.toLowerCase ^String %2)
                                                    (.toLowerCase ^String %1))
                                          "a" "b" "B"))))))

(deftest ranges
  (let [b (bag-of natural 5 1 3 3 7 9 3)
        sub (partial bag-subseq natural b)
        rsub (partial bag-rsubseq natural b)]
    (is (= [3 3 3 5] (sub >= 2 < 7)))
    (is (= [3 3 3 5] (sub >= 3 <= 5)))
    (is (= [5 7 9] (sub > 3)))
    (is (= [1 3 3 3] (sub < 5)))
    (is (= [3 3 3 1] (rsub <= 4)))
    (is (= [1] (rsub < 3)))
    (is (= [5 3 3 3] (rsub > 1 < 7)))
    (is (= [9 7] (rsub > 5)))
    (is (empty? (sub > 9)))
    (is (empty? (rsub < 1)))
    (testing "matches a filter over the whole seq for every bound"
      (doseq [k (range 0 11), t [< <= > >=]]
        (is (= (filter #(t % k) (bag-seq b)) (sub t k)))
        (is (= (filter #(t % k) (bag-rseq b)) (rsub t k)))))))

(deftest reducing
  (let [b (apply bag-of natural (range 10))]
    (is (= 45 (bag-reduce + 0 b)))
    (is (= 6 (bag-reduce (fn [^long a x] (if (> a 5) (reduced a) (+ a (long x)))) 0 b)))
    (is (= 0 (bag-reduce + 0 empty-bag)))))

(deftest equality
  (let [a (bag-of natural 1 2 2 3)
        b (bag-of natural 3 2 1 2)]
    (is (= a b))
    (is (= (hash a) (hash b)))
    (is (not= a (bag-of natural 1 2 3)))
    (is (not= a [1 2 2 3]))
    (is (= empty-bag (bag-of natural)))))

(deftest sorted-input-stays-shallow
  (doseq [xs [(range 65536) (range 65535 -1 -1)]]
    (let [b (into-bag natural empty-bag xs)]
      (is (= 65536 (bag-count b)))
      (is (<= (height (.-root ^GBBag b)) 33))
      (is (= (range 65536) (bag-seq b))))))

;; The reference is a sorted map from key to the vector of items, in insertion order.
(defn- expand [ref]
  (mapcat val ref))

(defn- ref-remove [ref [k :as item]]
  (let [v (get ref k [])
        i (.lastIndexOf ^java.util.List v item)]
    (cond (neg? i) ref
          (== 1 (count v)) (dissoc ref k)
          :else (assoc ref k (into (subvec v 0 i) (subvec v (inc i)))))))

(deftest differential
  (doseq [seed (range 8)
          :let [rnd (Random. seed)
                span (if (even? seed) 64 100000)]]
    (loop [i 0, total 0, b empty-bag, ref (sorted-map)]
      (when (zero? (rem i 997))
        (is (= (seq (expand ref)) (bag-seq b)) (str "seed " seed " step " i))
        (is (= (seq (reverse (expand ref))) (bag-rseq b)))
        (check-shape b))
      (when (< i 20000)
        (let [k (.nextInt rnd span)
              item [k (.nextInt rnd 3)]
              ;; Grow for the first half, then shrink, so the full rebuild runs.
              add? (< (.nextInt rnd 100) (if (< i 10000) 70 25))
              ref' (if add? (update ref k (fnil conj []) item) (ref-remove ref item))
              total' (long (cond add? (inc total) (identical? ref ref') total :else (dec total)))
              b' (if add? (insert by-first b item) (remove-item by-first b item))]
          (is (= total' (bag-count b')))
          (is (= (get ref' k []) (vec (bag-subseq by-first b' >= [k] <= [k]))))
          (recur (inc i) total' b' ref'))))))

(defn- random-bag [^Random rnd ^long n ^long span]
  (into-bag by-first empty-bag (repeatedly n #(vector (.nextInt rnd span) (.nextInt rnd 3)))))

(deftest merging
  (is (= (bag-of natural 1 2 2 2 3) (merge-bags natural (bag-of natural 1 2 2) (bag-of natural 2 3))))
  (is (= (bag-of natural 1 2) (merge-bags natural empty-bag (bag-of natural 1 2))))
  (is (= (bag-of natural 1 2) (merge-bags natural (bag-of natural 1 2) empty-bag)))
  (testing "similar sizes take the merge path and give a perfectly balanced tree"
    (let [rnd (Random. 42)
          ^GBBag m (merge-bags by-first (random-bag rnd 3000 100000) (random-bag rnd 2000 100000))
          k (.-nkeys m)]
      (is (== (height (.-root m)) (- 64 (Long/numberOfLeadingZeros k))))))
  (testing "both paths agree with inserting one bag into the other"
    (let [rnd (Random. 7)]
      (doseq [[na nb span] [[0 0 10] [1 1000 10] [1000 3 100000] [5 5 3]
                            [2000 2000 50] [3000 1500 100000] [40 4000 100000]]]
        (let [a (random-bag rnd na span)
              b (random-bag rnd nb span)
              m (merge-bags by-first a b)]
          (is (= (into-bag by-first a (bag-seq b)) m) (str [na nb span]))
          (is (= (+ (long na) (long nb)) (bag-count m)))
          (check-shape m)
          (is (= (bag-seq m)
                 (bag-seq (remove-item by-first (insert by-first m [-1 0]) [-1 0])))))))))

(deftest to-vector
  (let [rnd (Random. 3)]
    (doseq [n [0 1 31 32 33 63 64 65 1024 1056 1057 1088 32800 32801 40000]
            span [1000000000 7]
            :let [n (long n)]]
      (let [b (random-bag rnd n span)
            v (bag-vec b)
            expected (vec (bag-seq b))]
        (is (vector? v))
        (is (= expected v) (str [n span]))
        (is (= (hash expected) (hash v)))
        (is (= (conj expected :x) (conj v :x)))
        (when (pos? n)
          (is (= (assoc expected (quot n 2) :y) (assoc v (quot n 2) :y)))
          (is (= (subvec expected (quot n 3)) (subvec v (quot n 3))))
          (is (= (persistent! (conj! (transient expected) :z))
                 (persistent! (conj! (transient v) :z)))))
        (testing "pop walks the trie down to empty, so a wrong shape fails here"
          (is (loop [v v, e expected]
                (cond (empty? e) (empty? v)
                      (= (peek e) (peek v)) (recur (pop v) (pop e))
                      :else false))))))))

(defn- read-back [b]
  (binding [*data-readers* {'clara.rules/sorted-bag read-bag}]
    (read-string (pr-str b))))

(deftest printing-and-reading
  (let [b (bag-of by-first [1 :b] [0 :x] [1 :a] [1 :b])]
    (testing "the printed form is the groups, with no code"
      (is (= "#clara.rules/sorted-bag [[[0 :x]] [[1 :b] [1 :a] [1 :b]]]" (pr-str b)))
      (is (= "#clara.rules/sorted-bag []" (pr-str empty-bag))))
    (testing "a bag reads back equal, with the same groups, and stays usable"
      (doseq [x [empty-bag b (random-bag (Random. 11) 5000 700)]]
        (let [r (read-back x)]
          (is (= x r))
          (is (= (bag-groups x) (bag-groups r)))
          (check-shape r)
          (is (= (bag-seq (insert by-first x [1 :c])) (bag-seq (insert by-first r [1 :c]))))
          (is (= (bag-seq (remove-item by-first x [1 :b]))
                 (bag-seq (remove-item by-first r [1 :b])))))))
    (testing "read-bag takes any seqable of groups"
      (is (= b (read-bag (list '([0 :x]) '([1 :b] [1 :a] [1 :b]))))))))

;; ---------------------------------------------------------------------------------------
;; Map tests

(defn- map-of [cmp & kvs]
  (reduce (fn [m [k v]] (map-assoc cmp m k v)) empty-map (partition 2 kvs)))

(defn- check-map-shape [^GBMap m]
  (is (== (.-cnt m) (#'gb/size (.-root m))))
  (is (<= (.-cnt m) (.-peak m)))
  (is (<= (height (.-root m)) (inc (long (#'gb/limit (max 2 (.-peak m))))))))

(deftest map-basics
  (let [m (map-of natural 3 :c 1 :a 2 :b)]
    (is (= [[1 :a] [2 :b] [3 :c]] (map-seq m)))
    (is (= [[3 :c] [2 :b] [1 :a]] (map-rseq m)))
    (is (= 3 (map-count m)))
    (is (= :b (map-get natural m 2)))
    (is (nil? (map-get natural m 9)))
    (is (= :none (map-get natural m 9 :none)))
    (is (map-contains? natural m 1))
    (is (not (map-contains? natural m 9)))
    (is (= [[1 :a] [2 :z] [3 :c]] (map-seq (map-assoc natural m 2 :z))))
    (is (= 3 (map-count (map-assoc natural m 2 :z))))
    (is (= [[1 :a] [3 :c]] (map-seq (map-dissoc natural m 2))))
    (is (identical? m (map-dissoc natural m 9)))
    (is (identical? empty-map (map-dissoc natural empty-map 9)))
    (is (nil? (map-seq empty-map)))
    (is (nil? (map-rseq empty-map))))
  (testing "nil keys and nil values"
    (let [m (map-of natural nil 1 2 nil)]
      (is (= [[nil 1] [2 nil]] (map-seq m)))
      (is (map-contains? natural m 2))
      (is (nil? (map-get natural m 2 :none)))))
  (testing "a new value keeps the key object already in the map"
    (is (= [[[1 :a] :y]] (map-seq (map-of by-first [1 :a] :x [1 :b] :y)))))
  (testing "reduce-kv and update-vals"
    (is (= {1 2 3 4} (map-reduce-kv (fn [acc k v] (assoc acc k v)) {} (map-of natural 3 4 1 2))))
    (is (= 1 (map-reduce-kv (fn [_ k _] (reduced k)) nil (map-of natural 3 4 1 2))))
    (is (= [[1 "a"] [2 "b"]] (map-seq (map-update-vals (map-of natural 2 :b 1 :a) name))))))

(deftest map-differential
  (doseq [seed (range 6)
          :let [rnd (Random. seed)
                span (if (even? seed) 64 100000)]]
    (loop [i 0, m empty-map, ref (sorted-map)]
      (when (zero? (rem i 997))
        (is (= (seq ref) (map-seq m)) (str "seed " seed " step " i))
        (is (= (rseq ref) (map-rseq m)))
        (check-map-shape m))
      (when (< i 20000)
        (let [k (.nextInt rnd span)
              ;; Grow for the first half, then shrink, so the full rebuild runs.
              add? (< (.nextInt rnd 100) (if (< i 10000) 70 25))
              m' (if add? (map-assoc natural m k i) (map-dissoc natural m k))
              ref' (if add? (assoc ref k i) (dissoc ref k))]
          (is (= (count ref') (map-count m')))
          (is (= (get ref' k :none) (map-get natural m' k :none)))
          (recur (inc i) m' ref'))))))

(defn- random-map [^Random rnd ^long n ^long span]
  (reduce (fn [m _] (let [k (.nextInt rnd span)] (map-assoc natural m k [k (.nextInt rnd 1000)])))
          empty-map
          (range n)))

(deftest map-merging
  (testing "both paths agree with merge and merge-with on sorted maps"
    (let [rnd (Random. 5)]
      (doseq [[na nb span] [[0 0 10] [1 1000 2000] [1000 3 2000] [5 5 3]
                            [2000 2000 3000] [40 4000 100000]]]
        (let [a (random-map rnd na span)
              b (random-map rnd nb span)
              ra (into (sorted-map) (map-seq a))
              rb (into (sorted-map) (map-seq b))
              mw (map-merge-with natural vector a b)]
          (is (= (seq (merge ra rb)) (map-seq (map-merge natural a b))) (str [na nb span]))
          (is (= (seq (merge-with vector ra rb)) (map-seq mw)) (str [na nb span]))
          (check-map-shape mw))))))

(defn- read-back-map [x]
  (binding [*data-readers* {'clara.rules/sorted-map read-map
                            'clara.rules/sorted-bag read-bag}]
    (read-string (pr-str x))))

(deftest map-printing-and-reading
  (let [m (map-of natural 2 :b 1 [:a])]
    (is (= "#clara.rules/sorted-map [[1 [:a]] [2 :b]]" (pr-str m)))
    (is (= "#clara.rules/sorted-map []" (pr-str empty-map)))
    (is (= m (read-back-map m))))
  (testing "a map of bags reads back equal"
    (let [m (map-of natural :x (bag-of natural 2 1 2) :y (bag-of natural 3))]
      (is (= m (read-back-map m)))))
  (testing "a large map reads back equal and stays usable"
    (let [big (random-map (Random. 9) 3000 100000)
          r (read-back-map big)]
      (is (= big r))
      (check-map-shape r)
      (is (= (map-seq (map-assoc natural big 5 :x)) (map-seq (map-assoc natural r 5 :x))))
      (is (= (map-seq (map-dissoc natural big 5)) (map-seq (map-dissoc natural r 5)))))))

(deftest view
  (let [v (sorted-map-view natural (map-of natural 3 :c 1 :a 2 :b))
        ref (sorted-map 1 :a 2 :b 3 :c)]
    (testing "it equals other maps, both ways, with the same hash"
      (is (= ref v))
      (is (= v ref))
      (is (= {1 :a 2 :b 3 :c} v))
      (is (= v {1 :a 2 :b 3 :c}))
      (is (.equals ^Object v ref))
      (is (.equals ^Object ref v))
      (is (= (hash ref) (hash v)))
      (is (= (.hashCode ^Object ref) (.hashCode ^Object v)))
      (is (not= v {1 :a}))
      (is (not= v [[1 :a] [2 :b] [3 :c]])))
    (testing "it reads like a sorted map"
      (is (map? v))
      (is (sorted? v))
      (is (reversible? v))
      (is (= 3 (count v)))
      (is (= :b (get v 2) (v 2)))
      (is (= :none (get v 9 :none) (v 9 :none)))
      (is (contains? v 1))
      (is (not (contains? v 9)))
      (is (= [2 :b] (find v 2)))
      (is (nil? (find v 9)))
      (is (= [1 2 3] (keys v)))
      (is (= [:a :b :c] (vals v)))
      (is (= (seq ref) (seq v)))
      (is (= (rseq ref) (rseq v)))
      (is (= (subseq ref > 1) (subseq v > 1)))
      (is (= (rsubseq ref <= 2) (rsubseq v <= 2)))
      (is (= (subseq ref >= 2 < 3) (subseq v >= 2 < 3)))
      (is (= {1 :a 2 :b 3 :c} (reduce-kv assoc {} v)))
      (is (= :c (apply v [3])))
      (is (identical? natural (.comparator ^clojure.lang.Sorted v))))
    (testing "it writes like a sorted map"
      (is (= (assoc ref 0 :z) (assoc v 0 :z)))
      (is (= (dissoc ref 2) (dissoc v 2)))
      (is (= (conj ref [4 :d]) (conj v [4 :d])))
      (is (= (into ref {5 :e 0 :y}) (into v {5 :e 0 :y})))
      (is (= (merge ref {2 :q}) (merge v {2 :q})))
      (is (= [0 1 2 3] (keys (assoc v 0 :z))))
      (is (sorted? (assoc v 0 :z)))
      (is (= {} (empty v)))
      (is (sorted? (empty v)))
      (is (thrown? RuntimeException (.assocEx ^clojure.lang.IPersistentMap v 1 :x)))
      (is (= {:x 1} (meta (assoc (with-meta v {:x 1}) 0 :z)))))
    (testing "it prints and reads as an ordinary map"
      (is (= "{1 :a, 2 :b, 3 :c}" (pr-str v)))
      (is (= ref (read-string (pr-str v))))
      (is (not (sorted? (read-string (pr-str v))))))
    (testing "java.util.Map"
      (let [^java.util.Map jv v
            ^java.util.Map jref ref]
        (is (= 3 (.size jv)))
        (is (= :b (.get jv 2)))
        (is (.containsValue jv :c))
        (is (not (.containsValue jv :q)))
        (is (= (.keySet jref) (.keySet jv)))
        (is (= (.entrySet jref) (.entrySet jv)))
        (is (thrown? UnsupportedOperationException (.put jv 9 :x)))))
    (testing "a descending comparator"
      (let [d (sorted-map-view descending (map-of descending 1 :a 3 :c 2 :b))]
        (is (= [3 2 1] (keys d)))
        (is (= (sorted-map-by > 1 :a 2 :b 3 :c) d))
        (is (= [[2 :b] [1 :a]] (subseq d > 3)))))))
