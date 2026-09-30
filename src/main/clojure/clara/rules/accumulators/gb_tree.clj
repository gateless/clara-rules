(ns clara.rules.accumulators.gb-tree
  "A sorted bag (a multiset) and a sorted map on a general balanced tree.

   The scheme is from Andersson, \"General Balanced Trees\", J. Algorithms 30 (1999).
   Erlang's gb_trees uses the same scheme.

   A node stores no balance data. An insert that goes deeper than C * log2(n) walks back
   up. It rebuilds the lowest ancestor whose subtree is too tall for its size. A delete does
   not rebalance. The tree is rebuilt in full when the key count falls below half of the
   peak since the last full rebuild.

   In a bag, items that compare equal share one node. The node keeps every item verbatim,
   in insertion order. The tree balances on distinct keys, so such an item adds no depth.

   Neither collection holds a comparator or implements a Clojure interface. Each operation
   that compares takes the comparator as its first argument. So both collections are plain
   data, and they print and serialize without code.

   Bag API: `empty-bag`, `insert`, `remove-item`, `merge-bags`, `bag-subseq`, `bag-rsubseq`
   take the comparator. `bag-count`, `bag-seq`, `bag-rseq`, `bag-reduce`, `bag-vec`,
   `bag-groups`, `read-bag` do not.

   Map API: `map-assoc`, `map-dissoc`, `map-get`, `map-contains?`, `map-merge`,
   `map-merge-with` take the comparator. `empty-map`, `map-count`, `map-seq`, `map-rseq`,
   `map-reduce-kv`, `map-update-vals`, `map-pairs`, `read-map` do not.

   `sorted-map-view` puts a Clojure sorted map over a map and its comparator. The view
   prints as an ordinary map."
  (:import (clojure.lang AFn APersistentMap IPersistentMap LazilyPersistentVector MapEntry
                         MapEquivalence Murmur3 PersistentVector PersistentVector$Node RT Util)
           (java.lang.reflect Constructor)
           (java.util Arrays Collection Collections Comparator LinkedHashSet Map Map$Entry)))

(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)

;; Erlang uses 2. A smaller C gives shorter paths and more rebuilds.
(def ^:private ^:const C 2.0)

;; In a bag, k is the first item of a group, and more is nil or a vector of the later
;; items. In a map, k is the key and more is the value. The balancing code never looks
;; inside more.
(deftype Node [k more l r])

;; The items of the first group, then the items of the second, as the more of a node
;; whose k is the first item of the first group.
(defn- more-of [more1 k2 more2]
  (into (conj (or more1 []) k2) more2))

(defn- drop-nth [v ^long i]
  (when (> (count v) 1)
    (into (into [] (subvec v 0 i)) (subvec v (inc i)))))

(defn- limit ^double [^long keys]
  (* C (/ (Math/log keys) (Math/log 2.0))))

(defn- size ^long [node]
  (if (nil? node)
    0
    (let [^Node x node] (+ 1 (size (.-l x)) (size (.-r x))))))

;; ---------------------------------------------------------------------------------------
;; Rebuild

(defn- fill ^long [^objects a node ^long i]
  (if (nil? node)
    i
    (let [^Node x node
          i (fill a (.-l x) i)]
      (aset a i x)
      (fill a (.-r x) (inc i)))))

(defn- build [^objects a ^long lo ^long hi]
  (when (< lo hi)
    (let [m (unsigned-bit-shift-right (+ lo hi) 1)
          ^Node x (aget a m)]
      (Node. (.-k x) (.-more x) (build a lo m) (build a (inc m) hi)))))

(defn- rebuild [node ^long s]
  (let [a (object-array s)]
    (fill a node 0)
    (build a 0 s)))

(defn- nodes ^objects [root ^long n]
  (let [a (object-array n)]
    (fill a root 0)
    a))

;; ---------------------------------------------------------------------------------------
;; Insert and delete

;; ins adds the node k, more. When a node compares equal, (on-equal node k more) gives the
;; replacement, and ins keeps the children. st is [pending-height pending-size added?]. A
;; pending height above 0 means the new node is too deep and no ancestor has been rebuilt.
(defn- ins [^Comparator cmp node k more on-equal depth lim ^longs st]
  (if (nil? node)
    (do (aset st 2 1)
        (when (> (long depth) (double lim)) (aset st 0 1) (aset st 1 1))
        (Node. k more nil nil))
    (let [^Node x node
          c (.compare cmp k (.-k x))]
      (if (zero? c)
        (let [^Node y (on-equal x k more)]
          (Node. (.-k y) (.-more y) (.-l x) (.-r x)))
        (let [left? (neg? c)
              child (ins cmp (if left? (.-l x) (.-r x)) k more on-equal (inc (long depth)) lim st)
              y (if left?
                  (Node. (.-k x) (.-more x) child (.-r x))
                  (Node. (.-k x) (.-more x) (.-l x) child))
              h (aget st 0)]
          (if (zero? h)
            y
            ;; The root always passes this test, because the path went deeper than lim.
            (let [h (inc h)
                  s (+ 1 (aget st 1) (size (if left? (.-r x) (.-l x))))]
              (if (> h (limit s))
                (do (aset st 0 0) (rebuild y s))
                (do (aset st 0 h) (aset st 1 s) y)))))))))

;; A combine function joins two nodes that compare equal. Its first node comes from the
;; earlier collection. These two turn it into an on-equal function for ins.
(defn- incoming-last [combine]
  (fn [x k more] (combine x (Node. k more nil nil))))

(defn- incoming-first [combine]
  (fn [x k more] (combine (Node. k more nil nil) x)))

(defn- join-groups [^Node a ^Node b]
  (Node. (.-k a) (more-of (.-more a) (.-k b) (.-more b)) nil nil))

(def ^:private append-group (incoming-last join-groups))

(defn- remove-min [^Node x]
  (if-let [l (.-l x)]
    (Node. (.-k x) (.-more x) (remove-min l) (.-r x))
    (.-r x)))

(defn- join [l r]
  (cond (nil? l) r
        (nil? r) l
        :else (let [^Node m (loop [^Node m r] (if-let [ml (.-l m)] (recur ml) m))]
                (Node. (.-k m) (.-more m) l (remove-min r)))))

;; Removes the newest item that is = to item. Gives back the identical node when there is
;; none. Sets st[0] when a whole node goes.
(defn- del [^Comparator cmp node item ^longs st]
  (when node
    (let [^Node x node
          c (.compare cmp item (.-k x))
          more (.-more x)]
      (cond
        (neg? c) (let [l (del cmp (.-l x) item st)]
                   (if (identical? l (.-l x)) x (Node. (.-k x) more l (.-r x))))
        (pos? c) (let [r (del cmp (.-r x) item st)]
                   (if (identical? r (.-r x)) x (Node. (.-k x) more (.-l x) r)))
        :else (let [^java.util.List v (or more [])
                    i (.lastIndexOf v item)]
                (cond
                  (>= i 0) (Node. (.-k x) (drop-nth more i) (.-l x) (.-r x))
                  (not= item (.-k x)) x
                  (nil? more) (do (aset st 0 1) (join (.-l x) (.-r x)))
                  :else (Node. (nth more 0) (drop-nth more 0) (.-l x) (.-r x))))))))

;; Removes the node whose key compares equal to k. Gives back the identical node when there
;; is none.
(defn- del-key [^Comparator cmp node k]
  (when node
    (let [^Node x node
          c (.compare cmp k (.-k x))]
      (cond
        (neg? c) (let [l (del-key cmp (.-l x) k)]
                   (if (identical? l (.-l x)) x (Node. (.-k x) (.-more x) l (.-r x))))
        (pos? c) (let [r (del-key cmp (.-r x) k)]
                   (if (identical? r (.-r x)) x (Node. (.-k x) (.-more x) (.-l x) r)))
        :else (join (.-l x) (.-r x))))))

(defn- find-node [^Comparator cmp node k]
  (loop [node node]
    (when node
      (let [^Node x node
            c (.compare cmp k (.-k x))]
        (cond (neg? c) (recur (.-l x))
              (pos? c) (recur (.-r x))
              :else x)))))

;; ---------------------------------------------------------------------------------------
;; Merge

(defn- merge-sorted [^Comparator cmp combine ^objects xs ^objects ys ^objects out]
  (let [nx (alength xs), ny (alength ys)]
    (loop [i 0, j 0, k 0]
      (cond
        (== i nx) (do (System/arraycopy ys j out k (- ny j)) (+ k (- ny j)))
        (== j ny) (do (System/arraycopy xs i out k (- nx i)) (+ k (- nx i)))
        :else (let [^Node x (aget xs i)
                    ^Node y (aget ys j)
                    c (.compare cmp (.-k x) (.-k y))]
                (cond
                  (neg? c) (do (aset out k x) (recur (inc i) j (inc k)))
                  (pos? c) (do (aset out k y) (recur i (inc j) (inc k)))
                  :else (do (aset out k (combine x y))
                            (recur (inc i) (inc j) (inc k)))))))))

;; Merges tree a with na keys and tree b with nb keys. combine joins two nodes that compare
;; equal, the node of a first. Returns [root nkeys peak].
(defn- merge-trees [cmp combine a-root na a-peak b-root nb b-peak]
  (let [na (long na), nb (long nb)
        a-small? (< na nb)
        nbig (if a-small? nb na)
        nsmall (if a-small? na nb)]
    ;; Both ways cost about one new node per unit below. Inserts copy a path of about
    ;; log2(nbig) nodes for each key. A merge makes one node for each key of the result.
    (if (<= (* nsmall (/ (Math/log (max 2 nbig)) (Math/log 2.0))) (+ nbig nsmall))
      (let [^objects xs (if a-small? (nodes a-root na) (nodes b-root nb))
            on-equal (if a-small? (incoming-first combine) (incoming-last combine))]
        (loop [i 0
               r (if a-small? b-root a-root)
               n nbig
               peak (long (if a-small? b-peak a-peak))]
          (if (== i nsmall)
            [r n peak]
            (let [^Node x (aget xs i)
                  st (long-array 3)
                  r (ins cmp r (.-k x) (.-more x) on-equal 1 (limit (inc n)) st)
                  n (+ n (aget st 2))]
              (recur (inc i) r n (max peak n))))))
      (let [out (object-array (+ na nb))
            k (long (merge-sorted cmp combine (nodes a-root na) (nodes b-root nb) out))]
        [(build out 0 k) k k]))))

;; ---------------------------------------------------------------------------------------
;; Traversal

(defn- spine [node stack asc?]
  (if (nil? node)
    stack
    (let [^Node x node]
      (recur (if asc? (.-l x) (.-r x)) (cons x stack) asc?))))

(defn- spine-from [^Comparator cmp node k asc? stack]
  (if (nil? node)
    stack
    (let [^Node x node
          c (.compare cmp k (.-k x))]
      (if asc?
        (if (<= c 0)
          (recur cmp (.-l x) k asc? (cons x stack))
          (recur cmp (.-r x) k asc? stack))
        (if (>= c 0)
          (recur cmp (.-r x) k asc? (cons x stack))
          (recur cmp (.-l x) k asc? stack))))))

(defn- stack-seq [stack asc?]
  (when stack
    (lazy-seq
     (let [^Node x (first stack)
           tail (stack-seq (spine (if asc? (.-r x) (.-l x)) (next stack) asc?) asc?)
           more (.-more x)]
       (cond (nil? more) (cons (.-k x) tail)
             asc? (cons (.-k x) (concat more tail))
             :else (concat (rseq more) (cons (.-k x) tail)))))))

(defn- entry-seq [stack asc?]
  (when stack
    (lazy-seq
     (let [^Node x (first stack)]
       (cons (MapEntry/create (.-k x) (.-more x))
             (entry-seq (spine (if asc? (.-r x) (.-l x)) (next stack) asc?) asc?))))))

(defn- reduce-node [f acc node]
  (if (nil? node)
    acc
    (let [^Node x node
          acc (reduce-node f acc (.-l x))]
      (if (reduced? acc)
        acc
        (let [more (.-more x)
              n (count more)
              acc (loop [i 0, acc (f acc (.-k x))]
                    (if (or (== i n) (reduced? acc)) acc (recur (inc i) (f acc (nth more i)))))]
          (if (reduced? acc) acc (recur f acc (.-r x))))))))

(defn- reduce-kv-node [f acc node]
  (if (nil? node)
    acc
    (let [^Node x node
          acc (reduce-kv-node f acc (.-l x))]
      (if (reduced? acc)
        acc
        (let [acc (f acc (.-k x) (.-more x))]
          (if (reduced? acc) acc (recur f acc (.-r x))))))))

;; ---------------------------------------------------------------------------------------
;; The bag

;; The bag holds data only. cnt counts items. nkeys counts nodes. peak is the largest nkeys
;; since the last full rebuild.
(deftype GBBag [root ^long cnt ^long nkeys ^long peak]
  Object
  (equals [_ o]
    (and (instance? GBBag o)
         (== cnt (.-cnt ^GBBag o))
         (Util/equiv (stack-seq (spine root nil true) true)
                     (stack-seq (spine (.-root ^GBBag o) nil true) true))))
  (hashCode [_]
    (Murmur3/hashOrdered (or (stack-seq (spine root nil true) true) ())))
  (toString [this] (RT/printString this)))

(def empty-bag
  "The bag with no items."
  (GBBag. nil 0 0 0))

(defn bag-count
  "Returns the number of items in the bag."
  ^long [^GBBag b]
  (.-cnt b))

(defn bag-seq
  "Returns the items in order, or nil when the bag is empty."
  [^GBBag b]
  (stack-seq (spine (.-root b) nil true) true))

(defn bag-rseq
  "Returns the items in reverse order, or nil when the bag is empty."
  [^GBBag b]
  (stack-seq (spine (.-root b) nil false) false))

(defn bag-reduce
  "Like `reduce` with an initial value. It stops early on `reduced`."
  [f init ^GBBag b]
  (let [r (reduce-node f init (.-root b))]
    (if (reduced? r) @r r)))

(defn bag-groups
  "Returns the items as a vector of groups, in order. The items in a group compare equal,
   and they keep insertion order. `read-bag` makes the bag again from this vector."
  [^GBBag b]
  (mapv (fn [^Node x] (into [(.-k x)] (.-more x))) (nodes (.-root b) (.-nkeys b))))

(defn read-bag
  "Returns a bag from a vector of groups, as `bag-groups` returns. It needs no comparator,
   because the groups are already in order. It is also the data reader for
   #clara.rules/sorted-bag. Register it in data_readers.clj or in *data-readers*."
  [groups]
  (let [gs (vec groups)
        n (count gs)
        a (object-array n)]
    (dotimes [i n]
      (let [g (nth gs i)]
        (aset a i (Node. (first g) (when (next g) (vec (rest g))) nil nil))))
    (GBBag. (build a 0 n) (reduce (fn [^long t g] (+ t (count g))) 0 gs) n n)))

(defmethod print-method GBBag [b ^java.io.Writer w]
  (.write w "#clara.rules/sorted-bag ")
  (print-method (bag-groups b) w))

;; The functions below take the comparator cmp. It must be the comparator that built the
;; collection. Another comparator breaks the order, and nothing detects that.

(defn insert
  "Adds x to the bag. Items that compare equal to x keep their place before x."
  [cmp ^GBBag b x]
  (let [st (long-array 3)
        r (ins cmp (.-root b) x nil append-group 1 (limit (inc (.-nkeys b))) st)
        nk (+ (.-nkeys b) (aget st 2))]
    (GBBag. r (inc (.-cnt b)) nk (max (.-peak b) nk))))

(defn remove-item
  "Removes one item that is = to x. It looks among the items that compare equal to x, and
   removes the newest one that is = to x. Returns the same bag when there is none."
  [cmp ^GBBag b x]
  (let [st (long-array 1)
        r (del cmp (.-root b) x st)
        cnt (dec (.-cnt b))]
    (cond
      (identical? r (.-root b)) b
      (zero? (aget st 0)) (GBBag. r cnt (.-nkeys b) (.-peak b))
      :else (let [nk (dec (.-nkeys b))]
              (if (< (* 2 nk) (.-peak b))
                (GBBag. (rebuild r nk) cnt nk nk)
                (GBBag. r cnt nk (.-peak b)))))))

(defn merge-bags
  "Returns a bag that holds every item of a and every item of b. Where items of a and b
   compare equal, the items of a come first."
  [cmp ^GBBag a ^GBBag b]
  (let [[r n peak] (merge-trees cmp join-groups
                                (.-root a) (.-nkeys a) (.-peak a)
                                (.-root b) (.-nkeys b) (.-peak b))]
    (GBBag. r (+ (.-cnt a) (.-cnt b)) (long n) (long peak))))

;; clojure.core/subseq skips only one element on an exclusive bound, because a sorted set
;; holds each key once. These two skip every copy.

(defn- bound [^Comparator cmp test key]
  (fn [x] (test (.compare cmp x key) 0)))

(defn bag-subseq
  "Like `subseq`. test is one of <, <=, > or >=."
  ([cmp ^GBBag b test key]
   (let [in? (bound cmp test key)]
     (if (#{> >=} test)
       (drop-while (complement in?) (stack-seq (spine-from cmp (.-root b) key true nil) true))
       (take-while in? (bag-seq b)))))
  ([cmp b start-test start-key end-test end-key]
   (take-while (bound cmp end-test end-key) (bag-subseq cmp b start-test start-key))))

(defn bag-rsubseq
  "Like `rsubseq`. test is one of <, <=, > or >=."
  ([cmp ^GBBag b test key]
   (let [in? (bound cmp test key)]
     (if (#{< <=} test)
       (drop-while (complement in?) (stack-seq (spine-from cmp (.-root b) key false nil) false))
       (take-while in? (bag-rseq b)))))
  ([cmp b start-test start-key end-test end-key]
   (take-while (bound cmp start-test start-key) (bag-rsubseq cmp b end-test end-key))))

;; ---------------------------------------------------------------------------------------
;; The map

;; The map holds data only, like the bag. cnt counts keys. peak is the largest cnt since
;; the last full rebuild.
(deftype GBMap [root ^long cnt ^long peak]
  Object
  (equals [_ o]
    (and (instance? GBMap o)
         (== cnt (.-cnt ^GBMap o))
         (Util/equiv (entry-seq (spine root nil true) true)
                     (entry-seq (spine (.-root ^GBMap o) nil true) true))))
  (hashCode [_]
    (Murmur3/hashOrdered (or (entry-seq (spine root nil true) true) ())))
  (toString [this] (RT/printString this)))

(def empty-map
  "The map with no keys."
  (GBMap. nil 0 0))

(defn map-count
  "Returns the number of keys in the map."
  ^long [^GBMap m]
  (.-cnt m))

(defn map-seq
  "Returns the map entries in key order, or nil when the map is empty."
  [^GBMap m]
  (entry-seq (spine (.-root m) nil true) true))

(defn map-rseq
  "Returns the map entries in reverse key order, or nil when the map is empty."
  [^GBMap m]
  (entry-seq (spine (.-root m) nil false) false))

(defn map-reduce-kv
  "Like `reduce-kv`, in key order. It stops early on `reduced`."
  [f init ^GBMap m]
  (let [r (reduce-kv-node f init (.-root m))]
    (if (reduced? r) @r r)))

(defn- update-node-vals [node f]
  (when node
    (let [^Node x node]
      (Node. (.-k x) (f (.-more x)) (update-node-vals (.-l x) f) (update-node-vals (.-r x) f)))))

(defn map-update-vals
  "Returns the map with f applied to every value. The keys and the tree shape stay."
  [^GBMap m f]
  (GBMap. (update-node-vals (.-root m) f) (.-cnt m) (.-peak m)))

(defn map-pairs
  "Returns the entries as a vector of [k v] pairs, in key order. `read-map` makes the map
   again from this vector."
  [^GBMap m]
  (mapv (fn [^Node x] [(.-k x) (.-more x)]) (nodes (.-root m) (.-cnt m))))

(defn read-map
  "Returns a map from [k v] pairs in key order, with each key once, as `map-pairs` returns.
   It needs no comparator. It is also the data reader for #clara.rules/sorted-map."
  [pairs]
  (let [ps (vec pairs)
        n (count ps)
        a (object-array n)]
    (dotimes [i n]
      (let [p (nth ps i)]
        (aset a i (Node. (nth p 0) (nth p 1) nil nil))))
    (GBMap. (build a 0 n) n n)))

(defmethod print-method GBMap [m ^java.io.Writer w]
  (.write w "#clara.rules/sorted-map ")
  (print-method (map-pairs m) w))

;; Like assoc on a Clojure map, a new value keeps the key object already in the map.
(def ^:private replace-value
  (incoming-last (fn [^Node x ^Node y] (Node. (.-k x) (.-more y) nil nil))))

(defn map-assoc
  "Returns the map with k mapped to v."
  [cmp ^GBMap m k v]
  (let [st (long-array 3)
        r (ins cmp (.-root m) k v replace-value 1 (limit (inc (.-cnt m))) st)
        n (+ (.-cnt m) (aget st 2))]
    (GBMap. r n (max (.-peak m) n))))

(defn map-dissoc
  "Returns the map without k. Returns the same map when k is absent."
  [cmp ^GBMap m k]
  (let [r (del-key cmp (.-root m) k)]
    (if (identical? r (.-root m))
      m
      (let [n (dec (.-cnt m))]
        (if (< (* 2 n) (.-peak m))
          (GBMap. (rebuild r n) n n)
          (GBMap. r n (.-peak m)))))))

(defn map-get
  "Returns the value of k, or not-found when k is absent."
  ([cmp m k] (map-get cmp m k nil))
  ([cmp ^GBMap m k not-found]
   (if-let [^Node x (find-node cmp (.-root m) k)]
     (.-more x)
     not-found)))

(defn map-contains?
  "Returns true when the map has k."
  [cmp ^GBMap m k]
  (some? (find-node cmp (.-root m) k)))

(defn map-merge-with
  "Like `merge-with` for two maps. (f value-in-a value-in-b) gives the value of a key that
   is in both maps. The key object comes from a."
  [cmp f ^GBMap a ^GBMap b]
  (let [combine (fn [^Node x ^Node y] (Node. (.-k x) (f (.-more x) (.-more y)) nil nil))
        [r n peak] (merge-trees cmp combine
                                (.-root a) (.-cnt a) (.-peak a)
                                (.-root b) (.-cnt b) (.-peak b))]
    (GBMap. r (long n) (long peak))))

(defn map-merge
  "Like `merge` for two maps. Where both maps have a key, the value of b wins."
  [cmp a b]
  (map-merge-with cmp (fn [_ v] v) a b))

;; ---------------------------------------------------------------------------------------
;; Sorted map view

;; A Clojure sorted map over a GBMap and its comparator. It prints as an ordinary map. It
;; implements MapEquivalence and java.util.Map, so = works both ways with other maps.
(deftype SortedMapView [^Comparator cmp ^GBMap m meta]
  IPersistentMap
  (assoc [_ k v] (SortedMapView. cmp (map-assoc cmp m k v) meta))
  (assocEx [this k v]
    (if (.containsKey this k)
      (throw (Util/runtimeException "Key already present"))
      (.assoc this k v)))
  (without [_ k] (SortedMapView. cmp (map-dissoc cmp m k) meta))
  (containsKey [_ k] (some? (find-node cmp (.-root m) k)))
  (entryAt [_ k]
    (when-let [^Node x (find-node cmp (.-root m) k)]
      (MapEntry/create (.-k x) (.-more x))))
  (count [_] (.-cnt m))
  (cons [this o]
    (cond
      (instance? Map$Entry o) (.assoc this (.getKey ^Map$Entry o) (.getValue ^Map$Entry o))
      (vector? o) (if (== 2 (count o))
                    (.assoc this (nth o 0) (nth o 1))
                    (throw (IllegalArgumentException. "Vector arg to map conj must be a pair")))
      :else (reduce (fn [^IPersistentMap acc e] (.cons acc e)) this (seq o))))
  (empty [_] (SortedMapView. cmp empty-map meta))
  (equiv [this o]
    (cond
      (not (instance? Map o)) false
      (and (instance? IPersistentMap o) (not (instance? MapEquivalence o))) false
      :else (let [^Map o o]
              (and (== (.-cnt m) (.size o))
                   (every? (fn [^Map$Entry e]
                             (and (.containsKey o (.getKey e))
                                  (Util/equiv (.getValue e) (.get o (.getKey e)))))
                           (map-seq m))))))
  (seq [_] (map-seq m))
  (valAt [this k] (.valAt this k nil))
  (valAt [_ k not-found] (map-get cmp m k not-found))
  (iterator [_] (let [^Iterable s (or (map-seq m) ())] (.iterator s)))

  MapEquivalence

  clojure.lang.Sorted
  (comparator [_] cmp)
  (entryKey [_ e] (key e))
  (seq [_ asc?] (entry-seq (spine (.-root m) nil asc?) asc?))
  (seqFrom [_ k asc?] (entry-seq (spine-from cmp (.-root m) k asc? nil) asc?))

  clojure.lang.Reversible
  (rseq [_] (map-rseq m))

  clojure.lang.IKVReduce
  (kvreduce [_ f init] (map-reduce-kv f init m))

  clojure.lang.IFn
  (invoke [this k] (.valAt this k nil))
  (invoke [this k not-found] (.valAt this k not-found))
  (applyTo [this args] (AFn/applyToHelper this args))

  clojure.lang.IHashEq
  (hasheq [this] (APersistentMap/mapHasheq this))

  clojure.lang.IObj
  (meta [_] meta)
  (withMeta [_ mt] (SortedMapView. cmp m mt))

  Map
  (size [_] (.-cnt m))
  (isEmpty [_] (zero? (.-cnt m)))
  (containsValue [_ v] (boolean (some #(Util/equiv v (val %)) (map-seq m))))
  (get [_ k] (map-get cmp m k nil))
  (put [_ _ _] (throw (UnsupportedOperationException.)))
  (remove [_ _] (throw (UnsupportedOperationException.)))
  (putAll [_ _] (throw (UnsupportedOperationException.)))
  (clear [_] (throw (UnsupportedOperationException.)))
  (keySet [_]
    (let [^Collection ks (or (keys (map-seq m)) ())]
      (Collections/unmodifiableSet (LinkedHashSet. ks))))
  (values [_] (Collections/unmodifiableCollection (vec (vals (map-seq m)))))
  (entrySet [_]
    (let [^Collection es (or (map-seq m) ())]
      (Collections/unmodifiableSet (LinkedHashSet. es))))

  Object
  (equals [this o] (APersistentMap/mapEquals this o))
  (hashCode [this] (APersistentMap/mapHash this))
  (toString [this] (RT/printString this)))

(defn sorted-map-view
  "Returns a Clojure sorted map over the map m. cmp must be the comparator that built m.
   The view prints as an ordinary map."
  [cmp m]
  (SortedMapView. cmp m nil))

;; ---------------------------------------------------------------------------------------
;; Vector

;; PersistentVector has no public constructor that takes a trie, so this one is opened by
;; reflection. It is nil if that fails, and bag-vec then falls back to createOwning.
(def ^:private ^Constructor pv-ctor
  (try
    (doto (.getDeclaredConstructor PersistentVector
                                   (into-array Class [Integer/TYPE Integer/TYPE
                                                      PersistentVector$Node
                                                      (class (object-array 0))]))
      (.setAccessible true))
    (catch Exception _ nil)))

(defn- fill-elems ^long [^objects a node ^long i]
  (if (nil? node)
    i
    (let [^Node x node
          i (fill-elems a (.-l x) i)
          more (.-more x)
          n (count more)]
      (aset a i (.-k x))
      (dotimes [t n] (aset a (+ i 1 t) (nth more t)))
      (fill-elems a (.-r x) (+ i 1 n)))))

(defn- branches ^objects [^objects kids]
  (let [n (alength kids)
        out (object-array (quot (+ n 31) 32))
        edit (.-edit PersistentVector/EMPTY_NODE)]
    (dotimes [i (alength out)]
      (let [arr (object-array 32)
            s (* 32 i)]
        (System/arraycopy kids s arr 0 (min 32 (- n s)))
        (aset out i (PersistentVector$Node. edit arr))))
    out))

(defn bag-vec
  "Returns the items of the bag as a vector, in order.

   `vec` does one transient conj per element. This builds the vector trie from an array
   instead. The trie has the layout that conj builds: full leaves of 32, packed to the
   left, then a tail of 1 to 32 elements."
  [^GBBag b]
  (let [n (.-cnt b)
        a (object-array n)]
    (fill-elems a (.-root b) 0)
    (if (or (<= n 32) (nil? pv-ctor))
      (LazilyPersistentVector/createOwning a)
      (let [tailoff (bit-and-not (dec n) 31)
            edit (.-edit PersistentVector/EMPTY_NODE)
            leaves (object-array (quot tailoff 32))]
        (dotimes [i (alength leaves)]
          (aset leaves i (PersistentVector$Node. edit (Arrays/copyOfRange a (int (* 32 i)) (int (* 32 (inc i)))))))
        (loop [kids (branches leaves), shift 5]
          (if (== 1 (alength kids))
            (.newInstance pv-ctor (object-array [(int n) (int shift) (aget kids 0)
                                                 (Arrays/copyOfRange a (int tailoff) (int n))]))
            (recur (branches kids) (+ shift 5))))))))
