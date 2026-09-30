(ns clara.rules.accumulators.wb-tree
  "A sorted bag (a multiset) and a sorted map on a weight-balanced tree.

   The tree is Adams' weight-balanced tree, with the parameters (3, 2) from Hirai and
   Yamamoto, \"Balancing weight-balanced trees\", J. Functional Programming 21 (2011). Each
   node stores the size of its subtree. Insert and delete rebalance on the way up, so every
   operation is O(log n) in the worst case. A merge splits and joins, in O(m log(n/m + 1)).

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

;; In a bag, k is the first item of a group, and more is nil or a vector of the later
;; items. In a map, k is the key and more is the value. The balancing code never looks
;; inside more. size counts the nodes in the subtree.
(deftype Node [k more l r ^long size])

(defn- size ^long [node]
  (if (nil? node) 0 (.-size ^Node node)))

(defn- mk [k more l r]
  (Node. k more l r (+ 1 (size l) (size r))))

;; The items of the first group, then the items of the second, as the more of a node
;; whose k is the first item of the first group.
(defn- more-of [more1 k2 more2]
  (into (conj (or more1 []) k2) more2))

(defn- drop-nth [v ^long i]
  (when (> (count v) 1)
    (into (into [] (subvec v 0 i)) (subvec v (inc i)))))

;; ---------------------------------------------------------------------------------------
;; Balance

;; The weight of a subtree is its size plus one. Hirai and Yamamoto show that (3, 2) is the
;; only integer pair for which one balance step restores the invariant after an insert or a
;; delete.
(def ^:private ^:const delta 3)
(def ^:private ^:const gamma 2)

;; True when b is not too heavy for a.
(defn- balanced? [a b]
  (<= (inc (size b)) (* delta (inc (size a)))))

;; True when a single rotation is enough, a being the inner and b the outer grandchild.
(defn- single? [a b]
  (< (inc (size a)) (* gamma (inc (size b)))))

(defn- rotate-l [k more l ^Node r]
  (let [rl (.-l r)
        rr (.-r r)]
    (if (single? rl rr)
      (mk (.-k r) (.-more r) (mk k more l rl) rr)
      (let [^Node x rl]
        (mk (.-k x) (.-more x) (mk k more l (.-l x)) (mk (.-k r) (.-more r) (.-r x) rr))))))

(defn- rotate-r [k more ^Node l r]
  (let [ll (.-l l)
        lr (.-r l)]
    (if (single? lr ll)
      (mk (.-k l) (.-more l) ll (mk k more lr r))
      (let [^Node x lr]
        (mk (.-k x) (.-more x) (mk (.-k l) (.-more l) ll (.-l x)) (mk k more (.-r x) r))))))

;; Makes a node from subtrees whose weights are at most one step out of balance.
(defn- balance [k more l r]
  (cond (not (balanced? l r)) (rotate-l k more l r)
        (not (balanced? r l)) (rotate-r k more l r)
        :else (mk k more l r)))

(defn- insert-min [k more node]
  (if (nil? node)
    (mk k more nil nil)
    (let [^Node x node]
      (balance (.-k x) (.-more x) (insert-min k more (.-l x)) (.-r x)))))

(defn- insert-max [k more node]
  (if (nil? node)
    (mk k more nil nil)
    (let [^Node x node]
      (balance (.-k x) (.-more x) (.-l x) (insert-max k more (.-r x))))))

;; Joins l, the node k, more, and r, where every key of l is below k and every key of r is
;; above k. The two subtrees can have any sizes.
(defn- link [k more l r]
  (cond
    (nil? l) (insert-min k more r)
    (nil? r) (insert-max k more l)
    (not (balanced? l r)) (let [^Node y r]
                            (balance (.-k y) (.-more y) (link k more l (.-l y)) (.-r y)))
    (not (balanced? r l)) (let [^Node x l]
                            (balance (.-k x) (.-more x) (.-l x) (link k more (.-r x) r)))
    :else (mk k more l r)))

(defn- delete-min [^Node x]
  (if-let [l (.-l x)]
    (balance (.-k x) (.-more x) (delete-min l) (.-r x))
    (.-r x)))

(defn- delete-max [^Node x]
  (if-let [r (.-r x)]
    (balance (.-k x) (.-more x) (.-l x) (delete-max r))
    (.-l x)))

;; Joins two siblings that are in balance with each other, after their parent goes.
(defn- glue [l r]
  (cond
    (nil? l) r
    (nil? r) l
    (> (size l) (size r)) (let [^Node m (loop [^Node m l] (if-let [mr (.-r m)] (recur mr) m))]
                            (balance (.-k m) (.-more m) (delete-max l) r))
    :else (let [^Node m (loop [^Node m r] (if-let [ml (.-l m)] (recur ml) m))]
            (balance (.-k m) (.-more m) l (delete-min r)))))

;; ---------------------------------------------------------------------------------------
;; Build

(defn- fill ^long [^objects a node ^long i]
  (if (nil? node)
    i
    (let [^Node x node
          i (fill a (.-l x) i)]
      (aset a i x)
      (fill a (.-r x) (inc i)))))

(defn- nodes ^objects [root]
  (let [a (object-array (size root))]
    (fill a root 0)
    a))

;; Builds a perfectly balanced tree from nodes in key order. It reads only k and more.
(defn- build [^objects a ^long lo ^long hi]
  (when (< lo hi)
    (let [m (unsigned-bit-shift-right (+ lo hi) 1)
          ^Node x (aget a m)]
      (mk (.-k x) (.-more x) (build a lo m) (build a (inc m) hi)))))

;; ---------------------------------------------------------------------------------------
;; Insert, delete, find, merge

;; ins adds the node k, more. When a node compares equal, (on-equal node k more) gives the
;; replacement, and ins keeps the children.
(defn- ins [^Comparator cmp node k more on-equal]
  (if (nil? node)
    (mk k more nil nil)
    (let [^Node x node
          c (.compare cmp k (.-k x))]
      (cond
        (neg? c) (balance (.-k x) (.-more x) (ins cmp (.-l x) k more on-equal) (.-r x))
        (pos? c) (balance (.-k x) (.-more x) (.-l x) (ins cmp (.-r x) k more on-equal))
        :else (let [^Node y (on-equal x k more)]
                (Node. (.-k y) (.-more y) (.-l x) (.-r x) (.-size x)))))))

;; A combine function joins two nodes that compare equal. Its first node comes from the
;; earlier collection.
(defn- incoming-last [combine]
  (fn [x k more] (combine x (mk k more nil nil))))

(defn- join-groups [^Node a ^Node b]
  (mk (.-k a) (more-of (.-more a) (.-k b) (.-more b)) nil nil))

(def ^:private append-group (incoming-last join-groups))

;; Removes the newest item that is = to item. Gives back the identical node when there is
;; none.
(defn- del [^Comparator cmp node item]
  (when node
    (let [^Node x node
          c (.compare cmp item (.-k x))
          more (.-more x)]
      (cond
        (neg? c) (let [l (del cmp (.-l x) item)]
                   (if (identical? l (.-l x)) x (balance (.-k x) more l (.-r x))))
        (pos? c) (let [r (del cmp (.-r x) item)]
                   (if (identical? r (.-r x)) x (balance (.-k x) more (.-l x) r)))
        :else (let [^java.util.List v (or more [])
                    i (.lastIndexOf v item)]
                (cond
                  (>= i 0) (Node. (.-k x) (drop-nth more i) (.-l x) (.-r x) (.-size x))
                  (not= item (.-k x)) x
                  (nil? more) (glue (.-l x) (.-r x))
                  :else (Node. (nth more 0) (drop-nth more 0) (.-l x) (.-r x) (.-size x))))))))

;; Removes the node whose key compares equal to k. Gives back the identical node when there
;; is none.
(defn- del-key [^Comparator cmp node k]
  (when node
    (let [^Node x node
          c (.compare cmp k (.-k x))]
      (cond
        (neg? c) (let [l (del-key cmp (.-l x) k)]
                   (if (identical? l (.-l x)) x (balance (.-k x) (.-more x) l (.-r x))))
        (pos? c) (let [r (del-key cmp (.-r x) k)]
                   (if (identical? r (.-r x)) x (balance (.-k x) (.-more x) (.-l x) r)))
        :else (glue (.-l x) (.-r x))))))

(defn- find-node [^Comparator cmp node k]
  (loop [node node]
    (when node
      (let [^Node x node
            c (.compare cmp k (.-k x))]
        (cond (neg? c) (recur (.-l x))
              (pos? c) (recur (.-r x))
              :else x)))))

;; Returns [l x r]: the nodes below k, the node that compares equal to k or nil, and the
;; nodes above k.
(defn- split [^Comparator cmp node k]
  (if (nil? node)
    [nil nil nil]
    (let [^Node x node
          c (.compare cmp k (.-k x))]
      (cond
        (neg? c) (let [[ll m lr] (split cmp (.-l x) k)]
                   [ll m (link (.-k x) (.-more x) lr (.-r x))])
        (pos? c) (let [[rl m rr] (split cmp (.-r x) k)]
                   [(link (.-k x) (.-more x) (.-l x) rl) m rr])
        :else [(.-l x) x (.-r x)]))))

;; The union of trees a and b. combine joins a node of a with a node of b that compares
;; equal, the node of a first.
(defn- union [cmp combine a b]
  (cond
    (nil? a) b
    (nil? b) a
    :else (let [^Node x a
                [bl m br] (split cmp b (.-k x))
                ^Node y (if m (combine x m) x)]
            (link (.-k y) (.-more y)
                  (union cmp combine (.-l x) bl)
                  (union cmp combine (.-r x) br)))))

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

;; The bag holds data only. cnt counts items. The root size counts distinct keys.
(deftype WBBag [root ^long cnt]
  Object
  (equals [_ o]
    (and (instance? WBBag o)
         (== cnt (.-cnt ^WBBag o))
         (Util/equiv (stack-seq (spine root nil true) true)
                     (stack-seq (spine (.-root ^WBBag o) nil true) true))))
  (hashCode [_]
    (Murmur3/hashOrdered (or (stack-seq (spine root nil true) true) ())))
  (toString [this] (RT/printString this)))

(def empty-bag
  "The bag with no items."
  (WBBag. nil 0))

(defn bag-count
  "Returns the number of items in the bag."
  ^long [^WBBag b]
  (.-cnt b))

(defn bag-seq
  "Returns the items in order, or nil when the bag is empty."
  [^WBBag b]
  (stack-seq (spine (.-root b) nil true) true))

(defn bag-rseq
  "Returns the items in reverse order, or nil when the bag is empty."
  [^WBBag b]
  (stack-seq (spine (.-root b) nil false) false))

(defn bag-reduce
  "Like `reduce` with an initial value. It stops early on `reduced`."
  [f init ^WBBag b]
  (let [r (reduce-node f init (.-root b))]
    (if (reduced? r) @r r)))

(defn bag-groups
  "Returns the items as a vector of groups, in order. The items in a group compare equal,
   and they keep insertion order. `read-bag` makes the bag again from this vector."
  [^WBBag b]
  (mapv (fn [^Node x] (into [(.-k x)] (.-more x))) (nodes (.-root b))))

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
        (aset a i (mk (first g) (when (next g) (vec (rest g))) nil nil))))
    (WBBag. (build a 0 n) (reduce (fn [^long t g] (+ t (count g))) 0 gs))))

(defmethod print-method WBBag [b ^java.io.Writer w]
  (.write w "#clara.rules/sorted-bag ")
  (print-method (bag-groups b) w))

;; The functions below take the comparator cmp. It must be the comparator that built the
;; collection. Another comparator breaks the order, and nothing detects that.

(defn insert
  "Adds x to the bag. Items that compare equal to x keep their place before x."
  [cmp ^WBBag b x]
  (WBBag. (ins cmp (.-root b) x nil append-group) (inc (.-cnt b))))

(defn remove-item
  "Removes one item that is = to x. It looks among the items that compare equal to x, and
   removes the newest one that is = to x. Returns the same bag when there is none."
  [cmp ^WBBag b x]
  (let [r (del cmp (.-root b) x)]
    (if (identical? r (.-root b))
      b
      (WBBag. r (dec (.-cnt b))))))

(defn merge-bags
  "Returns a bag that holds every item of a and every item of b. Where items of a and b
   compare equal, the items of a come first."
  [cmp ^WBBag a ^WBBag b]
  (WBBag. (union cmp join-groups (.-root a) (.-root b)) (+ (.-cnt a) (.-cnt b))))

;; clojure.core/subseq skips only one element on an exclusive bound, because a sorted set
;; holds each key once. These two skip every copy.

(defn- bound [^Comparator cmp test key]
  (fn [x] (test (.compare cmp x key) 0)))

(defn bag-subseq
  "Like `subseq`. test is one of <, <=, > or >=."
  ([cmp ^WBBag b test key]
   (let [in? (bound cmp test key)]
     (if (#{> >=} test)
       (drop-while (complement in?) (stack-seq (spine-from cmp (.-root b) key true nil) true))
       (take-while in? (bag-seq b)))))
  ([cmp b start-test start-key end-test end-key]
   (take-while (bound cmp end-test end-key) (bag-subseq cmp b start-test start-key))))

(defn bag-rsubseq
  "Like `rsubseq`. test is one of <, <=, > or >=."
  ([cmp ^WBBag b test key]
   (let [in? (bound cmp test key)]
     (if (#{< <=} test)
       (drop-while (complement in?) (stack-seq (spine-from cmp (.-root b) key false nil) false))
       (take-while in? (bag-rseq b)))))
  ([cmp b start-test start-key end-test end-key]
   (take-while (bound cmp start-test start-key) (bag-rsubseq cmp b end-test end-key))))

;; ---------------------------------------------------------------------------------------
;; The map

;; The map holds data only, like the bag. The root size counts keys.
(deftype WBMap [root]
  Object
  (equals [_ o]
    (and (instance? WBMap o)
         (== (size root) (size (.-root ^WBMap o)))
         (Util/equiv (entry-seq (spine root nil true) true)
                     (entry-seq (spine (.-root ^WBMap o) nil true) true))))
  (hashCode [_]
    (Murmur3/hashOrdered (or (entry-seq (spine root nil true) true) ())))
  (toString [this] (RT/printString this)))

(def empty-map
  "The map with no keys."
  (WBMap. nil))

(defn map-count
  "Returns the number of keys in the map."
  ^long [^WBMap m]
  (size (.-root m)))

(defn map-seq
  "Returns the map entries in key order, or nil when the map is empty."
  [^WBMap m]
  (entry-seq (spine (.-root m) nil true) true))

(defn map-rseq
  "Returns the map entries in reverse key order, or nil when the map is empty."
  [^WBMap m]
  (entry-seq (spine (.-root m) nil false) false))

(defn map-reduce-kv
  "Like `reduce-kv`, in key order. It stops early on `reduced`."
  [f init ^WBMap m]
  (let [r (reduce-kv-node f init (.-root m))]
    (if (reduced? r) @r r)))

(defn- update-node-vals [node f]
  (when node
    (let [^Node x node]
      (Node. (.-k x) (f (.-more x)) (update-node-vals (.-l x) f) (update-node-vals (.-r x) f)
             (.-size x)))))

(defn map-update-vals
  "Returns the map with f applied to every value. The keys and the tree shape stay."
  [^WBMap m f]
  (WBMap. (update-node-vals (.-root m) f)))

(defn map-pairs
  "Returns the entries as a vector of [k v] pairs, in key order. `read-map` makes the map
   again from this vector."
  [^WBMap m]
  (mapv (fn [^Node x] [(.-k x) (.-more x)]) (nodes (.-root m))))

(defn read-map
  "Returns a map from [k v] pairs in key order, with each key once, as `map-pairs` returns.
   It needs no comparator. It is also the data reader for #clara.rules/sorted-map."
  [pairs]
  (let [ps (vec pairs)
        n (count ps)
        a (object-array n)]
    (dotimes [i n]
      (let [p (nth ps i)]
        (aset a i (mk (nth p 0) (nth p 1) nil nil))))
    (WBMap. (build a 0 n))))

(defmethod print-method WBMap [m ^java.io.Writer w]
  (.write w "#clara.rules/sorted-map ")
  (print-method (map-pairs m) w))

;; Like assoc on a Clojure map, a new value keeps the key object already in the map.
(def ^:private replace-value
  (incoming-last (fn [^Node x ^Node y] (mk (.-k x) (.-more y) nil nil))))

(defn map-assoc
  "Returns the map with k mapped to v."
  [cmp ^WBMap m k v]
  (WBMap. (ins cmp (.-root m) k v replace-value)))

(defn map-dissoc
  "Returns the map without k. Returns the same map when k is absent."
  [cmp ^WBMap m k]
  (let [r (del-key cmp (.-root m) k)]
    (if (identical? r (.-root m)) m (WBMap. r))))

(defn map-get
  "Returns the value of k, or not-found when k is absent."
  ([cmp m k] (map-get cmp m k nil))
  ([cmp ^WBMap m k not-found]
   (if-let [^Node x (find-node cmp (.-root m) k)]
     (.-more x)
     not-found)))

(defn map-contains?
  "Returns true when the map has k."
  [cmp ^WBMap m k]
  (some? (find-node cmp (.-root m) k)))

(defn map-merge-with
  "Like `merge-with` for two maps. (f value-in-a value-in-b) gives the value of a key that
   is in both maps. The key object comes from a."
  [cmp f ^WBMap a ^WBMap b]
  (let [combine (fn [^Node x ^Node y] (mk (.-k x) (f (.-more x) (.-more y)) nil nil))]
    (WBMap. (union cmp combine (.-root a) (.-root b)))))

(defn map-merge
  "Like `merge` for two maps. Where both maps have a key, the value of b wins."
  [cmp a b]
  (map-merge-with cmp (fn [_ v] v) a b))

;; ---------------------------------------------------------------------------------------
;; Sorted map view

;; A Clojure sorted map over a WBMap and its comparator. It prints as an ordinary map. It
;; implements MapEquivalence and java.util.Map, so = works both ways with other maps.
(deftype SortedMapView [^Comparator cmp ^WBMap m meta]
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
  (count [_] (map-count m))
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
              (and (== (map-count m) (.size o))
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
  (size [_] (map-count m))
  (isEmpty [_] (zero? (map-count m)))
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
  [^WBBag b]
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
