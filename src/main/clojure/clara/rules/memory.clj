(ns clara.rules.memory
  "This namespace is for internal use and may move in the future.
  Specification and default implementation of working memory"
  (:require [ham-fisted.api :as hf]
            [ham-fisted.mut-map :as hm])
  (:import [java.util
            Map
            List
            Collections
            LinkedList
            NavigableMap
            PriorityQueue
            TreeMap]
           [ham_fisted MutableMap]))

(defprotocol IPersistentMemory
  (to-transient [memory]))

(defprotocol IMemoryReader
  ;; Returns the rulebase associated with the given memory.
  (get-rulebase [memory])

  ;; Returns a function that produces a map of alpha nodes to
  ;; facts that match the type of the node
  (get-alphas-fn [memory])

  ;; Returns the elements assoicated with the given node.
  (get-elements [memory node bindings])

  ;; Returns all elements associated with the given node, regardless of bindings.
  (get-elements-all [memory node])

  ;; Returns the tokens associated with the given node.
  (get-tokens [memory node bindings])

  ;; Returns a map of all the bindings to tokens associated with the given node.
  (get-tokens-map [memory node])

  ;; Returns all tokens associated with the given node, regardless of bindings
  (get-tokens-all [memory node])

  ;; Returns the reduced form of objects processed by an accumulator node
  ;; for facts that match the given bindings.
  (get-accum-reduced [memory node join-bindings fact-bindings])

  ;; Returns all reduced results for the given node that matches
  ;; the given join bindings, independent of the individual fact-bindings
  ;; created by the accumulator's condition.
  (get-accum-reduced-all [memory node join-bindings])

  ;; Returns a tuple of [join-bindings fact-bindings result] for all
  ;; accumulated items on this node.
  (get-accum-reduced-complete [memory node])

  ;; Returns insertions that occurred at the given node for the given token.
  ;; Returns a sequence of the form
  ;; [facts-inserted-for-one-rule-activation facts-inserted-for-another-rule-activation]
  (get-insertions [memory node token])

  ;; Returns all insertions that occurred in the given node's RHS; this takes the form
  ;; {token [facts-inserted-for-one-rule-activation facts-inserted-for-another-rule-activation]}
  (get-insertions-all [memory node])

  ;; Returns a map of nodes with pending activations to the activations themselves.
  (get-activations [memory]))

(defprotocol ITransientMemory

  ;; Adds working memory elements to the given working memory at the given node.
  (add-elements! [memory node join-bindings elements])

  ;; Remove working memory elements from the given working memory at the given node.
  (remove-elements! [memory node elements join-bindings])

  ;; Add tokens to the given working memory at the given node.
  (add-tokens! [memory node join-bindings tokens])

  ;; Removes tokens from the given working memory at the given node.
  (remove-tokens! [memory node join-bindings tokens])

  ;; Adds the result of a reduced accumulator execution to the given memory and node.
  (add-accum-reduced! [memory node join-bindings accum-result fact-bindings])

  ;; Removes the result of a reduced accumulator execution to the given memory and node.
  (remove-accum-reduced! [memory node join-bindings fact-bindings])

  ;; Add a record that a given fact twas inserted at a given node with
  ;; the given support. Used for truth maintenance.
  ;; This should be called at most once per rule activation.
  (add-insertions! [memory node token facts])

  ;; Removes all records of facts that were inserted at the given node
  ;; due to the given token. Used for truth maintenance.
  ;; This function returns a map of each token to the associated facts
  ;; it removed.
  (remove-insertions! [memory node token])

  ;; Add a sequence of activations.
  (add-activations! [memory production activations])

  ;; Pop an activation from the working memory. Returns nil if no
  ;; activations are pending.
  (pop-activations! [memory count])

  ;; Returns the group of the next activation, or nil if none are pending.
  (next-activation-group [memory])

  ;; Remove the given activations from the working memory.  This is expected
  ;; to return a tuple of the form [removed-activations unremoved-activations],
  ;; where unremoved-activations is comprised of activations passed to the memory
  ;; for removal but which were not removed because they were not present in the memory's
  ;; store of pending activations.
  (remove-activations! [memory production activations])

  ;; Clear all activations from the working memory
  (clear-activations! [memory])

  ;; Converts the transient memory to persistent form.
  (to-persistent! [memory]))

(defn- coll-empty?
  "Returns true if the collection is empty.  Does not call seq due to avoid
  overhead that may cause for non-persistent collection types, e.g.
  java.util.LinkedList, etc."
  [^java.util.Collection coll]
  (or (nil? coll) (.isEmpty coll)))

(defn- list-remove!
  "Removes the item, to-remove, from the given list, lst.  If it is found and removed,
  returns true.  Otherwise returns false.  Only removes the first element in the list
  that is equal to to-remove.  Equality is done based on the given eq-pred function.
  If it isn't given, the default is = .  If others are equal, they will not be removed.
  This is similar to java.util.List.remove(Object).  lst is updated in place for performance.
  This implies that the list must support the mutable list interface, namely via the
  java.util.List.listIterator()."
  ([^java.util.List lst to-remove]
   (list-remove! lst to-remove =))
  ([^java.util.List lst to-remove eq-pred]
   (if-not (coll-empty? lst)
     (let [li (.listIterator lst)]
       (loop [x (.next li)]
         (cond
           (eq-pred to-remove x)
           (do
             (.remove li)
             true)

           (.hasNext li)
           (recur (.next li))

           :else
           false)))
     false)))

(defn- add-all!
  "Adds all items from source to the destination dest collection
  destructively.  Avoids using Collection.addAll() due to unnecessary
  performance overhead of calling Collection.toArray() on the
  incoming source. Returns dest."
  [^java.util.Collection dest source]
  (doseq [x source]
    (.add dest x))
  dest)

(defn- linked-list?
  [coll]
  (instance? LinkedList coll))

(defn- ->linked-list
  "Creates a new java.util.LinkedList from the coll, but avoids using
  Collection.addAll(Collection) since there is unnecessary overhead 
  in this of calling Collection.toArray() on coll."
  ^java.util.List [coll]
  (if (linked-list? coll)
    coll
    (add-all! (LinkedList.) coll)))

(defn- mutable-map?
  [m]
  (instance? MutableMap m))

(defn- ->mutable-map
  "Creates a new ham_fisted.MutableMap from the map, but only if necessary."
  [m]
  (if (mutable-map? m)
    m
    (hf/mut-map m)))

(defn- ->persistent-coll
  "Creates a persistent collection from the input collection, but only if necessary"
  [coll]
  (cond
    (coll? coll)
    coll

    (mutable-map? coll)
    (persistent! coll)

    (map? coll)
    (persistent! coll)

    :else
    (seq coll)))

(defn- remove-first-of-each!
  "Remove the first instance of each item in the given remove-seq that
  appears in the collection coll.  coll is updated in place for
  performance.  This implies that the coll must support the mutable
  collection interface method Collection.remove(Object).  Returns a tuple
  of the form [remove-seq-items-removed remove-seq-items-not-removed].
  An optional compare-fn can be given to specify how to compare remove-seq 
  items against items in coll.  The default compare-fn is = .
  For immutable collection removal, use the non-destructive remove-first-of-each
  defined below."
  ([remove-seq ^java.util.List coll]
   (remove-first-of-each! remove-seq coll =))

  ([remove-seq ^java.util.List coll compare-fn]
   ;; Optimization for special case of one item to remove,
   ;; which occurs frequently.
   (if (= 1 (count remove-seq))
     (let [to-remove (first remove-seq)]
       (if (list-remove! coll to-remove compare-fn)
         [remove-seq []]
         [[] remove-seq]))

     ;; Otherwise, perform a linear search for items to remove.
     (loop [to-remove (first remove-seq)
            remove-seq (next remove-seq)
            removed (transient [])
            not-removed (transient [])]
       (if to-remove
         (let [found? (list-remove! coll to-remove compare-fn)
               removed (if found?
                         (conj! removed to-remove)
                         removed)
               not-removed (if found?
                             not-removed
                             (conj! not-removed to-remove))]
           (recur (first remove-seq)
                  (next remove-seq)
                  removed
                  not-removed))
         ;; If this is expensive, using a mutable collection maybe good to
         ;; consider here in a future optimization.
         [(persistent! removed) (persistent! not-removed)])))))

(defn remove-first-of-each
  "Remove the first instance of each item in the given remove-seq that
  appears in the collection.  This also tracks which items were found
  and removed.  Returns a tuple of the form:
  [items-removed coll-with-items-removed items-not-removed]
  This function does so eagerly since
  the working memories with large numbers of insertions and retractions
  can cause lazy sequences to become deeply nested."
  [remove-seq coll]
  (cond

    ;; There is nothing to remove.
    (empty? remove-seq) [[] coll]

    ;; Otherwise, perform a linear search for items to remove.
    :else (loop [f (first coll)
                 r (rest coll)
                 [remove-seq items-removed result] [remove-seq (transient []) (transient [])]]

            (if f
              (recur (first r)
                     (rest r)

                     ;; Determine if f matches any of the items to remove.
                     (loop [to-remove (first remove-seq)
                            remove-seq (rest remove-seq)
                            ;; Remember what is left to remove for later.
                            left-to-remove (transient [])]

                       ;; Try to find if f matches anything to-remove.
                       (if to-remove
                         (if (= to-remove f)

                           ;; Found a match, so the search is done.
                           [(persistent! (reduce conj! left-to-remove remove-seq))
                            (conj! items-removed to-remove)
                            result]

                           ;; Keep searching for a match.
                           (recur (first remove-seq)
                                  (rest remove-seq)
                                  (conj! left-to-remove to-remove)))

                         ;; No matches found.
                         [(persistent! left-to-remove)
                          items-removed
                          (conj! result f)])))

              [(persistent! items-removed) (persistent! result) remove-seq]))))

(defn fast-token-compare [compare-fn token other-token]
  ;; Fastest path is if the two tokens are truly identical.
  (or (identical? token other-token)
      ;; Assumption is that both arguments given are tokens already.
      (and (let [bindings (:bindings token)
                 other-bindings (:bindings other-token)]
             ;; Calling `count` on these Clojure maps shows up as a bottleneck
             ;; even with clojure.lang.IPersistentMap being clojure.lang.Counted unfortunately.
             (and (= (.size ^java.util.Map bindings)
                     (.size ^java.util.Map other-bindings))
                  ;; `every?` is too slow for a performance critical place like this.  It
                  ;; calls `seq` too many times on the underlying maps.  Instead `seq` one
                  ;; time and keep using that same seq.
                  ;; Also avoiding Clojure destructuring since even that is not as fast
                  ;; pre-1.9.0.
                  (if-let [^clojure.lang.ISeq entries (.seq ^clojure.lang.Seqable bindings)]
                    ;; Type hint to Indexed vs MapEntry just because MapEntry seems to be a
                    ;; less stable impl detail to rely on.
                    (loop [^clojure.lang.Indexed entry (.first entries)
                           entries (.next entries)]
                      (let [k (some-> entry (.nth 0))
                            v (some-> entry (.nth 1))]
                        (if (and k
                                 ;; other-bindings will always be persistent map so invoke
                                 ;; it directly.  It is faster than `get`.
                                 (compare-fn v (other-bindings k)))
                          (recur (some-> entries .first)
                                 (some-> entries .next))
                          ;; If there is no k left, then every entry matched.  If there is a k,
                          ;; that means the comparison failed, so the maps aren't equal.
                          (not k))))
                    ;; Empty bindings on both sides.
                    true)))

           ;; Check the :matches on each token.  :matches need to be in the same order on both
           ;; tokens to be considered the same.
           (let [^clojure.lang.Indexed matches (:matches token)
                 ^clojure.lang.Indexed other-matches (:matches other-token)
                 count-matches (.size ^java.util.List matches)]
             (and (= count-matches
                     (.size ^java.util.List other-matches))
                  (loop [i 0]
                    (cond
                      (= i count-matches)
                      true

                      ;; Compare node-id's first.  Fallback to comparing facts.  This will
                      ;; most very likely be the most expensive part to execute.
                      (let [^clojure.lang.Indexed m (.nth matches i)
                            ^clojure.lang.Indexed om (.nth other-matches i)]
                        ;; A token :matches tuple is of the form [fact node-id].
                        (and (= (.nth m 1) (.nth om 1))
                             (compare-fn (.nth m 0) (.nth om 0))))
                      (recur (inc i))

                      :else
                      false)))))))

(defprotocol IdentityComparable
  (using-token-identity! [this bool]))

(deftype RuleOrderedActivation [node-id
                                token
                                activation
                                rule-load-order
                                ^:unsynchronized-mutable use-token-identity?]
  IdentityComparable
  ;; NOTE!  This should never be called on a RuleOrderedActivation instance that has been stored
  ;; somewhere in local memory because it could cause interference across threads that have
  ;; multiple versions of local memories that are sharing some of their state.  This is only intended
  ;; to be called by ephemeral, only-local references to RuleOrderedActivation instances used to
  ;; search for activations to remove from memory when performing `remove-activations!` operations.
  ;; The reason this mutable state exists at all is to "flip" a single instance of a RuleOrderedActivation
  ;; from identity to value equality based comparable when doing the "two-pass" removal search operation
  ;; of `remove-activations!`.  This avoids having to create different instances for each pass.
  (using-token-identity! [this bool]
    (set! use-token-identity? bool)
    this)
  Object
  ;; Two RuleOrderedActivation instances should be equal if and only if their
  ;; activation is equal.  Note that if the node of two activations is the same,
  ;; their rule-load-order must be the same.  Using a deftype wrapper allows us to
  ;; use Clojure equality to determine this while placing the wrapper in a Java data
  ;; structure that uses Java equality; the Java equality check will simply end up calling
  ;; Clojure equality checks.
  (equals [this other]
    ;; Note that the .equals method is only called by PriorityQueue.remove, and the object provided
    ;; to the .remove method will never be identical to any object in the queue.  A short-circuiting
    ;; check for reference equality would therefore be pointless here because it would never be true.
    (boolean
     (when (instance? RuleOrderedActivation other)
       (let [^RuleOrderedActivation other other]
         (and
            ;; If the node-id of two nodes is equal then we can assume that the nodes are equal.
          (= node-id
             (.node-id other))

            ;; We check with identity based semantics on the other when the use-token-identity? field
            ;; indicates to do so.
          (if (or use-token-identity? (.-use-token-identity? other))
            (fast-token-compare identical? token (.-token other))
            (fast-token-compare = token (.-token other)))))))))

(defn- ->rule-ordered-activation
  "Take an activation from the engine and wrap it in a map that includes information
  on the rule load order.  In Clojure, as opposed to ClojureScript, each activation should
  be wrapped in this way exactly once (that is, the value of the :activation key should
                                            be an activation from the engine.)"
  ([activation]
   (->rule-ordered-activation activation false))
  ([activation use-token-identity?]
   (let [node (:node activation)]
     (RuleOrderedActivation. (:id node)
                             (:token activation)
                             activation
                             (or (-> node
                                     :production
                                     meta
                                     :clara.rules.compiler/rule-load-order)
                                 0)
                             use-token-identity?))))

(defn- queue-activations!
  "Add activations to a queue. The wrap-rule-order? option should be true
  unless the activations in question have previously been wrapped."
  ([^java.util.Queue pq activations]
   (queue-activations! pq activations true))
  ([^java.util.Queue pq activations wrap-rule-order?]
   (if wrap-rule-order?
     (doseq [act activations]
       (.add pq (->rule-ordered-activation act)))
     (doseq [act activations]
       (.add pq act)))
   pq))

(defn- ->activation-priority-queue
  "Given activations, create a priority queue based on rule ordering.
  The activations should be wrapped by using the wrap-rule-order? option
  if they have not been wrapped already."
  ([activations]
   (->activation-priority-queue activations true))
  ([activations wrap-rule-order?]
   (let [init-cnt (count activations)
         ;; Note that 11 is the default initial value; there is no constructor
         ;; for PriorityQueue that takes a custom comparator and does not require
         ;; an initial size to be passed.
         pq (PriorityQueue. (if (pos? init-cnt) init-cnt 11)
                            (fn [^RuleOrderedActivation x
                                 ^RuleOrderedActivation y]
                              (compare (.rule-load-order x)
                                       (.rule-load-order y))))]
     (queue-activations! pq activations wrap-rule-order?))))

(declare ->PersistentLocalMemory)

;;; Transient local memory implementation. Typically only persistent memory will be visible externally.

(deftype TransientLocalMemory [rulebase
                               activation-group-sort-fn
                               activation-group-fn
                               alphas-fn
                               ^Map alpha-memory
                               ^Map beta-memory
                               ^Map accum-memory
                               ^Map production-memory
                               ^NavigableMap activation-map]

  IMemoryReader
  (get-rulebase [memory] rulebase)

  (get-alphas-fn [memory] alphas-fn)

  (get-elements [memory node bindings]
    (get (get alpha-memory (:id node) {})
         bindings
         []))

  (get-elements-all [memory node]
    (sequence
     cat
     (vals
      (get alpha-memory (:id node) {}))))

  (get-tokens [memory node bindings]
    (get (get beta-memory (:id node) {})
         bindings
         []))

  (get-tokens-map [memory node]
    (get beta-memory (:id node) {}))

  (get-tokens-all [memory node]
    (sequence
     cat
     (vals (get beta-memory (:id node) {}))))

  (get-accum-reduced [memory node join-bindings fact-bindings]
    (get-in accum-memory [(:id node) join-bindings fact-bindings] ::no-accum-reduced))

  (get-accum-reduced-all [memory node join-bindings]
    (get
     (get accum-memory (:id node) {})
     join-bindings))

  ;; TODO: rename existing get-accum-reduced-all and use something better here.
  (get-accum-reduced-complete [memory node]
    (for [[join-binding joins] (get accum-memory (:id node) {})
          [fact-binding reduced] joins]
      {:join-bindings join-binding
       :fact-bindings fact-binding
       :result reduced}))

  (get-insertions [memory node token]
    (get
     (get production-memory (:id node) {})
     token
     []))

  (get-insertions-all [memory node]
    (get production-memory (:id node) {}))

  (get-activations [memory]
    (into []
          (comp cat
                (map (fn [^RuleOrderedActivation a]
                       (.activation a))))
          (vals activation-map)))

  ITransientMemory
  (add-elements! [memory node join-bindings elements]
    (hm/compute! alpha-memory (:id node)
                 (fn do-add-bem
                   [_ bem]
                   (if bem
                     (let [binding-element-map (->mutable-map bem)]
                       (hm/compute! binding-element-map join-bindings
                                    (fn do-add-bel
                                      [_ bel]
                                      (if bel
                                        (let [binding-element-list (->linked-list bel)]
                                          (add-all! binding-element-list elements)
                                          binding-element-list)
                                        elements)))
                       binding-element-map)
                     {join-bindings elements}))))

  (remove-elements! [memory node join-bindings elements]
    ;; Do nothing when no elements to remove.
    (when-not (coll-empty? elements)
      (let [removed-elements-result (hf/mut-list)]
        (hm/compute-if-present! alpha-memory (:id node)
                                (fn do-rem-bem
                                  [_ bem]
                                  (let [binding-element-map (->mutable-map bem)]
                                    (hm/compute-if-present! binding-element-map join-bindings
                                                            (fn do-rem-bel
                                                              [_ bel]
                                                              (let [binding-element-list (->linked-list bel)
                                                                    removed-elements (first (remove-first-of-each! elements binding-element-list))]
                                                                (hf/add-all! removed-elements-result removed-elements)
                                                                (not-empty binding-element-list))))
                                    (not-empty binding-element-map))))
        (hf/persistent! removed-elements-result))))

  (add-tokens! [memory node join-bindings tokens]
    (hm/compute! beta-memory (:id node)
                 (fn do-add-btm
                   [_ btm]
                   (if btm
                     (let [binding-token-map (->mutable-map btm)]
                       (hm/compute! binding-token-map join-bindings
                                    (fn do-add-btl
                                      [_ btl]
                                      (if btl
                                        (let [binding-token-list (->linked-list btl)]
                                          (add-all! binding-token-list tokens)
                                          binding-token-list)
                                        tokens)))
                       binding-token-map)
                     {join-bindings tokens}))))

  (remove-tokens! [memory node join-bindings tokens]
    ;; The reasoning here is the same as remove-elements!
    (when-not (coll-empty? tokens)
      (let [removed-tokens-result (hf/mut-list)]
        (hm/compute-if-present!
         beta-memory (:id node)
         (fn do-rem-btm
           [_ btm]
           (let [binding-token-map (->mutable-map btm)]
             (hm/compute-if-present!
              binding-token-map join-bindings
              (fn do-rem-btl
                [_ btl]
                (let [binding-token-list (->linked-list btl)
                      ;; Attempt to remove tokens using the faster indentity-based equality first since
                      ;; most of the time this is all we need and it can be much faster.  Any token that
                      ;; wasn't removed via identity, has to be "retried" with normal value-based
                      ;; equality though since those semantics are supported within the engine.  This
                      ;; slower path should be rare for any heavy retraction flows - such as those that come
                      ;; via truth maintenance.
                      [removed-tokens not-removed-tokens]
                      (remove-first-of-each! tokens
                                             binding-token-list
                                             (partial fast-token-compare identical?))]
                  (hf/add-all! removed-tokens-result removed-tokens)
                  (when (seq not-removed-tokens)
                    (let [[other-removed-tokens]
                          (remove-first-of-each! not-removed-tokens binding-token-list
                                                 (partial fast-token-compare =))]
                      (hf/add-all! removed-tokens-result other-removed-tokens)))
                  (not-empty binding-token-list))))
             (not-empty binding-token-map))))
        (hf/persistent! removed-tokens-result))))

  (add-accum-reduced! [memory node join-bindings accum-result fact-bindings]
    (hm/compute! accum-memory (:id node)
                 (fn add-jbam
                   [_ jbam]
                   (if jbam
                     (let [join-binding-accum-map (->mutable-map jbam)]
                       (hm/compute! join-binding-accum-map join-bindings
                                    (fn add-fbam
                                      [_ fact-binding-accum-map]
                                      (assoc fact-binding-accum-map fact-bindings accum-result)))
                       join-binding-accum-map)
                     {join-bindings {fact-bindings accum-result}}))))

  (remove-accum-reduced! [memory node join-bindings fact-bindings]
    (hm/compute-if-present! accum-memory (:id node)
                            (fn add-jbam
                              [_ jbam]
                              (let [join-binding-accum-map (->mutable-map jbam)]
                                (hm/compute-if-present! join-binding-accum-map join-bindings
                                                        (fn add-fbam
                                                          [_ fact-binding-accum-map]
                                                          (not-empty (dissoc fact-binding-accum-map fact-bindings))))
                                (not-empty join-binding-accum-map)))))

  ;; The value under each token in the map should be a sequence
  ;; of sequences of facts, with each inner sequence coming from a single
  ;; rule activation.
  (add-insertions! [memory node token facts]
    (hm/compute! production-memory (:id node)
                 (fn add-tfm
                   [_ tfm]
                   (if tfm
                     (let [token-facts-map (->mutable-map tfm)]
                       (hm/compute! token-facts-map token
                                    (fn add-tfl
                                      [_ tfl]
                                      (let [^List token-facts-list (->linked-list tfl)]
                                        (.add token-facts-list facts)
                                        token-facts-list)))
                       token-facts-map)
                     {token [facts]}))))

  (remove-insertions! [memory node tokens]
    ;; Remove the facts inserted from the given token.
    (let [results (hf/mut-map)]
      (hm/compute-if-present! production-memory (:id node)
                              (fn rem-tfm
                                [_ tfm]
                                (let [token-facts-map (->mutable-map tfm)]
                                  (doseq [token tokens]
                                    (hm/compute-if-present! token-facts-map token
                                                            (fn [_ tfl]
                                                              ;; Don't use contains? due to http://dev.clojure.org/jira/browse/CLJ-700
                                                              (let [^List token-facts-list (->linked-list tfl)
                                                                    ;; There is no particular significance in removing the
                                                                    ;; first group; we just need to remove exactly one.
                                                                    removed-facts (.remove token-facts-list 0)]
                                                                (hm/compute! results token
                                                                             (fn add-tfr
                                                                               [_ tfr]
                                                                               (let [token-facts-removed (->linked-list tfr)]
                                                                                 (add-all! token-facts-removed removed-facts)
                                                                                 token-facts-removed)))
                                                                (not-empty token-facts-list)))))
                                  (not-empty token-facts-map))))
      (persistent! (hf/update-values results (fn to-persistent [_ coll]
                                               (->persistent-coll coll))))))

  (add-activations!
    [memory production new-activations]
    (let [activation-group (activation-group-fn production)]
      (hm/compute! activation-map activation-group
                   (fn do-add-activations
                     [_ old-activations]
                     (cond
                       old-activations
                       (queue-activations! old-activations new-activations)

                       (not (coll-empty? new-activations))
                       (->activation-priority-queue new-activations)

                       :else nil)))))

  (pop-activations!
    [memory count]
    (loop [^List activations (hf/mut-list)
           remaining count]
      (cond
        (.isEmpty activation-map)
        (persistent! activations)

        (not (and (number? remaining)
                  (pos? remaining)))
        (persistent! activations)

        :else
        (let [entry (.firstEntry activation-map)
              key (.getKey entry)
              ^java.util.Queue activation-queue (.getValue entry)
              curr-popped-activations (not (.isEmpty activations))
              next-no-loop-activation (some-> ^RuleOrderedActivation (.peek activation-queue)
                                              (.activation)
                                              :node :production :props :no-loop)]
          (if (and curr-popped-activations next-no-loop-activation)
            (persistent! activations)
            (let [;; An empty value is illegal and should be removed by an action
                  ;; that creates one (e.g. a remove-activations! call).
                  ^RuleOrderedActivation activation-wrapper (.remove activation-queue)
                  ;; Extract the selected activation.
                  activation (.activation activation-wrapper)
                  empty-activation-group (.isEmpty activation-queue)]
              (.add activations activation)
              ;; This activation group is empty now, so remove it from
              ;; the map entirely.
              (when empty-activation-group
                (.remove activation-map key))
              (cond
                ;; This activation group is empty so return and do not  move
                ;; to the next activation group
                empty-activation-group
                (persistent! activations)
                ;; When we encounter a no-loop activation we need to stop returning activations since it would
                ;; flush updates after the RHS is activated
                (some-> activation :node :production :props :no-loop)
                (persistent! activations)

                :else
                (recur activations (dec remaining)))))))))

  (next-activation-group
    [memory]
    (when (not (.isEmpty activation-map))
      (let [entry (.firstEntry activation-map)]
        (.getKey entry))))

  (remove-activations! [memory production to-remove]
    (when-not (coll-empty? to-remove)
      (let [activation-group (activation-group-fn production)
            ^java.util.Queue activations (.get activation-map activation-group)
            removed-activations (LinkedList.)
            unremoved-activations (LinkedList.)]

        (if (coll-empty? activations)
          ;; If there are no activations present under the group
          ;; then we can't remove any.
          [[] to-remove]
          ;; Remove as many activations by identity as possible first.
          (let [not-removed (loop [to-remove-item (first to-remove)
                                   to-remove (next to-remove)
                                   not-removed (transient [])]
                              (if to-remove-item
                                (let [^RuleOrderedActivation act (->rule-ordered-activation to-remove-item true)]
                                  (if (.remove activations act)
                                    (do
                                      (.add removed-activations (.activation act))
                                      ;; The activations that are not removed in the identity checking sweep
                                      ;; are a superset of the activations that are removed after the equality
                                      ;; sweep finishes so we can just create the list of unremoved activations
                                      ;; during that sweep.
                                      (recur (first to-remove) (next to-remove) not-removed))
                                    (recur (first to-remove) (next to-remove) (conj! not-removed act))))
                                (persistent! not-removed)))]

            ;; There may still be activations not removed since the removal may be based on value-based
            ;; equality semantics.  Retractions in the engine do not require that identical object references
            ;; are given to remove object values that are equal.
            (doseq [^RuleOrderedActivation act not-removed]
              (if (.remove activations (using-token-identity! act false))
                (.add removed-activations (.activation act))
                (.add unremoved-activations (.activation act))))

            (when (coll-empty? activations)
              (.remove activation-map activation-group))

            [(Collections/unmodifiableList removed-activations)
             (Collections/unmodifiableList unremoved-activations)])))))

  (clear-activations!
    [memory]
    (.clear activation-map))

  (to-persistent! [memory]
    (let [persistent-maps (fn do-update-vals [update-fn m]
                            (->> m
                                 (reduce-kv (fn [m k v]
                                              (assoc! m k (update-fn v)))
                                            (hf/mut-map))
                                 persistent!))
          persistent-vals (partial persistent-maps ->persistent-coll)]
      (->PersistentLocalMemory rulebase
                               activation-group-sort-fn
                               activation-group-fn
                               alphas-fn
                               (persistent-maps persistent-vals alpha-memory)
                               (persistent-maps persistent-vals beta-memory)
                               (persistent-maps persistent-vals accum-memory)
                               (persistent-maps persistent-vals production-memory)
                               (into {}
                                     (map (juxt key (comp ->persistent-coll val)))
                                     activation-map)))))

(defrecord PersistentLocalMemory [rulebase
                                  activation-group-sort-fn
                                  activation-group-fn
                                  alphas-fn
                                  alpha-memory
                                  beta-memory
                                  accum-memory
                                  production-memory
                                  activation-map]
  IMemoryReader
  (get-rulebase [memory] rulebase)

  (get-alphas-fn [memory] alphas-fn)

  (get-elements [memory node bindings]
    (get (get alpha-memory (:id node) {})
         bindings
         []))

  (get-elements-all [memory node]
    (sequence
     cat
     (vals
      (get alpha-memory (:id node) {}))))

  (get-tokens [memory node bindings]
    (get (get beta-memory (:id node) {})
         bindings
         []))

  (get-tokens-map [memory node]
    (get beta-memory (:id node) {}))

  (get-tokens-all [memory node]
    (sequence
     cat
     (vals (get beta-memory (:id node) {}))))

  (get-accum-reduced [memory node join-bindings fact-bindings]
    ;; nil is a valid previously reduced value that can be found in the map.
    ;; Return ::no-accum-reduced instead of nil when there is no previously
    ;; reduced value in memory.
    (get-in accum-memory [(:id node) join-bindings fact-bindings] ::no-accum-reduced))

  (get-accum-reduced-all [memory node join-bindings]
    (get
     (get accum-memory (:id node) {})
     join-bindings))

  (get-accum-reduced-complete [memory node]
    (for [[join-binding joins] (get accum-memory (:id node) {})
          [fact-binding reduced] joins]
      {:join-bindings join-binding
       :fact-bindings fact-binding
       :result reduced}))

  (get-insertions [memory node token]
    (get
     (get production-memory (:id node) {})
     token
     []))

  (get-insertions-all [memory node]
    (get production-memory (:id node) {}))

  (get-activations [memory]
    (into []
          (comp cat
                (map (fn [^RuleOrderedActivation a]
                       (.activation a))))
          (vals activation-map)))

  IPersistentMemory
  (to-transient [memory]
    (TransientLocalMemory. rulebase
                           activation-group-sort-fn
                           activation-group-fn
                           alphas-fn
                           (->mutable-map alpha-memory)
                           (->mutable-map beta-memory)
                           (->mutable-map accum-memory)
                           (->mutable-map production-memory)
                           (let [treemap (TreeMap. ^java.util.Comparator activation-group-sort-fn)]
                             (doseq [[activation-group activations] activation-map]
                               (.put treemap
                                     activation-group
                                     (->activation-priority-queue activations false)))
                             treemap))))

(defn local-memory
  "Creates an persistent local memory for the given rule base."
  [rulebase activation-group-sort-fn activation-group-fn alphas-fn]

  (->PersistentLocalMemory rulebase
                           activation-group-sort-fn
                           activation-group-fn
                           alphas-fn
                           (hf/hash-map)
                           (hf/hash-map)
                           (hf/hash-map)
                           (hf/hash-map)
                           (hf/hash-map)))
