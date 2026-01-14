(ns clara.tools.inspect
  "Tooling to inspect a rule session. The two major methods here are:

  * inspect, which returns a data structure describing the session that can be used by tooling.
  * explain-activations, which uses inspect and prints a human-readable description covering
  why each rule activation or query match occurred."
  (:require [clara.rules.engine :as eng]
            [clara.rules.schema :as schema]
            [clara.rules.memory :as mem]
            [clara.rules.platform :as platform]
            [clojure.set :as set]
            [clara.tools.internal.inspect :as i]
            [clojure.main :refer [demunge]]
            [schema.core :as s]
            [clojure.string :as str])
  (:import [clara.rules.engine
            ISystemFact
            ProductionNode
            RootJoinNode
            HashJoinNode
            ExpressionJoinNode
            NegationNode
            NegationWithJoinFilterNode]))

(s/defschema ConditionMatch
  "A structure associating a condition with the facts that matched them.  The fields are:
  :fact - A fact propagated from this condition in a rule or query.  For non-accumulator conditions,
  this will be the fact matched by the condition.  For accumulator conditions, it will be the result
  of the accumulation.  So, for example, if we have a condition like

  [?cold <- Cold]

  a ConditionMatch for this condition will have a Cold fact in its :fact field.  If we have a condition like

  [?min-cold <- (acc/min :temperature) :from [Cold]]

  the value of :fact will be the minimum temperature returned by the accumulator.

  :condition - A structure representing this condition.  This is the same structure used inside the structures defining
  rules and queries.

  :facts-accumulated (nullable) : When the condition is an accumulator condition, this will contain the individual facts over 
  which the accumulator ran.  For example, in the case above with the condition

  [?min-cold <- (acc/min :temperature) :from [Cold]]

  this will contain the individual Cold facts over which we accumulated, while the :fact field
  will contain the result of the accumulation."
  {:fact s/Any
   :condition schema/Condition
   (s/optional-key :facts-accumulated) [s/Any]})

;; A structured explanation of why a rule or query matched.
;; This is derived from the Rete-style tokens, but this token
;; is designed to propagate all context needed to easily inspect
;; the state of rules.  
(s/defrecord Explanation [matches :- [ConditionMatch]
                          bindings :- {s/Keyword s/Any}]) ; Bound variables

;; Schema of an inspected rule session.
(def RulesInspectionSchema
  {:rule-matches {schema/Rule [Explanation]}
   :query-matches {schema/Query [Explanation]}
   :condition-matches {schema/Condition [s/Any]}
   :root-facts [s/Any]
   :insertions {schema/Rule [{:explanation Explanation :fact s/Any}]}
   :fact->explanations {s/Any [{:rule schema/Rule
                                :explanation Explanation}]}
   (s/optional-key :unfiltered-rule-matches) {schema/Rule [Explanation]}})

(def FactsInspectionSchema
  {:rules {s/Int schema/Rule}
   :facts [{:fact s/Any
            (s/optional-key :rule-id) s/Int
            (s/optional-key :bindings) {s/Keyword s/Any}
            :fact-types [s/Any]}]})

(defn- gen-binding?
  [[k _v]]
  (.startsWith (name k) "?__gen__"))

(defn- dissoc-gen-bindings
  [bindings]
  (into {} (remove gen-binding? bindings)))

(defn get-condition-matches
  "Returns facts matching each condition"
  [nodes memory]
  (let [node-class->node-type (fn [node]
                                (get {ExpressionJoinNode :join
                                      HashJoinNode :join
                                      RootJoinNode :join
                                      NegationNode :negation
                                      NegationWithJoinFilterNode :negation} (type node)))

        join-node-ids (for [beta-node nodes
                            :let [node-type (node-class->node-type beta-node)]
                            ;; Unsupported and irrelevant node types will have a node-type of nil
                            ;; since the map in node-class->node-type won't contain an entry
                            ;; for them, so this check will remove them.
                            :when (contains? #{:join :negation}
                                             node-type)]
                        [(:id beta-node) (:condition beta-node) node-type])]
    (reduce
     (fn [matches [node-id condition node-type]]
       (update-in matches
                  (condp = node-type

                    :join
                    [condition]

                     ;; Negation nodes store the fact that they are a negation
                     ;; in their :node-type and strip the information out of the
                     ;; :condition field.  We reconstruct the negation boolean condition
                     ;; that is contained in rule and query data structures created by defrule
                     ;; and that conforms to the Condition schema.
                    :negation
                    [[:not condition]])
                  concat (map :fact (mem/get-elements-all memory {:id node-id}))))
     {}
     join-node-ids)))

(defn to-explanations
  "Helper function to convert tokens to explanation records."
  [session tokens]
  (let [memory (-> session eng/components :memory)
        id-to-node (get-in (eng/components session) [:rulebase :id-to-node])]

    (for [{:keys [matches bindings] :as token} tokens]
      (->Explanation
        ;; Convert matches to explanation structure.
       (for [[fact node-id] matches
             :let [node (id-to-node node-id)
                   condition (if (:accum-condition node)

                               {:accumulator (get-in node [:accum-condition :accumulator])
                                :from {:type (get-in node [:accum-condition :from :type])
                                       :constraints (or (seq (get-in node [:accum-condition :from :original-constraints]))
                                                        (get-in node [:accum-condition :from :constraints]))}}

                               {:type (:type (:condition node))
                                :constraints (or (seq (:original-constraints (:condition node)))
                                                 (:constraints (:condition node)))})]]
         (if (:accum-condition node)
           {:fact fact
            :condition condition
            :facts-accumulated (eng/token->matching-elements node memory token)}
           {:fact fact
            :condition condition}))

        ;; Remove generated bindings from user-facing explanation.
       (dissoc-gen-bindings bindings)))))

(defn gen-all-rule-matches
  [session]
  (when-let [activation-info (i/get-activation-info session)]
    (let [grouped-info (group-by #(-> % :activation :node) activation-info)]
      (into {}
            (map (fn [[k v]]
                   [(:production k)
                    (to-explanations session (map #(-> % :activation :token) v))]))
            grouped-info))))

(defn gen-fact->explanations
  [session]

  (let [{:keys [memory rulebase]} (eng/components session)
        {:keys [production-nodes]} rulebase
        rule-to-rule-node (into {} (for [rule-node production-nodes]
                                     [(:production rule-node) rule-node]))]
    (apply merge-with into
           (for [[rule rule-node] rule-to-rule-node
                 token (keys (mem/get-insertions-all memory rule-node))
                 insertion-group (mem/get-insertions memory rule-node token)
                 insertion insertion-group]
             {insertion [{:rule rule
                          :explanation (first (to-explanations session [token]))}]}))))

(defn get-root-facts
  "Returns all root facts in the session that were not derived from rules."
  [session]
  ;;; If there are any root elements at all then attempt to find them in the memory.
  ;;; Old sessions may not have any root elements stored in memory when serialized.
  (let [{:keys [rulebase memory]} (eng/components session)
        {:keys [alpha-memory]} memory
        {:keys [production-nodes id-to-node]} rulebase
        ;;; Gather facts from alpha memory
        facts-from-alphas (->> (vals alpha-memory)
                               (mapcat vals)
                               (mapcat identity)
                               (map :fact)
                               (map platform/fact-id-wrap)
                               (set))
        ;;; Gather facts that were inserted by rules
        facts-from-inserts (->> (for [rule-node production-nodes
                                      token (keys (mem/get-insertions-all memory rule-node))
                                      insertion-group (mem/get-insertions memory rule-node token)
                                      fact insertion-group]
                                  (platform/fact-id-wrap fact))
                                (set))
        ;;; Gather facts that were matched by rules
        facts-from-matches (->> (for [rule-node production-nodes
                                      {:keys [matches] :as token} (keys (mem/get-insertions-all memory rule-node))
                                      [fact node-id] matches
                                      :let [node (id-to-node node-id)
                                            accum (when (:accum-condition node)
                                                    (eng/token->matching-elements node memory token))]
                                      fact (if (and (some? accum) (coll? accum))
                                             accum
                                             [fact])]
                                  (platform/fact-id-wrap fact))
                                (set))
        ;;; Combine all gathered facts and remove duplicates, using their identity wrappers
        all-facts (set/union facts-from-alphas facts-from-inserts facts-from-matches)
        ;;; Root facts are those that are not derived from rules
        root-facts (set/difference all-facts facts-from-inserts)]
    ;;; Return the unwrapped root facts
    (for [wrapper root-facts]
      (platform/fact-id-unwrap wrapper))))

(def ^{:doc "Return a new session on which information will be gathered for optional inspection keys.
       This can significantly increase memory consumption since retracted facts
       cannot be garbage collected as normally."}
  with-full-logging i/with-activation-listening)

(def ^{:doc "Return a new session without information gathering on this session for optional inspection keys.
       This new session will not retain references to any such information previously gathered."}
  without-full-logging i/without-activation-listening)

(s/defn inspect :- RulesInspectionSchema
  " Returns a representation of the given rule session useful to understand the
  state of the underlying rules.

  The returned structure always includes the following keys:

  * :rule-matches -- a map of rule structures to their matching explanations.
  Note that this only includes rule matches with corresponding logical 
  insertions after the rules finished firing.
  * :query-matches -- a map of query structures to their matching explanations.
  * :condition-matches -- a map of conditions pulled from each rule to facts they match.
  * :insertions -- a map of rules to a sequence of {:explanation E, :fact F} records
  to allow inspection of why a given fact was inserted.
  * :fact->explanations -- a map of facts inserted to a sequence 
  of maps of the form {:rule rule-structure :explanation explanation}, 
  where each such map justifies a single insertion of the fact.

  And additionally includes the following keys for operations 
  performed after a with-full-logging call on the session:

  * :unfiltered-rule-matches: A map of rule structures to their matching explanations.
  This includes all rule activations, regardless of whether they led to insertions or if
  they were ultimately retracted.  This should be considered low-level information primarily
  useful for debugging purposes rather than application control logic, although legitimate use-cases
  for the latter do exist if care is taken.  Patterns of insertion and retraction prior to returning to
  the caller are internal implementation details of Clara unless explicitly controlled by the user.

  Users may inspect the entire structure for troubleshooting or explore it
  for specific cases. For instance, the following code snippet could look
  at all matches for some example rule:

  (defrule example-rule ... )

  ...

  (get-in (inspect example-session) [:rule-matches example-rule])

  ...

  The above segment will return matches for the rule in question."
  [session]
  (let [{:keys [memory rulebase]} (eng/components session)
        {:keys [production-nodes query-nodes id-to-node]} rulebase
        ;; Map of queries to their nodes in the network.
        query-to-nodes (->> (for [[_query-name query-node] query-nodes]
                              [(:query query-node) query-node])
                            (into {}))
        query-matches (->> (for [[query query-node] query-to-nodes]
                             [query (to-explanations session
                                                     (mem/get-tokens-all memory query-node))])
                           (into {}))
        ;; Map of rules to their nodes in the network.
        rule-to-nodes (->> (for [rule-node production-nodes]
                             [(:production rule-node) rule-node])
                           (into {}))
        rule-matches (->> (for [[rule rule-node] rule-to-nodes]
                            [rule (to-explanations session
                                                   (keys (mem/get-insertions-all memory rule-node)))])
                          (into {}))
        condition-matches (get-condition-matches (vals id-to-node) memory)
        root-facts (get-root-facts session)
        insertions (->> (for [[rule rule-node] rule-to-nodes]
                          [rule
                           (for [token (keys (mem/get-insertions-all memory rule-node))
                                 insertion-group (get (mem/get-insertions-all memory rule-node) token)
                                 insertion insertion-group]
                             {:explanation (first (to-explanations session [token])) :fact insertion})])
                        (into {}))
        fact-explanations (into {} (gen-fact->explanations session))
        base-info {:rule-matches rule-matches
                   :query-matches query-matches
                   :condition-matches condition-matches
                   :root-facts root-facts
                   :insertions insertions
                   :fact->explanations fact-explanations}]
    (if-let [unfiltered-rule-matches (gen-all-rule-matches session)]
      (assoc base-info :unfiltered-rule-matches unfiltered-rule-matches)
      base-info)))

(defn explain-activation
  "Prints a human-readable explanation of the facts and conditions that created the Rete token."
  ([explanation] (explain-activation explanation ""))
  ([explanation prefix]
   (doseq [{:keys [fact condition]} (:matches explanation)]
     (if (:from condition)
       ;; Explain why the accumulator matched.
       (let [{:keys [accumulator from]} condition]
         (println prefix fact)
         (println prefix "  accumulated with" accumulator)
         (println prefix "  from" (:type from))
         (println prefix "  where" (:constraints from)))

       ;; Explain why a condition matched.
       (let [{:keys [type constraints]} condition]
         (println prefix fact)
         (println prefix "  is a" type)
         (println prefix "  where" constraints))))))

(defn explain-activations
  "Prints a human-friendly explanation of why rules and queries matched in the given session.
  A caller my optionally pass a :rule-filter-fn, which is a predicate

  (clara.tools.inspect/explain-activations session
                                           :rule-filter-fn (fn [rule] (re-find my-rule-regex (:name rule))))"

  [session & {:keys [rule-filter-fn] :as options}]
  (let [filter-fn (or rule-filter-fn (constantly true))]

    (doseq [[rule explanations] (:rule-matches (inspect session))
            :when (filter-fn rule)
            :when (seq explanations)]
      (println "rule"  (or (:name rule) (str "<" (:lhs rule) ">")))
      (println "  executed")
      (println "   " (:rhs rule))
      (doseq [explanation explanations]
        (println "  with bindings")
        (println "    " (:bindings explanation))
        (println "  because")
        (explain-activation explanation "    "))
      (println))

    (doseq [[rule explanations] (:query-matches (inspect session))
            :when (filter-fn rule)
            :when (seq explanations)]
      (println "query"  (or (:name rule) (str "<" (:lhs rule) ">")))
      (doseq [explanation explanations]
        (println "  with bindings")
        (println "    " (:bindings explanation))
        (println "  qualified because")
        (explain-activation explanation "    "))
      (println))))

(let [inverted-type-lookup (zipmap (vals eng/node-type->abbreviated-type)
                                   (keys eng/node-type->abbreviated-type))]
  (defn node-fn-name->production-name
    "A helper function for retrieving the name or names of rules that a generated function belongs to.

    'session' - a LocalSession from which a function was retrieved
    'node-fn' - supports the following types:
    1. String   - expected to be in the format '<namespace>/<Node abbreviation>_<NodeId>_<Function abbreviation>'.
    Expected use-case for string would be in the event that a user copy pasted this function identifier
    from an external tool, ex. a jvm profiler
    2. Symbol   - expected to be in the format '<namespace>/<Node abbreviation>_<NodeId>_<Function abbreviation>.
    Has the same use-case as string, just adds flexibility to the type.
    3. Function - expected to be the actual function from the Session
    This covers a use-case where the user can capture the function being used and programmatically
    trace it back to the rules being executed."
    [session node-fn]
    (let [fn-name-str (cond
                        (string? node-fn)
                        node-fn

                        (fn? node-fn)
                        (str node-fn)

                        (symbol? node-fn)
                        (str node-fn)

                        :else
                        (throw (ex-info "Unsupported type for 'node-fn-name->production-name'"
                                        {:type (type node-fn)
                                         :supported-types ["string" "symbol" "fn"]})))
          fn-name-str (-> fn-name-str demunge (str/split #"/") last)

          simple-fn-name (-> (or (re-find #"(.+)--\d+" fn-name-str) ;; anonymous function
                                 (re-find #"(.+)" fn-name-str)) ;; regular function
                             last)

          [node-abr node-id _] (str/split simple-fn-name #"-")]
      ;; used as a sanity check that the fn provided is in the form expected, ie. <NodeAbr>-<NodeId>-<FnType>
      (if (contains? inverted-type-lookup node-abr)
        (if-let [node (-> (eng/components session)
                          :rulebase
                          :id-to-node
                          (get (Long/valueOf ^String node-id)))]
          (if (= ProductionNode (type node))
            [(-> node :production :name)]
            (if-let [production-names (seq (eng/node-rule-names (some-fn :production :query) node))]
              production-names
              ;; This should be un-reachable but i am leaving it here in the event that the rulebase is somehow corrupted
              (throw (ex-info "Unable to determine suitable name from node"
                              {:node node}))))
          (throw (ex-info "Node-id not found in rulebase"
                          {:node-id node-id
                           :simple-name simple-fn-name})))
        (throw (ex-info "Unable to determine node from function"
                        {:name node-fn
                         :simple-name simple-fn-name}))))))

(s/defn inspect-facts :- FactsInspectionSchema
  "Returns a map with all rules and their associated facts in the session.
  - :rules - a map of rule ids to their production nodes
  - :facts - a sequence of maps with the following keys:
    - :fact - the fact inserted
    - :rule-id (optional) - the id of the rule that inserted the fact,
      absent for root facts
    - :bindings (optional) - the bindings used to insert the fact,
      absent for root facts
    - :fact-types - a sequence of fact types associated with the fact,
      including ancestors"
  [session]
  (let [{:keys [memory rulebase get-alphas-fn]} (eng/components session)
        {:keys [fact-type-fn
                ancestors-fn]} (meta get-alphas-fn)
        {:keys [production-nodes]} rulebase
        root-facts (for [fact (get-root-facts session)
                         :let [fact-type (fact-type-fn fact)
                               ancestors (ancestors-fn fact-type)]]
                     {:fact fact
                      :fact-types (cons fact-type ancestors)})
        rule-nodes (for [{:keys [id production]} production-nodes]
                     [id production])
        rule-facts (for [{:keys [id] :as rule-node} production-nodes
                         {:keys [bindings] :as token} (keys (mem/get-insertions-all memory rule-node))
                         insertion-group (mem/get-insertions memory rule-node token)
                         fact insertion-group
                         :let [fact-type (fact-type-fn fact)
                               ancestors (ancestors-fn fact-type)
                               bindings (dissoc-gen-bindings bindings)]
                         :when (and (some? fact)
                                    (not (instance? ISystemFact fact)))]
                     {:fact fact
                      :rule-id id
                      :bindings bindings
                      :fact-types (cons fact-type ancestors)})]
    {:rules (into {} rule-nodes)
     :facts (concat root-facts rule-facts)}))
