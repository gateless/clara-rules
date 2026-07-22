(ns clara.rules.activation-cache.core
  "Support for caching the output of rule right-hand-side (RHS) activations
  so it can be replayed across rules sessions instead of recomputed.

  The engine consults a cache the caller supplies via the `:cache` fire-rules
  option: an atom wrapping any `clojure.core.cache/CacheProtocol` implementation.
  A rule opts in via its own `:cache` prop. This namespace provides
  `build-cache-key`, which derives the key an activation is cached under. Any
  policy beyond basic lookup/hit/miss — TTL, tracking which entries were
  consulted, sweeping at the end of a run — is the responsibility of the caller's
  cache implementation.")

(defn build-cache-key
  "Builds an activation cache key for the given activation (a map with `:node` and
  `:token`).

  The key is the data the RHS output depends on: the rule's environment, name,
  props, and the bindings it fired on. The rule name and namespace version are
  already encoded in the rule's `:name`/`:props` by the caller, so this key
  changes exactly when the rule logic or its inputs change. The full bindings are
  stored (not a hash) so a deserialized key compares `=` to a freshly-computed
  one with no chance of collision."
  [{:keys [node token]}]
  (let [{:keys [production]} node
        {:keys [bindings]} token
        rule-name (:name production)
        rule-env (or (:env production) {})
        rule-props (or (:props production) {})]
    {:env rule-env
     :name rule-name
     :props rule-props
     :bindings bindings}))
