# Changes in gateless/clara-rules vs. upstream cerner/clara-rules

This document inventories the high-level changes in the `gateless/clara-rules` fork
since it diverged from upstream cerner/clara-rules, as of 2026-05-01.

## Summary

- **JVM-only.** ClojureScript support was dropped in favor of focusing on the JVM target.
- **Async + parallel rule firing.** New `fire-rules-async` API, `:parallel-batch-size`
  for parallel RHS execution, and interruptible sessions, all built on
  `gateless/futurama` instead of `core.async`.
- **Read-only and query-only sessions.** New session types and durability options
  for fast deserialization when only queries or inspection are needed.
- **Pluggable caching.** Session and expression compilation are both backed by
  `core.cache` `CacheProtocol` instances and can be swapped or cleared.
- **`ham-fisted` performance rewrite.** Working memory, beta graph, update caches,
  and Fressian durability use ham-fisted mutable collections.
- **DSL additions.** `defhierarchy` macro, namespace-level rule properties,
  `IClaraSource` protocol replacing `IRuleSource`, function-as-rule-source support,
  and `&env` capture in rule/query macros.
- **Richer inspection.** Root-fact tracking, new `inspect-facts`, and
  `:fact->explanations` in the inspect output.
- **New accumulators.** `sorting-by`, `sorted-grouping-by`, and a safe-default
  `acc/sum`.
- **Tooling overhaul.** Migrated from Leiningen to `deps.edn` + `tools.build`,
  Kaocha for tests, GraalVM native-image smoke build, and republished as
  `com.github.gateless/clara-rules` on Clojars.

---

## 1. Async / parallel rules engine
- **`fire-rules-async`** added as a first-class API (`clara.rules.clj`,
  `engine.clj`). Returns a `CompletableFuture` and supports awaiting RHS that
  return futures/channels/deferreds. New `:parallel-batch-size` option pops N
  activations at once.
- Engine refactored into separate sync vs async firing paths:
  `fire-activation!` / `fire-activation-async!`, `fire-activations!` /
  `fire-activations-async!`, `process-activations!`, `do-fire-rules` macro.
- Replacement of `core.async` with **`gateless/futurama`** (own library) as the
  async primitive; pinned to 1.4.2.
- **`pop-activation!` → `pop-activations! [memory count]`** in `IMemoryReader`
  (breaking change for custom memories) to support batch pops.
- **Interruptible sessions** via `futurama/async-cancelled?` checks inside the
  activation loop — runaway/infinite loops can be cancelled. Tests in
  `test_infinite_loops.clj`.
- ClojureScript support **dropped**.

## 2. Read-only and query-only sessions
- New `ReadOnlyLocalSession` deftype that throws on insert/retract/fire-rules.
- New session assembly entry points: `assemble-read-only`, `as-read-only`,
  `assemble-query-only`, `as-query-only`, `rulebase->query-only-rulebase`,
  `memory->query-only-beta-memory`.
- New durability options `:read-only?` and `:query-only?` on
  `serialize-session-state` / `deserialize-session-state`. Read-only sessions
  skip RHS/alpha/test/join-filter/accum compilation (uses `com/read-only-expr`
  stub).
- Compiler stripping helpers for serialization: `rem-rhs-fn`, `rem-alpha-fn`,
  `rem-join-filter-fn`, `rem-test-fn`, `rem-accumulator`,
  `reconstruct-node-expr-fn-lookup`.
- New `IMemoryReader/get-tokens-map` protocol method to fetch full beta-memory
  state.

## 3. Caching layer
- **Pluggable session cache**: `:cache` on `mk-session` now accepts
  `true`/`false`/any `core.cache` `CacheProtocol`. Default is an LRU cache.
- **New `:compiler-cache` option** on `mk-session` for memoizing expression
  compilation; default is a soft-reference cache.
- Public helpers `clear-session-cache!` and `clear-compiler-cache!`.
- New `:hash-expr-fn` option for deterministic, MD5-based cache keying.

## 4. ham-fisted-based performance rewrite
- `ham-fisted` introduced as a core dep (currently 3.006). Used pervasively in:
  - **Compiler**: beta graph (`forward-edges`/`backward-edges`/
    `id-to-condition-node`/`id-to-production-node`/`id-to-new-bindings`) is now
    a `MutableLongHashMap` instead of a sorted Clojure map. Schema in
    `schema.clj` was updated accordingly.
  - **Memory** (`memory.clj` was rewritten — 533-line diff): TransientLocalMemory
    uses ham-fisted mutable maps (`MutableMap`) for alpha/beta/accum/production
    memory and replaces `compute!`-based ops everywhere; `LinkedList` helpers
    retained for hot paths.
  - **Update caches**: `OrderedUpdateCache` rebuilt around `IMutList`;
    `CancellingUpdateCache` simplified to use ham-fisted's
    `compute-if-absent!`/`apply-concat`.
  - **Fressian durability**: new `hamf/set` and `hamf/map` Fressian handlers so
    deserialized sessions retain ham-fisted collection types.
- Many micro-optimizations: persistent collection initialization, transient
  prod-memory ops via `compute`, simplified equality wrappers, etc.

## 5. Rule / query / hierarchy DSL changes
- **Breaking renames**:
  - Protocol `IRuleSource/load-rules` → **`IClaraSource/load-source`**.
  - `clear-ns-productions!` → **`clear-ns-vars!`**.
- **`defhierarchy`** macro added — defines a `make-hierarchy` derive chain in a
  var; integrates with `mk-session`'s new `:hierarchy` option and
  `create-ancestors-fn`.
- **`defrule` rewritten**: now expands to a `defn` with three arities (no-args
  returns rule map; full args is the compiled RHS handler). Rule's `:handler`
  field stores a symbol pointing at the compiled function. Var serialization
  support added (`clojure.lang/var` Fressian handler) so handlers serialize via
  symbol.
- `clojure.lang.Fn` now implements `IClaraSource` (you can pass functions as
  rule sources and they're invoked to produce rules).
- `=>` separator is now optional when there's no LHS.
- `defrule`/`defquery`/`parse-rule`/`parse-query` now capture `&env` (local
  lexical env) and `&form` metadata. Fixes env not being available in
  expression/accumulator join nodes.
- **Namespace-level rule properties**: `dsl/get-ns-props`,
  `dsl/add-allowed-ns-props!`, `dsl/set-allowed-ns-props!`. Defaults to
  `:author :no-loop :salience` — set ns metadata `^{:salience 100}` and rules
  in that namespace inherit it.

## 6. Sum / sort accumulators
- `acc/sum`: `:default-value` kw-arg (defaults to 0) so nil fields no longer NPE.
- New **`sorting-by`** accumulator (sort-by with optional comparator and
  convert-return-fn).
- New **`sorted-grouping-by`** accumulator (groups + sorts both groups and
  within-group; result is an `array-map` for ordering preservation).
- `grouping-by` private helper extracted.

## 7. Inspection enhancements
- `InspectionSchema` renamed → **`RulesInspectionSchema`**; new
  **`FactsInspectionSchema`**.
- New top-level fields in `inspect`: **`:root-facts`** and
  **`:fact->explanations`**.
- New **`get-root-facts`** and **`inspect-facts`** functions; root facts are
  now memorized in working memory (new `ROOT_NODE`, `ROOT_NODE_ID`,
  `->RootElement`).
- `get-condition-matches`, `to-explanations`, `gen-all-rule-matches`,
  `gen-fact->explanations`, `explain-activation` made public.
- Generated-binding (`?__gen__`) removal from inspect bindings results.
- **`PendingUpdate` operation types renamed**: `:insertion` → `:insert`,
  `:retraction` → `:retract`.

## 8. Loop detector
- `CyclicalRuleListener.to-persistent!` now returns the cycles count instead
  of nil — useful for telemetry on hit limits.

## 9. Durability internals
- Switched from JVM `ThreadLocal`s to **dynamic vars**
  (`*node-id->node-cache*`, `*node-fn-cache*`, `*clj-struct-holder*`,
  `*mem-facts*`, `*mem-internal*`) — done so async/virtual threads work safely.
- Use of `with-thread-local-binding` macro replaced with `binding`.
- New Fressian handler for `clojure.lang.Var`.
- `JavaEqualityWrapper` got an identity-first short-circuit and `(==hash)`
  short-circuit. New helpers `jeq-wrap`/`jeq-unwrap`. New `FactIdentityWrapper`
  deftype with `fact-id-wrap`/`fact-id-unwrap` (used by inspection root-fact
  diffing).
- `compute-for` macro added in `platform.clj`.

## 10. Listener
- `null-listener?` now treats `nil` as null (defensive against missing
  listener).
- New `combine-listeners` helper that returns the default null listener for
  empty collections vs. a delegating listener otherwise.

## 11. Tooling, build, ops
- **GraalVM native-image test build target**: new `app/clara/main.clj` and Makefile
  `build-native` target verifying that a clara-rules app compiles to a native binary.
- Project moved from `cerner/clara-rules` to **`com.github.gateless/clara-rules`**
  on Clojars; pom, README badge, namespace updated.
- README: stripped ClojureScript references, added YourKit attribution,
  fork-specific issue link, Clojure-only support disclaimer.
- Move from Leiningen/`project.clj` patterns to **deps.edn + tools.build**
  (`tool/build.clj`); Makefile drives all flows; Kaocha test runner replaces
  lein-test (`bin/kaocha`, `tests.edn`, junit-xml/cloverage support).
- `dev/user.clj` significantly expanded with REPL scaffolding (added Portal
  viewer support, slf4j logging deps).
- Clojure version bumped to **1.12.4**; clj-kondo hook config updated for new
  macros (`defhierarchy`, `clear-ns-vars!`, etc.).
- New test files: `test_engine.clj`, `coverage_ruleset.clj`/`test_coverage.clj`
  (validates instrumentation works), `long_running_tests.clj` parallel options.
- `testing-utils`: added `test-compile-async-action` and
  `test-fire-rules-async` helpers.

## 12. Compiler internals
- New public surface: `read-only-expr`, `mk-node-fn-name`,
  `compile-action-handler` (separated from `compile-action`), `build-rule-node`,
  `create-get-alphas-fn` (was private), `create-ancestors-fn`,
  `alpha-roots-wrap`, `load-source*`.
- `effective-type` and `get-fields` now memoized.
- `AlphaRootsWrapper` deftype simplified (now wraps `JavaEqualityWrapper`
  directly instead of carrying its own hash).
- `:omit-compile-ctx` plumbing for serialization.
- Rulebase/session compilation deterministic-sorts productions before hashing.
