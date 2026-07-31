# LeanReach architecture

LeanReach is optimized for short declaration-navigation queries over artifacts that Lake has already
built. It deliberately avoids embeddings, a materialized transitive DAG, and source-text parsing.
Lean remains the authority for declaration identity, dependency extraction, pretty-printing, and
source positions.

## Query pipeline

```text
Lake project discovery
  → module fragments
  → shared declaration table + sharded direct adjacency
  → name resolution
  → upstream/downstream candidate lookup
  → dependency ranking
  → selected PP sidecars or bounded live PP
  → human or JSON output
```

Name matching, graph lookup, mathematical ranking, and pretty-printing are separate stages. Changing
pattern matching therefore does not alter dependency scores, and changing a score does not affect
exact-name resolution.

Across these stages, `Neighborhood α` carries located names in cached plans, Lean names in PP
plans, and rendered declarations in output.

## Dependency semantics

For a declaration `A`, LeanReach calls `ConstantInfo.getUsedConstantsAsSet` on the complete
`ConstantInfo`. An edge `A → B` means that `A`'s type, proof, or implementation uses `B`.

- Upstream of `A` is the set of direct outgoing neighbors.
- Downstream of `B` is the set of declarations with a direct edge to `B`.
- Type and value dependencies are intentionally presented as one relation.
- Non-source implementation details are transitively collapsed back to their source declarations.

The complete private `.olean` layer is required while extracting fragments because exported and
server layers may omit opaque theorem values. Searchable source declarations, including explicit
private declarations, are selected from `.ilean` definitions; generated implementation details are
filtered separately.

This graph is a navigation index, not a runtime call graph and not a transitive proof-dependency DAG.

## Name matching

A complete, case-sensitive declaration name selects dependency navigation. Otherwise the same
input is compiled as an unanchored, case-sensitive regex. Cached and in-memory execution use the
same final matcher.

The pattern AST yields only trigrams proven to occur on every successful path. Each regex
alternative selects its rarest posting, the selected postings are merged, and the complete regex is
then checked. Patterns without a safe trigram scan the compact cached name table. Limits are applied
only after the complete match.

Mode selection uses only a complete kernel name or complete user-visible private name. Suffix and
substring uniqueness never change the command mode: agents search first, then copy a returned
complete name to navigate its dependencies.

## Dependency ranking

Ranking operates only on the direct neighbors of the target. It does not inspect declaration kinds
and has no theorem, instance, projection, or name blacklist branches.

For each candidate, `users` is the number of indexed declarations that use it, `dependencies` is
the number it uses, and `N` is the total number of indexed declarations. The graph prior has three
components:

```text
specificity = log(1 + (N - users + 0.5) / (users + 0.5))
confidence  = users / (users + 0.5)
substance   = 4 dependencies / (dependencies + users + 8)

upstreamPrior   = specificity · confidence + substance
downstreamPrior = log(1 + users) + substance
```

The affinity term is:

```text
affinity =
  (3 sameModule + 3 declarationNamespace + 2 moduleNamespace + 4 leafTokens) / 8

score = graphPrior · (1 + affinity)
```

The three similarities are Dice scores. `leafTokens` compares underscore-separated final-name
tokens of length at least three. Keeping the graph prior and affinity separate makes the formula
and its cache boundary explicit.

Candidate priors are computed with the relation index. A bounded binary heap selects the requested
Top-K without sorting a widely used declaration's entire reverse posting. Equal scores are ordered
by Lean `Name`.

The relevance design draws on Lean's
[MePo implementation](https://github.com/leanprover/lean4/blob/master/src/Lean/LibrarySuggestions/MePo.lean),
the [Meng–Paulson relevance filter](https://www.cl.cam.ac.uk/~lp15/papers/Automation/filtering-jal.pdf),
the [probabilistic IDF derivation behind BM25](https://www.staff.city.ac.uk/~sbrp622/papers/foundations_bm25_review.pdf),
and [Lean premise-selection experiments](https://arxiv.org/abs/2304.00994).

A 20-query graded ablation also tested log-frequency-only priors, normalized IDF, direct-dependency
symbol overlap, the original MePo quotient, equal-weight affinity, and locally tuned affinity
weights. Several improved development-set Recall@5, but every simplified replacement reduced
held-out NDCG or Recall@10. The production formula therefore keeps the validated signals without
adding theorem/instance branches, name blacklists, a second-order graph pass, or learned state.

## Persistent cache layers

Module fragments and exact-query shards use compact binary formats. The remaining structured
caches use Lean module data, and small markers use text. Cache files live beside an `.olean`, which
lets a dependency provide reusable artifacts to downstream Lake projects.

### Module fragment

`Cache.Fragment` stores, per module:

- imports;
- searchable declaration names, including user-written private declarations;
- direct used-constant arrays after private-helper collapse.

Names share a parent-first module dictionary, and imports, declarations, and edges use varint
dictionary references. Sidecars are content-addressed by the emitted `.olean` layer hashes, so a
transitive Lake dependency-hash change does not rebuild an unchanged fragment. Without output
metadata, LeanReach hashes the available `.olean` layers directly.

### Search cache

The shared declaration table stores sorted names, module ownership, the module list, and direct
forward/reverse degree counts. Search adds a trigram-frequency directory and 256 posting shards.
Posting IDs are delta-varint encoded in `ByteArray`s. A regex query reads the table and only the
selected posting shard.

### Query cache and local overlay

Complete direct upstream and downstream ID arrays are split across 1024 exact-query shards. IDs and
counts use UInt32 varints; each shard validates its own dependency hash before use. Exact queries
read one shard. The default ten results are pre-ranked in place; wider requests rank the complete
neighborhood on demand. Arbitrary limits therefore do not require a persisted root graph.

When a view combines built local modules with Mathlib, Mathlib is the stable base and
`Cache.Overlay` stores only:

- local declarations and their outgoing edges;
- reverse edges from base or local declarations into the local layer.

The overlay reuses the base declaration table rather than copying names, modules, or degree counts.
Regex search reads an immutable local-name catalog; an exact hit builds a separate local
forward/reverse relation sidecar, reads one base query shard, and patches that neighborhood on
demand. Once both overlay parts exist, LeanReach keeps them as an immutable snapshot. Changed
modules append declaration-level, `Name`-keyed deltas; bounded chains or substantial churn trigger
compaction into a new snapshot, after which obsolete artifacts are removed.

### Pretty-print cache

The PP cache stores a `NameMap Declaration` per defining module. A root marker records that all
modules in a view have complete PP sidecars. A valid partial sidecar can be resumed declaration by
declaration; changing the module hash invalidates that module as a unit. Loaded sidecars are reused
within a process and revalidated before an incremental merge.

`Cache.Build` owns cache construction and worker scheduling. Four persistent workers share one
immutable imported environment by default. Each completed module is checkpointed immediately.

## Pretty-printing

Signatures use Lean's own `PrettyPrinter.ppSignature`. Non-Prop definitions additionally use
`PrettyPrinter.ppExpr` for their values. Theorems and other Prop-valued declarations never traverse
proof values during PP.

Private constants needed by a public signature or body are added to a temporary environment overlay.
Structure fields and constructors share a module-local signature memo. Declarations retain source
order to keep generated meta names as deterministic as Lean permits.

Source positions use Lean declaration ranges when available and `.ilean` selection ranges as a
fallback. Files are found through the current Lake project, dependency source roots, and the Lean
sysroot source tree.

`cache --profile` reports:

- root import;
- private overlay preparation;
- source lookup and PP planning;
- signature PP;
- body PP;
- sidecar writes.

Worker-stage values are accumulated work time and may overlap in wall time.

## Local incrementality

Project discovery includes only local source modules with existing `.olean` files. A partially built
library is therefore useful immediately, and LeanReach never invokes `lake build` implicitly.

The current granularity is:

- module fragments: per module hash;
- PP: per module hash, resumable within one valid sidecar;
- Mathlib plus local query view: persistent Mathlib base plus a local snapshot;
- local overlay catalog and relations: module-output fingerprints plus incremental deltas.

The detected built-module list is persisted under the target project's `.lake`. Running
`leanreach cache` refreshes it; ordinary queries reuse it for fast process startup. Consequently, a
newly built module may require one `cache` command before automatic detection includes it. Local
roots are stored in a canonical order so filesystem enumeration cannot invalidate aggregate caches.

## Runtime model

One-shot queries avoid importing a root environment when every selected declaration is already
pretty-printed. PP-cold queries import only the modules required for the selected result.

Interactive mode keeps loaded declaration tables, query shards, and PP maps alive across commands.
This avoids repeated Lean runtime startup and is the intended interface for agents performing a
search chain.

The remaining cold-cache cost is primarily Lean signature delaboration and formatting. Stable
Mathlib sidecars should be built once and reused. Local module fragments and PP sidecars are reused
per module; an edited module updates the local overlay without rematerializing the unchanged graph.

## Test projects

The root package and its default tests do not depend on Mathlib. `Tests/Mathlib` is a standalone
Lake project that requires the repository by path and owns the Mathlib cache, ranking, PP, and
overlay integration suite. Its build directory is local to that project, while its package
directory reuses the repository's existing Lake packages.

## Source layout

```text
LeanReach/Search/Types.lean           shared located-name and neighborhood models
LeanReach/Search/Match.lean           exact matching, name normalization, and trigrams
LeanReach/Search/Pattern.lean         regex compilation and candidate plans
LeanReach/Search/Rank.lean            dependency scoring and Top-K selection
LeanReach/Search/TopK.lean            bounded heap selection
LeanReach/Search/Index.lean           catalog, direct graph, and lookup
LeanReach/Runtime/Project.lean        Lake project and built-module discovery
LeanReach/Runtime/Environment.lean    search paths, imports, and CoreM execution
LeanReach/Runtime/ModuleData.lean     `.olean` layers and private overlays
LeanReach/Runtime/Source.lean         `.ilean` declaration locations
LeanReach/PrettyPrint/Declaration.lean cached and JSON declaration model
LeanReach/PrettyPrint/Timing.lean      PP stage measurements
LeanReach/PrettyPrint/Printer.lean     Lean declaration formatting
LeanReach/PrettyPrint/Module.lean      module PP environment preparation
LeanReach/Cache/Codec.lean             binary varints and decoder cursor
LeanReach/Cache/Fragment.lean          compact module-fragment encoding
LeanReach/Cache/Storage.lean           persistence and root fingerprints
LeanReach/Cache/Index.lean             `.olean` extraction and graph materialization
LeanReach/Cache/Search.lean            sharded regex candidate persistence
LeanReach/Cache/Overlay.lean           local graph overlay
LeanReach/Cache/OverlayDelta.lean      local snapshot deltas and compaction
LeanReach/Cache/Query.lean             exact-query shards and routing
LeanReach/Cache/PrettyPrint.lean       module PP sidecars
LeanReach/Cache/Build.lean             cache workers and orchestration
LeanReach/Query.lean                   cross-layer query construction
LeanReach.lean                         public session orchestration
Main.lean                              CLI and output
Tests/Unit.lean                        storage, codec, index, and regex units
Tests/Session.lean                     interactive query contracts
Tests/Layout/Test.ps1                  custom Lake layout integration
Tests/Main.lean                        test runner
Tests/Mathlib/                          standalone Mathlib integration project
```

## Benchmark discipline

`Benchmarks/run.py` compares a fixed regression corpus. Each pattern occurs once per measured
process or interactive session, but the corpus intentionally repeats across commits; these numbers
measure regressions, not globally cold first-use queries. The harness uses the platform executable
under `.lake/build/bin`; run `lake build` and precompute `leanreach cache` first.

It primes both tools without querying a corpus declaration, uses low-cardinality patterns, compares
a long-lived LeanReach session with fresh LeanReach and `rg` processes, and records every sample in
`Benchmarks/history.csv`. Separate blind agent trials use previously unqueried theorem prompts to
measure end-to-end discovery.

`Benchmarks/plot.py` renders the history as a logarithmic scatter plot with median markers.
