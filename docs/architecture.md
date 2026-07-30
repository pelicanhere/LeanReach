# LeanReach architecture

LeanReach is optimized for short declaration-navigation queries over artifacts that Lake has already
built. It deliberately avoids embeddings, a materialized transitive DAG, and source-text parsing.
Lean remains the authority for declaration identity, dependency extraction, pretty-printing, and
source positions.

## Query pipeline

```text
Lake project discovery
  → module fragments
  → catalog + direct relation index
  → name resolution
  → upstream/downstream candidate lookup
  → dependency ranking
  → selected PP sidecars or bounded live PP
  → human or JSON output
```

Name matching, graph lookup, mathematical ranking, and pretty-printing are separate stages. Changing
substring matching therefore does not alter dependency scores, and changing a score does not affect
exact-name resolution.

The three query stages reuse `Neighborhood α`: cached plans contain located names, PP plans contain
Lean names, and output contains rendered declarations.

## Dependency semantics

For a declaration `A`, LeanReach calls `ConstantInfo.getUsedConstantsAsSet` on the complete
`ConstantInfo`. An edge `A → B` means that `A`'s type, proof, or implementation uses `B`.

- Upstream of `A` is the set of direct outgoing neighbors.
- Downstream of `B` is the set of declarations with a direct edge to `B`.
- Type and value dependencies are intentionally presented as one relation.
- Compiler-generated or private helpers are transitively collapsed back to their public
  dependencies.

The complete private `.olean` layer is required while extracting fragments because exported and
server layers may omit opaque theorem values. Searchable public declarations are filtered with
`.ilean` definitions and a small generated-name blacklist.

This graph is a navigation index, not a runtime call graph and not a transitive proof-dependency DAG.

## Name matching

The catalog is sorted by full Lean `Name`. For a search string, results are grouped in this order:

1. case-insensitive complete name;
2. final name component;
3. general substring.

Queries of at least three characters use the rarest available trigram posting. Shorter queries scan
the compact name table. Cached and in-memory searches use the same bounded bucket collector.

Exact dependency queries first try a case-sensitive complete `Name`. A unique final component can be
resolved from a query shard; otherwise LeanReach loads the complete catalog to preserve ambiguity
reporting.

## Dependency ranking

Ranking operates only on the direct neighbors of the target. It does not inspect declaration kinds
and has no theorem, instance, projection, or name blacklist branches.

For a candidate used by `df` of `N` indexed declarations and itself using `out` declarations:

```text
specificity = log(1 + (N - df + 0.5) / (df + 0.5))
substance   = 4 out / (out + df + 8)
upstream    = specificity · df / (df + 0.5) + substance
downstream  = log(1 + df) + substance
```

The graph prior is multiplied by `1 + locality / 8`. Locality combines:

- the same defining module;
- common declaration namespace;
- common module namespace;
- Dice similarity between underscore-separated final-name tokens of length at least three.

Candidate priors are computed with the relation index. A bounded binary heap selects the requested
Top-K without sorting a widely used declaration's entire reverse posting. Equal scores are ordered
by Lean `Name`.

The relevance design draws on Lean's
[MePo implementation](https://github.com/leanprover/lean4/blob/master/src/Lean/LibrarySuggestions/MePo.lean),
the [Meng–Paulson relevance filter](https://www.cl.cam.ac.uk/~lp15/papers/Automation/filtering-jal.pdf),
and [Lucene's smoothed IDF](https://lucene.apache.org/core/9_4_2/core/org/apache/lucene/search/similarities/BM25Similarity.html).

## Persistent cache layers

Object caches use Lean module data; exact-query shards and small markers use compact text. Cache
files live beside an `.olean`, which lets a dependency provide reusable artifacts to downstream
Lake projects.

### Module fragment

`Cache.Index` stores, per module:

- imports;
- searchable public declaration names;
- direct used-constant sets after private-helper collapse.

The sidecar is keyed by the module's Lake `depHash`. Without a Lake trace, LeanReach hashes all
available `.olean` layers.

### Catalog and relations

A root view materializes:

- a name-to-module catalog and trigram postings;
- forward and reverse declaration-ID arrays;
- precomputed upstream and downstream graph priors.

Catalog and relations are separate files so name search need not map the full graph.

### Search cache

The disk name index has a compact declaration/module table, a trigram-frequency directory, and 256
posting shards. Posting IDs are delta-varint encoded in `ByteArray`s. A query maps only the selected
posting shard and the name table.

### Query cache and local overlay

The default Top-10 upstream and downstream results are stored in 1024 exact-query shards. Limits
above 10 fall back to the complete relation index.

When a view combines built local modules with Mathlib, Mathlib is the stable base and
`Cache.Overlay` stores only:

- local declarations and their outgoing edges;
- reverse edges from base or local declarations into the local layer.

The overlay ranks merged base and local candidates with the same `Rank.select` implementation. It
does not copy the full Mathlib query plan.

### Pretty-print cache

The PP cache stores a `NameMap Declaration` per defining module. A root marker records that all modules
in a view have complete PP sidecars. A valid partial sidecar can be resumed declaration by
declaration; changing the module hash invalidates that module as a unit.

`Cache.Build` owns cache construction and worker scheduling. Four persistent workers share one
immutable imported environment by default. Each completed module is checkpointed immediately.

## Pretty-printing

Signatures use Lean's own `PrettyPrinter.ppSignature`. Non-Prop definitions additionally use
`PrettyPrinter.ppExpr` for their values. Theorems and other Prop-valued declarations never traverse
proof values during PP.

Private constants needed by a public signature or body are added to a temporary environment overlay.
Structure fields and constructors share a module-local signature memo. Declarations retain source
order to keep generated meta names as deterministic as Lean permits.

Source positions come from `.ilean` selection ranges. Files are found through the current Lake
project, dependency source roots, and the Lean sysroot source tree.

`cache --profile` reports:

- root import;
- private overlay preparation;
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
- Mathlib plus local query view: persistent Mathlib base plus a regenerated local overlay;
- root catalog and relations: per ordered root view.

The detected built-module list is persisted under the target project's `.lake`. Running
`leanreach cache` refreshes it; ordinary queries reuse it for fast process startup. Consequently, a
newly built module may require one `cache` command before automatic detection includes it. Local
roots are stored in a canonical order so filesystem enumeration cannot invalidate aggregate caches.

## Runtime model

One-shot queries avoid importing a root environment when every selected declaration is already
pretty-printed. PP-cold queries import only the modules required for the selected result.

Interactive mode keeps the dependency index and in-memory PP map alive across commands. This avoids
repeated Lean runtime startup and is the intended interface for agents performing a search chain.

The remaining cold-cache cost is primarily Lean signature delaboration and formatting. Stable
Mathlib sidecars should be built once and reused; changed local modules are generated incrementally.

## Source layout

```text
LeanReach/Search/Types.lean           shared located-name and neighborhood models
LeanReach/Search/Name.lean            reusable Lean name decomposition
LeanReach/Search/Match.lean           matching and bounded result buckets
LeanReach/Search/Rank.lean            dependency scoring and Top-K selection
LeanReach/Search/Index.lean           catalog, direct graph, and lookup
LeanReach/Runtime/Project.lean        Lake project and built-module discovery
LeanReach/Runtime/Environment.lean    search paths, imports, and CoreM execution
LeanReach/Runtime/ModuleData.lean     `.olean` layers and private overlays
LeanReach/Runtime/Source.lean         `.ilean` declaration locations
LeanReach/PrettyPrint/Declaration.lean cached and JSON declaration model
LeanReach/PrettyPrint/Timing.lean      PP stage measurements
LeanReach/PrettyPrint/Printer.lean     Lean declaration formatting
LeanReach/PrettyPrint/Module.lean      module PP environment preparation
LeanReach/Cache/Storage.lean           persistence and root fingerprints
LeanReach/Cache/Index.lean             module fragments and graph indexes
LeanReach/Cache/Search.lean            sharded substring-search persistence
LeanReach/Cache/Overlay.lean           local graph overlay
LeanReach/Cache/Query.lean             exact-query shards and routing
LeanReach/Cache/PrettyPrint.lean       module PP sidecars
LeanReach/Cache/Build.lean             cache workers and orchestration
LeanReach/Query.lean                   cross-layer query construction
LeanReach.lean                         public session orchestration
Main.lean                              CLI and output
```

## Benchmark discipline

`Benchmarks/run.py` compares a chain of distinct searches. It does not report repeated lookup of one
name as first-use latency. The current harness uses the packaged Windows executable; run
`pwsh scripts/package.ps1` and precompute `leanreach.exe cache` first. A fair cached comparison:

1. builds the complete LeanReach cache beforehand;
2. primes executable and catalog startup without querying a benchmark declaration;
3. uses distinct names once each;
4. compares a long-lived LeanReach session, fresh LeanReach processes, and fresh `rg` processes;
5. records every sample in `Benchmarks/history.csv`.

`Benchmarks/plot.py` renders the history as a logarithmic scatter plot with median markers.
