# LeanReach

LeanReach is a Lean-native declaration search tool. It is meant to sit next to `rg`: use a name
fragment to find canonical declarations, then inspect the direct upstream and downstream
dependencies of a declaration together with its pretty-printed signature/body and exact source
position.

The implementation follows Loogle's deliberately simple process model, with module-granular
artifacts for local libraries:

- read each built module's `.olean`, `.olean.server`, `.olean.private`, and `.ilean` directly;
- cache a small dependency fragment per module and materialize separate name and relation indexes;
- plan the bounded query from the index, then import only result modules for pretty-printing;
- persist pretty-printed declarations per module, reuse them across roots, and skip imports when cached;
- precompute PP for a complete root in short-lived batched workers with progress checkpoints;
- mark a completed root and load only the PP sidecars selected by each query;
- use Lean's own delaborator and pretty-printer;
- hide compiler-generated declarations using Loogle/doc-gen-style filtering;
- index direct constants mentioned by declaration types and values;
- rank only the requested number of direct dependencies instead of materializing a transitive DAG.

Module fragments and the materialized index are checked against Lake's transitive `depHash`; modules
without Lake traces use Lake's binary hash of all available `.olean` parts. A local rebuild therefore
invalidates only the affected fragments, pretty-printed declarations, and root view. Both directions use
`ConstantInfo.getUsedConstantsAsSet`, which includes the type and the proof or implementation body.

## Build and test

```console
lake build
lake exe leanreach_tests
```

The Mathlib benchmark runs a chain of distinct declaration searches exactly once. Its session uses
an unbuffered binary pipe and synchronous reads so Python thread scheduling is not counted as query
latency. It primes the executable and catalog without pretty-printing a declaration, then compares
a long-lived LeanReach session, one LeanReach process per query, and one `rg` process per query:

```console
python Benchmarks/run.py --stage baseline --append-history
python Benchmarks/plot.py
```

LeanReach is pinned to Lean and Mathlib `v4.32.0`. The executable enables interpreter support
because loading environment extensions at runtime requires it.

On Windows, create a directly runnable distribution containing the native executable and the Lean
runtime DLLs. The package also records the current Lean sysroot so startup does not need to launch
`lean --print-prefix`; if the package is moved to a machine where that path is invalid, LeanReach
falls back to the standard lookup:

```console
pwsh scripts/package.ps1
.lake/build/leanreach-dist/leanreach.exe --help
```

## Usage

```console
# Search names. Exact names, final-name matches, then substrings are ranked in that order.
lake exe leanreach search span_le --limit 10

# Show a declaration with 10 upstream and 10 downstream dependencies.
lake exe leanreach Submodule.span_le

# Machine-readable output.
lake exe leanreach Submodule.span_le --json

# Precompute PP for the detected view. This resumes at the next incomplete module if interrupted.
lake exe leanreach cache

# Or precompute PP only for selected built modules.
lake exe leanreach cache Mathlib.LinearAlgebra.Span.Defs

# A narrower root imports and indexes much less than all of Mathlib.
lake exe leanreach --module Mathlib.LinearAlgebra.Span.Defs Submodule.span_le
```

Important options:

```text
-m, --module MODULE   override automatic local-library and Mathlib detection
-n, --limit N         override both dependency limits, 1 through 1000
-i, --interactive     keep the environment alive and read stdin
-j, --json            JSON, or NDJSON with --interactive
    --profile         report startup and per-query time
```

Lines and columns are one-based. Human output and JSON contain the pretty-printed signature, module
name, absolute source path when available, and selection position. Non-Prop definitions also show
their complete value; structures, classes, and inductives show their fields and constructors.

## Long-lived agent session

Process startup is the dominant PP-hot cost. Agents should reuse one process:

```console
lake exe leanreach --interactive --json --profile
```

Each input line is a declaration name or `search PATTERN`:

```text
search span_le
Submodule.span_le
```

The process emits one compact JSON value per line and flushes stdout after every response. It loads
the dependency index once but does not import Mathlib at startup. Each query loads only its selected
module PP sidecars into the session; only a missing declaration triggers a bounded module import.

On the development Windows machine, nine distinct PP-cached complete-leaf searches had 9.39 ms
median session latency and 100.87 ms median one-shot latency, versus 204.68 ms for `rg`. The first
session result was 25.03 ms; the other eight were 1.56–20.22 ms. A one-shot process is dominated by
Windows loading the Lean runtime DLLs, so agents should keep the NDJSON session alive when possible.

## Web frontend

The frontend follows Loogle's process boundary: a small Python standard-library HTTP server owns
one long-lived `--interactive --json` LeanReach worker. Search and dependency requests therefore
reuse the same index and PP cache without adding a web framework to the Lean executable. Successful
worker responses are forwarded unchanged instead of being parsed and serialized again in Python.
The server uses HTTP/1.1 keep-alive so a browser session also reuses its local TCP connection.

From this checkout:

```console
python Frontend/server.py --project-dir .
```

Or from a packaged distribution while serving another Lake project:

```console
python /path/to/leanreach-dist/Frontend/server.py \
  --project-dir /path/to/project
```

Open `http://127.0.0.1:8088`. Forward root or limit options after `--`, for example
`-- --module Mathlib --limit 20`. The browser uses `/json?q=PATTERN` for name search and
`/json?name=DECLARATION` for dependency navigation.

## Searching another local Lake library

Build LeanReach with the same Lean toolchain as the target project. From the target project's
directory or any of its subdirectories, invoke the packaged binary directly:

```console
/path/to/LeanReach/.lake/build/leanreach-dist/leanreach search my_theorem
```

LeanReach walks upward to the nearest Lake configuration and uses Lake's own package APIs to find
the local `lean_lib` modules. Every module with an existing `.olean` is searchable, so a partial
`lake build` is enough; stale `.olean` files whose source module was removed are ignored, and missing
modules are not built implicitly. If that package directly
`require`s Mathlib, the Mathlib root is included in the same search view. The small discovery result
including Lake's actual `lean_lib` source directories is cached under `.lake` and invalidated by the
Lake configuration hash. Running `cache` refreshes the list of built modules; ordinary queries reuse
that persisted view instead of recursively scanning the build tree in every process.

`--module MyProject` remains available as an explicit override. Without `LEAN_PATH`, LeanReach also
discovers the project and dependency build directories plus their source roots. `lake env` remains
supported for projects with custom Lake build or source directories.

After `lake build`, precompute PP for the complete built root once:

```console
/path/to/leanreach cache
```

This pays index construction, environment import, and pretty-printing once. LeanReach imports only
the modules with missing PP, shares the immutable environment across four bounded module tasks, and
writes one PP sidecar after each completed module. An interruption therefore leaves completed modules
reusable. A small root marker makes later `cache` calls return before loading the catalog, while queries
read only the module sidecars containing their selected declarations. Sidecars are reusable from
larger roots and invalidated by the defining module's build hash; LeanReach never builds missing
modules implicitly. When a detected view combines local roots with Mathlib, a valid completed
Mathlib view is reused without reopening all of its module sidecars, and only modules with missing
PP are imported. On the development Windows machine, rebuilding a combined root marker while reusing
the completed Mathlib view took 1.69 seconds; caching 16 declarations from one missing local module
took 14.56 seconds without importing the separate Mathlib root. The same 64 modules and 982
declarations took 29.9 seconds in two 32-module import waves, 15.3 seconds with one import, and
14.1 seconds with four pretty-print tasks.

The root cache also materializes the current default top ten upstream and downstream results into
hash-partitioned query shards. A view that adds local modules over an already-cached Mathlib stores
only a compact overlay of local declarations and cross-layer reverse edges; it ranks merged
dependencies with the same scoring function instead of copying Mathlib's 132 MB query plan. In the
fixture benchmark this reduced a new combined plan from 101.36 seconds to 359 ms. Dependency queries
by fully qualified name or unique final component therefore read one small plan shard or overlay and
only the selected module PP sidecars; ambiguous final components are reported from the same cache.
Name search also uses these caches for a complete full name or final component while preserving
exact-before-suffix ordering. General substring matching, and dependency limits above ten,
deliberately fall back to the complete index so they preserve the same matching and ranking semantics.
Root dependency hashes are memoized against the modification time and size of every root trace, so a
normal rebuild invalidates the view without reparsing every trace on each query. With the current
Mathlib and local view fully cached, measured internal time was 12 ms for a distinct exact query and
11 ms for a distinct final-component search. The median one-shot wall time was 116 ms because the
Windows process still maps roughly 250 MB of Lean runtime DLLs; interactive mode avoids that fixed
process startup cost.

## Dependency semantics

An edge `A → B` means `ConstantInfo.getUsedConstantsAsSet` for `A` contains `B`, possibly after
collapsing compiler-generated private helpers back into the public declaration. Consequently:

- upstream of `A` contains constants used by its signature and proof or implementation;
- downstream of `B` contains declarations whose signature or body uses `B`;
- there is one relation and one output list per direction, without splitting type and body edges.

The direct relation remains a lightweight navigation aid rather than a materialized transitive DAG
or a runtime call graph.

Only the requested top results are selected. A bounded binary heap avoids sorting a declaration's
entire posting list, which matters for very widely used constants.

## Dependency ranking

Both directions combine mathematical relevance with locality:

- same-module, common namespace, and common module prefixes favor declarations near the target;
- exact final names and shared underscore-separated words connect wrappers such as
  `Nat.Prime.dvd_of_dvd_pow` with `Prime.dvd_of_dvd_pow`;
- upstream uses Lucene's smoothed IDF, favoring specific definitions and lemmas over ubiquitous
  proof plumbing;
- downstream uses `log(1 + df)`, favoring declarations that themselves became reusable APIs.

For an upstream declaration used by `df` of the `N` indexed declarations, the frequency component
is:

```text
log(1 + (N - df + 0.5) / (df + 0.5))
```

This combines the rarity principle from Lean's
[MePo implementation](https://github.com/leanprover/lean4/blob/master/src/Lean/LibrarySuggestions/MePo.lean)
and the original [Meng–Paulson relevance filter](https://www.cl.cam.ac.uk/~lp15/papers/Automation/filtering-jal.pdf)
with [Lucene's smoothed IDF](https://lucene.apache.org/core/9_4_2/core/org/apache/lucene/search/similarities/BM25Similarity.html).

## Layout

```text
LeanReach/Index.lean  names, direct-reference postings, and resolution
LeanReach/Cache.lean  persistent index serialization and freshness checks
LeanReach/BlackListed.lean  generated-declaration filtering
LeanReach/Query.lean  pretty-printing, source locations, and sessions
LeanReach/Project.lean  Lake project and built-module discovery
LeanReach.lean        environment-loading facade
Main.lean             Lake ArgsT CLI and interactive transport
Frontend/             Loogle-style HTTP worker and browser UI
Tests/                local-library fixture and behavior checks
```

The environment lifecycle, disk-cache strategy, and CLI organization are adapted from
[Loogle](https://github.com/nomeata/loogle), which is distributed under Apache-2.0. LeanReach's
dependency relation intentionally also includes proof and implementation bodies.
