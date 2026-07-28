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
- persist rendered declarations and skip imports entirely when every result is cached;
- keep a root `Environment` alive only in interactive mode;
- use Lean's own delaborator and pretty-printer;
- hide compiler-generated declarations using Loogle/doc-gen-style filtering;
- index direct constants mentioned by declaration types and values;
- perform bounded breadth-first traversal instead of materializing a transitive DAG.

Module fragments and the materialized index are checked against Lake's transitive `depHash`, so a
local library rebuild invalidates only the affected fragments and root view. Both directions use
`ConstantInfo.getUsedConstantsAsSet`, which includes the type and the proof or implementation body.

## Build and test

```console
lake build
lake exe leanreach_tests
```

The repeatable Mathlib benchmark compares direct process wall time with `rg` and also records
LeanReach's internal query time:

```console
pwsh Benchmarks/run.ps1
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

# Show a declaration and both directions of its direct dependencies.
lake exe leanreach Submodule.span_le --limit 20

# Traverse two hops in one direction.
lake exe leanreach Submodule.span_le --upstream --depth 2

# Rank the most informative declarations in a bounded upstream neighborhood.
lake exe leanreach context Submodule.span_le --depth 2 --limit 20

# Machine-readable output.
lake exe leanreach Submodule.span_le --json

# A narrower root imports and indexes much less than all of Mathlib.
lake exe leanreach --module Mathlib.LinearAlgebra.Span.Defs Submodule.span_le
```

Important options:

```text
-m, --module MODULE   imported root module (default: Mathlib)
-d, --depth N         traversal depth, 0 through 8 (default: 1)
-n, --limit N         results per list, 1 through 1000 (default: 20)
    --upstream        only declarations used by the target
    --downstream      only declarations that use the target
-i, --interactive     keep the environment alive and read stdin
-j, --json            JSON, or NDJSON with --interactive
    --profile         report startup and per-query time
```

Lines and columns are one-based. Human output and JSON contain the pretty-printed signature, module
name, absolute source path when available, and selection position. Non-Prop definitions also show
their complete value; structures, classes, and inductives show their fields and constructors.

## Long-lived agent session

Importing a complete Lean environment is the expensive part. Agents should reuse one process:

```console
lake exe leanreach --interactive --json --profile
```

Each input line is a declaration name, `search PATTERN`, or `context DECLARATION`:

```text
search span_le
Submodule.span_le
context Submodule.span_le
```

The process emits one compact JSON value per line and flushes stdout after every response. On the
development Windows machine, a small cached local environment took about 10 seconds to start; the
first name search and pretty-print took 89 ms, and the following dependency query took 7 ms.

The dependency index is loaded without importing Mathlib. A one-shot command imports only the
modules needed to render its bounded result set; interactive mode imports the root once and reuses
it. Prefer a one-shot command for isolated lookups and a long-lived session for a sequence of
queries over the same root.

## Searching another local Lake library

Build LeanReach with the same Lean toolchain as the target project. From the target project's
directory, invoke the packaged binary and name an aggregate/root module:

```console
/path/to/LeanReach/.lake/build/leanreach-dist/leanreach \
  --module MyProject search my_theorem
```

Without `LEAN_PATH`, LeanReach discovers the current project's default `.lake/build/lib/lean`,
dependency build directories under `.lake/packages`, package roots, and common `src` directories.
`lake env` remains supported for projects with custom Lake build or source directories.

## Dependency semantics

An edge `A → B` means `ConstantInfo.getUsedConstantsAsSet` for `A` contains `B`. Consequently:

- upstream of `A` contains constants used by its signature and proof or implementation;
- downstream of `B` contains declarations whose signature or body uses `B`;
- there is one relation and one output list per direction, without splitting type and body edges.

The bounded traversal remains a lightweight navigation aid rather than a materialized transitive
DAG or a runtime call graph.

Direct dependencies are ordered once while building the relation index. Declarations from the same
module and nearby namespaces come first; ties prefer rarer upstream symbols and more widely reused
downstream declarations. This keeps generic proof plumbing below definitions and lemmas local to
the target without maintaining a heavier graph.

## Ranked context

`context` selects informative upstream declarations without an embedding model or a complete DAG.
For a declaration used by `df` of the `N` indexed declarations, its score starts with Lucene's
smoothed IDF:

```text
log(1 + (N - df + 0.5) / (df + 0.5))
```

The score is multiplied by `0.5^(distance - 1)`. Direct dependencies are all considered; deeper
layers expand only the 16 highest-scoring declarations from the previous layer and stop after
examining 256 edges. The output includes score, distance, and `df` so an agent can explain why a
declaration was selected. This combines the rarity principle from Lean's
[MePo implementation](https://github.com/leanprover/lean4/blob/master/src/Lean/LibrarySuggestions/MePo.lean)
and the original [Meng–Paulson relevance filter](https://www.cl.cam.ac.uk/~lp15/papers/Automation/filtering-jal.pdf)
with [Lucene's smoothed IDF](https://lucene.apache.org/core/9_4_2/core/org/apache/lucene/search/similarities/BM25Similarity.html).

## Layout

```text
LeanReach/Index.lean  names, direct-reference postings, and resolution
LeanReach/Cache.lean  persistent index serialization and freshness checks
LeanReach/BlackListed.lean  generated-declaration filtering
LeanReach/Rank.lean  bounded expansion and symbol-rarity ranking
LeanReach/Query.lean  rendering, source locations, traversal, and sessions
LeanReach.lean        environment-loading facade
Main.lean             Lake ArgsT CLI and interactive transport
Tests/                local-library fixture and behavior checks
```

The environment lifecycle, disk-cache strategy, and CLI organization are adapted from
[Loogle](https://github.com/nomeata/loogle), which is distributed under Apache-2.0. LeanReach's
dependency relation intentionally also includes proof and implementation bodies.
