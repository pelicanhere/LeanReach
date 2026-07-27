# LeanReach

LeanReach is a Lean-native declaration search tool. It is meant to sit next to `rg`: use a name
fragment to find canonical declarations, then inspect the direct upstream and downstream
dependencies of a declaration together with its pretty-printed signature/body and exact source
position.

The implementation follows Loogle's deliberately simple process model, with module-granular
artifacts for local libraries:

- read each built module's `.olean`, `.olean.server`, `.olean.private`, and `.ilean` directly;
- cache a small dependency fragment per module and materialize a root query index;
- import the root with `loadExts := true` only for pretty-printing;
- keep that `Environment` alive for the whole process;
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

LeanReach is pinned to Lean and Mathlib `v4.32.0`. The executable enables interpreter support
because loading environment extensions at runtime requires it.

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

The default `Mathlib` root is intentionally a much heavier pretty-printing workload. The dependency
index itself is loaded without importing Mathlib, but this version still imports the root before
rendering results. Prefer the narrowest useful root and keep full-Mathlib sessions alive.

## Searching another local Lake library

Build LeanReach with the same Lean toolchain as the target project. From the target project's
directory, run the binary under that project's Lake environment and name an aggregate/root module:

```console
lake env /path/to/LeanReach/.lake/build/bin/leanreach \
  --module MyProject search my_theorem
```

`lake env` supplies both `LEAN_PATH` and `LEAN_SRC_PATH`. The former lets LeanReach import the local
`.olean`s; the latter maps declaration modules back to local `.lean` files, including projects that
use a custom source directory.

## Dependency semantics

An edge `A → B` means `ConstantInfo.getUsedConstantsAsSet` for `A` contains `B`. Consequently:

- upstream of `A` contains constants used by its signature and proof or implementation;
- downstream of `B` contains declarations whose signature or body uses `B`;
- there is one relation and one output list per direction, without splitting type and body edges.

The bounded traversal remains a lightweight navigation aid rather than a materialized transitive
DAG or a runtime call graph.

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
