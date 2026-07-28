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
- persist rendered declarations per module, reuse them across roots, and skip imports when cached;
- pre-render a complete root in bounded module batches with module-level checkpoints;
- keep a root `Environment` alive only in interactive mode;
- use Lean's own delaborator and pretty-printer;
- hide compiler-generated declarations using Loogle/doc-gen-style filtering;
- index direct constants mentioned by declaration types and values;
- rank only the requested number of direct dependencies instead of materializing a transitive DAG.

Module fragments and the materialized index are checked against Lake's transitive `depHash`; modules
without Lake traces use Lake's binary hash of all available `.olean` parts. A local rebuild therefore
invalidates only the affected fragments, rendered declarations, and root view. Both directions use
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

# Show a declaration with 6 upstream and 10 downstream dependencies.
lake exe leanreach Submodule.span_le

# Machine-readable output.
lake exe leanreach Submodule.span_le --json

# Pre-render the complete detected view. This resumes at the next incomplete module if interrupted.
lake exe leanreach cache

# Or pre-render only selected built modules.
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

Importing a complete Lean environment is the expensive part. Agents should reuse one process:

```console
lake exe leanreach --interactive --json --profile
```

Each input line is a declaration name or `search PATTERN`:

```text
search span_le
Submodule.span_le
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
directory or any of its subdirectories, invoke the packaged binary directly:

```console
/path/to/LeanReach/.lake/build/leanreach-dist/leanreach search my_theorem
```

LeanReach walks upward to the nearest Lake configuration and uses Lake's own package APIs to find
the local `lean_lib` modules. Every module with an existing `.olean` is searchable, so a partial
`lake build` is enough; missing modules are not built implicitly. If that package directly
`require`s Mathlib, the Mathlib root is included in the same search view. The small discovery result
is cached under `.lake` and invalidated by the Lake configuration hash.

`--module MyProject` remains available as an explicit override. Without `LEAN_PATH`, LeanReach also
discovers the project and dependency build directories plus their source roots. `lake env` remains
supported for projects with custom Lake build or source directories.

After `lake build`, pre-render the complete built root once:

```console
/path/to/leanreach cache
```

This pays index construction, environment import, and pretty-printing once. Work is saved after each
module, and a root completion marker makes repeated cache checks constant-time. The resulting
per-module caches are reusable from larger roots and are invalidated by the module's build hash.
LeanReach never builds missing modules implicitly.

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
LeanReach/Query.lean  rendering, source locations, and sessions
LeanReach/Project.lean  Lake project and built-module discovery
LeanReach.lean        environment-loading facade
Main.lean             Lake ArgsT CLI and interactive transport
Tests/                local-library fixture and behavior checks
```

The environment lifecycle, disk-cache strategy, and CLI organization are adapted from
[Loogle](https://github.com/nomeata/loogle), which is distributed under Apache-2.0. LeanReach's
dependency relation intentionally also includes proof and implementation bodies.
