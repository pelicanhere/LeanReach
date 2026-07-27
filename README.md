# LeanReach

LeanReach is a Lean-native declaration search tool. It is meant to sit next to `rg`: use a name
fragment to find canonical declarations, then inspect the direct upstream and downstream
dependencies of a declaration together with its pretty-printed signature and exact source
position.

The implementation follows Loogle's deliberately simple process model:

- import one root module with `loadExts := true`;
- keep that complete `Environment` alive for the whole process;
- use Lean's own delaborator and pretty-printer;
- index only direct constants mentioned by declaration signatures;
- cache names and the reverse relation next to the root `.olean`;
- perform bounded breadth-first traversal instead of materializing a transitive DAG.

The cache is checked against Lake's transitive `depHash`, so a local library rebuild invalidates it
automatically. Upstream edges are read directly from `ConstantInfo.type`; only the reverse edges
needed for downstream lookup are stored.

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

# Show a declaration and both directions of its direct signature dependencies.
lake exe leanreach Submodule.span_le --limit 20

# Traverse two hops in one direction.
lake exe leanreach Submodule.span_le --upstream --depth 2

# Machine-readable output.
lake exe leanreach Submodule.span_le --json

# A narrower root imports and indexes much less than all of Mathlib.
lake exe leanreach --module Mathlib.LinearAlgebra.Span.Defs Submodule.span_le
```

Important options:

```text
-m, --module MODULE   imported root module (default: Mathlib)
-d, --depth N         dependency depth, 0 through 8 (default: 1)
-n, --limit N         results per list, 1 through 1000 (default: 20)
    --upstream        only constants used by the target signature
    --downstream      only signatures that use the target
-i, --interactive     keep the environment alive and read stdin
-j, --json            JSON, or NDJSON with --interactive
    --profile         report startup and per-query time
```

Lines and columns are one-based. Human output and JSON both contain the full source-like signature,
module name, absolute source path when available, and selection position.

## Long-lived agent session

Importing a complete Lean environment is the expensive part. Agents should reuse one process:

```console
lake exe leanreach --interactive --json --profile
```

Each input line is either a declaration name or `search PATTERN`:

```text
search span_le
Submodule.span_le
```

The process emits one compact JSON value per line and flushes stdout after every response. On the
development Windows machine, a small cached local environment took about 10 seconds to start; the
first name search and pretty-print took 89 ms, and the following dependency query took 7 ms.

The default `Mathlib` root is intentionally a much heavier workload. A first full run on the same
machine took 676.6 seconds including environment import, index construction, and a 265 MB cache
write; the actual bounded query and pretty-print took 1.0 second. An immediate warm run restored the
cache and finished in 29.9 seconds, of which 41 ms was the query. A cache avoids rebuilding the
reverse relation, but—as in Loogle—it cannot avoid importing the complete environment. Prefer the
narrowest useful root and keep full-Mathlib sessions alive.

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

An edge `A → B` means the type/signature of `A` contains the constant `B` after elaboration.
Consequently:

- upstream of `A` contains the constants used to state `A`;
- downstream of `B` contains declarations whose statements mention `B`;
- proof-body and implementation-only references are intentionally excluded.

This is the same lightweight relation used at the core of Loogle's candidate index. It is stable,
cheap to cache, and useful for navigating APIs, but it is not a call graph.

## Layout

```text
LeanReach.lean       environment, cache, search, traversal, signatures, and locations
Main.lean            Lake ArgsT CLI and interactive transport
Tests/Fixture.lean   local-library fixture
Tests/Main.lean      signature, location, search, and dependency checks
```

The environment lifecycle, disk-cache strategy, and CLI organization are adapted from
[Loogle](https://github.com/nomeata/loogle), which is distributed under Apache-2.0.
