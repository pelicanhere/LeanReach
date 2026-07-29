# LeanReach

LeanReach is a Lean-native companion to `rg` for finding declarations and navigating their direct
dependencies. A query returns:

- the declaration's Lean-pretty-printed signature, plus the body for non-Prop definitions;
- its source file, line, and column;
- ranked upstream declarations used by its type, proof, or implementation;
- ranked downstream declarations that use it.

LeanReach reads already-built `.olean` and `.ilean` files. It works with Mathlib, local `lean_lib`
modules, and partially built Lake projects without building missing modules.

## Build

LeanReach currently targets Lean and Mathlib `v4.32.0`.

```console
lake build
lake exe leanreach_tests
```

The native executable is written to `.lake/build/bin/leanreach` (`leanreach.exe` on Windows).
To create a directly runnable Windows distribution with the required Lean runtime DLLs:

```console
pwsh scripts/package.ps1
.lake/build/leanreach-dist/leanreach.exe --help
```

## CLI

```console
# Find declarations by exact name, final component, or substring.
lake exe leanreach search span_le

# Show a declaration and its direct dependencies.
lake exe leanreach Submodule.span_le

# Emit JSON.
lake exe leanreach Submodule.span_le --json

# Build or resume caches for the detected project view.
lake exe leanreach cache --profile

# Cache selected modules only.
lake exe leanreach cache Mathlib.LinearAlgebra.Span.Defs

# Override automatic project detection.
lake exe leanreach --module Mathlib.LinearAlgebra.Span.Defs Submodule.span_le
```

The default query returns 10 upstream and 10 downstream declarations. Search returns 20 names.

```text
-m, --module MODULE   override automatic project detection
-n, --limit N         override both dependency and search limits
-i, --interactive     read multiple commands from stdin
-j, --json            emit JSON, or NDJSON in interactive mode
    --profile         report startup, query, and cache-stage timings
-h, --help            show help
```

Lines and columns are one-based. Source paths are absolute when LeanReach can locate the matching
source tree.

## Agent session

For a chain of queries, keep one process alive to avoid repeatedly starting the Lean runtime:

```console
lake exe leanreach --interactive --json
```

Each input line is either a declaration name or `search PATTERN`:

```text
search localization_maximal
Submodule.span_eq_bot
```

The process writes and flushes one compact JSON value per line. It loads the dependency index once,
loads only relevant PP sidecars, and writes back newly pretty-printed declarations.

## Local Lake projects

Build LeanReach with the same Lean toolchain as the target project. Then run the packaged executable
from the target project or one of its subdirectories:

```console
/path/to/LeanReach/.lake/build/leanreach-dist/leanreach.exe search my_theorem
```

LeanReach walks upward to the nearest `lakefile.toml` or `lakefile.lean`, asks Lake for the local
`lean_lib` roots, and includes every source module with an existing `.olean`. If the project
directly requires Mathlib, the Mathlib root is included in the same query view.

`leanreach cache` refreshes the set of built local modules. Ordinary queries reuse the persisted
project view to avoid recursively scanning `.lake/build` during every process startup.

Caches are stored next to the corresponding `.olean` files and invalidated with Lake dependency
hashes. Rebuilding one local module reuses unchanged module fragments and PP sidecars; a changed
module is regenerated at module granularity.

## Web frontend

The frontend is a Python standard-library HTTP server backed by one long-lived interactive
LeanReach process. On Windows, run `pwsh scripts/package.ps1` first so the executable has its Lean
runtime DLLs:

```console
python Frontend/server.py --project-dir .
```

Open <http://127.0.0.1:8088>. To pass CLI options to the worker:

```console
python Frontend/server.py --project-dir . -- --module Mathlib --limit 20
```

## Benchmarks

The benchmark compares distinct, first-use name searches in a long-lived LeanReach session with
fresh LeanReach and `rg` processes. It does not count repeated lookup of one declaration as a cold
query.

```console
pwsh scripts/package.ps1
.lake/build/leanreach-dist/leanreach.exe cache
python Benchmarks/run.py --stage my-change --query-set substring --append-history
python Benchmarks/plot.py
```

The current harness targets the Windows distribution. The history is rendered as
[Benchmarks/history.svg](Benchmarks/history.svg).

## Design

See [docs/architecture.md](docs/architecture.md) for dependency semantics, ranking, persistent cache
layers, incremental behavior, pretty-printing, and the source layout.

See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for adapted work and licenses.
