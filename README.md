# LeanReach

LeanReach is a Lean-native companion to `rg` for finding declarations and navigating direct
dependencies. It reports:

- Lean-pretty-printed signatures and non-Prop definition bodies;
- source files, lines, and columns;
- ranked upstream and downstream declarations.

LeanReach reads built `.olean` and `.ilean` files. It supports Mathlib, local `lean_lib` modules,
and partially built Lake projects.

## Install

Add LeanReach to `lakefile.toml`:

```toml
[[require]]
name = "LeanReach"
scope = "pelicanhere"
rev = "main"
```

Then build it:

```console
lake update LeanReach
lake build @LeanReach/leanreach
lake query '@LeanReach/leanreach' --text
```

The last command prints the executable's absolute path. With the default Lake layout it is:

```text
.lake/packages/LeanReach/.lake/build/bin/leanreach
```

Use that executable directly. `lake exe @LeanReach/leanreach --help` is useful as a quick build
smoke test.

## Usage

```console
# Search declaration names.
./.lake/packages/LeanReach/.lake/build/bin/leanreach search span_le

# Show one declaration and its dependencies.
./.lake/packages/LeanReach/.lake/build/bin/leanreach Submodule.span_le

# Emit JSON.
./.lake/packages/LeanReach/.lake/build/bin/leanreach Submodule.span_le --json

# Build or resume caches for the detected project.
./.lake/packages/LeanReach/.lake/build/bin/leanreach cache

# Cache selected modules.
./.lake/packages/LeanReach/.lake/build/bin/leanreach cache Mathlib.LinearAlgebra.Span.Defs

# Override project detection.
./.lake/packages/LeanReach/.lake/build/bin/leanreach --module Mathlib.LinearAlgebra.Span.Defs Submodule.span_le
```

Queries return 10 upstream and 10 downstream declarations by default. Search returns 20 names.

```text
-m, --module MODULE   override automatic project detection
-n, --limit N         override dependency and search limits
-i, --interactive     read multiple commands from stdin
-j, --json            emit JSON or interactive NDJSON
    --profile         report timing information
-h, --help            show help
```

## Agent sessions

Keep one process alive for a chain of queries:

```console
./.lake/packages/LeanReach/.lake/build/bin/leanreach --interactive --json
```

Each input line is a declaration name or `search PATTERN`. The process returns and flushes one JSON
value per line.

## Project detection

Run LeanReach from the target project or a subdirectory. It discovers built local `lean_lib`
modules and Mathlib when required by that project. Modules without an `.olean` are skipped; after
building more modules, run the executable with `cache` to refresh the project view.

Caches are stored beside the corresponding `.olean` files and invalidated by Lake dependency
hashes. Generated caches and binaries are not tracked by this repository.

## Build from source

```console
lake build
./.lake/build/bin/leanreach --help
lake build leanreach_tests
lake exe leanreach_tests
```

## Frontend and benchmarks

```console
python Frontend/server.py --project-dir /path/to/project
python Benchmarks/run.py --project-dir /path/to/mathlib-project
python Benchmarks/plot.py
```

See [docs/architecture.md](docs/architecture.md) for the design and
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for adapted work and licenses.
