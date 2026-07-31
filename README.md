# LeanReach

LeanReach is a Lean-native companion to `rg` for finding declarations and navigating direct
dependencies. It reports:

- Lean-pretty-printed signatures and non-Prop definition bodies;
- source files, lines, and columns;
- ranked upstream and downstream declarations.

It reads built `.olean` and `.ilean` files, including partially built local libraries.

## Install

Add LeanReach to `lakefile.toml`:

```toml
[[require]]
name = "LeanReach"
scope = "pelicanhere"
rev = "main"
```

Then build it and ask Lake for the executable path:

```console
lake update LeanReach
lake build @LeanReach/leanreach
lake query '@LeanReach/leanreach' --text
```

With the default Lake layout, use:

```text
.lake/packages/LeanReach/.lake/build/bin/leanreach
```

`lake exe @LeanReach/leanreach --help` is useful as a build smoke test.

## Usage

```console
# Search declaration names with an unanchored regex.
./.lake/packages/LeanReach/.lake/build/bin/leanreach 'span_(le|eq)'

# Show one declaration and its direct dependencies.
./.lake/packages/LeanReach/.lake/build/bin/leanreach Submodule.span_le

# Emit JSON.
./.lake/packages/LeanReach/.lake/build/bin/leanreach Submodule.span_le --json

# Build or resume caches for the detected project.
./.lake/packages/LeanReach/.lake/build/bin/leanreach cache

# Override project detection.
./.lake/packages/LeanReach/.lake/build/bin/leanreach \
  --module Mathlib.LinearAlgebra.Span.Defs Submodule.span_le
```

An exact, case-sensitive declaration name shows its dependencies. Every other input is an
unanchored regex search. Use `(?i)` to ignore case, `^...$` to match the complete name, and `--`
before a dash-leading pattern.

Queries and searches return 10 declarations by default.

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

Each input line follows the same exact-name-or-regex rule. The process returns and flushes one JSON
value per line.

## Project detection

Run LeanReach from the target project or a subdirectory. It discovers built local `lean_lib`
modules and Mathlib when required. Modules without an `.olean` are skipped; after building more
modules, run `cache` to refresh the project view.

Caches live beside the corresponding `.olean` files and are invalidated by Lake dependency hashes.

## Build from source

```console
lake build
./.lake/build/bin/leanreach --help
lake exe leanreach_tests
```

## Frontend and benchmarks

```console
python Frontend/server.py --project-dir /path/to/project
python Benchmarks/run.py --stage my-change --query-set all --append-history
python Benchmarks/plot.py
```

See [docs/architecture.md](docs/architecture.md) for the design and
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for adapted work and licenses.
