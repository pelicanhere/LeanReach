# LeanReach

LeanReach is a Lean-native companion to `rg` for finding declarations and navigating direct
dependencies. It reports:

- Pretty-printed signatures and non-Prop definition bodies;
- source files, lines, and columns;
- ranked upstream and downstream declarations.

It reads built `.olean` and `.ilean` files, including partially built local libraries.

## Install

Add LeanReach to `lakefile.toml`:

```toml
[[require]]
name = "LeanReach"
git = "https://github.com/pelicanhere/LeanReach.git"
rev = "v4.31.0"
```

Then build it and ask Lake for the executable path:

```console
lake update LeanReach
lake build @LeanReach/leanreach
lake query '@LeanReach/leanreach' --text
```

With the default Lake layout, the executable is usually at:

```text
.lake/packages/LeanReach/.lake/build/bin/leanreach
```

Use the executable directly. `lake exe @LeanReach/leanreach --help` can be used as a build smoke
test.

## Usage

```console
# Search declaration names with an unanchored regex.
./.lake/packages/LeanReach/.lake/build/bin/leanreach 'span_(le|eq)'

# Show one declaration and its direct dependencies.
./.lake/packages/LeanReach/.lake/build/bin/leanreach Submodule.span_le

# Emit JSON.
./.lake/packages/LeanReach/.lake/build/bin/leanreach Submodule.span_le --json

# Precompute caches for fast repeated queries.
./.lake/packages/LeanReach/.lake/build/bin/leanreach cache

# Override project detection.
./.lake/packages/LeanReach/.lake/build/bin/leanreach \
  --module Mathlib.LinearAlgebra.Span.Defs Submodule.span_le
```

An exact, case-sensitive declaration name shows its dependencies. Every other input is an
unanchored regex search. Use `(?i)` to ignore case, `^...$` to match the complete name, and `--`
before a dash-leading pattern.

Dependency lists and search results are limited to 10 entries by default.

```text
-m, --module MODULE   override automatic project detection
-n, --limit N         override dependency and search limits
-i, --interactive     read multiple commands from stdin
-j, --json            emit JSON or interactive NDJSON
    --profile         report timing information
-h, --help            show help
```

## Cache

Queries work without a prepared cache, but the first lookup may need to index built modules and
pretty-print selected declarations. Run `cache` once to build persistent dependency, search, and
pretty-print data for the detected project. Interrupted cache builds resume, and changed modules
are updated incrementally.

## Agent sessions

Keep one process alive for a chain of queries:

```console
./.lake/packages/LeanReach/.lake/build/bin/leanreach --interactive --json
```

Each input line follows the same exact-name-or-regex rule. The process returns and flushes one JSON
value per line.

## Project detection

Run LeanReach from the target project or a subdirectory. It discovers built local `lean_lib`
modules and Mathlib when required. Modules without an `.olean` are skipped. After building more
modules, run `cache` to refresh the detected project view.

Caches live beside the corresponding `.olean` files and are invalidated by Lake dependency hashes.

## Build from source

```console
lake build
./.lake/build/bin/leanreach --help
lake exe leanreach_tests
```

## Frontend

```console
python .lake/packages/LeanReach/Frontend/server.py --project-dir .
```

See [docs/architecture.md](docs/architecture.md) for the design.

## Acknowledgements

- LeanReach draws on [Loogle](https://github.com/nomeata/loogle), by Joachim Breitner and
  contributors, especially its environment, cache, CLI, and frontend design.
- Regex matching uses [lean-regex](https://github.com/pandaman64/lean-regex) by pandaman64.
