# LeanReach

LeanReach is a Lean-native CLI for finding declarations, opening their exact source locations, and
inspecting a bounded neighborhood of upstream and downstream dependencies.

LeanReach indexes Lean's resolved `.ilean` data and reads selected `.olean` constants only when
rendering result signatures. It never imports a Mathlib `Environment`, and it stores direct
references rather than a transitive declaration DAG.

The long-lived process model follows
[Lean REPL](https://github.com/leanprover-community/repl). Persistent cache validation and the
Lean-native CLI design are influenced by [Loogle](https://github.com/nomeata/loogle).

## Build and test

The project is pinned to Lean and Mathlib `v4.32.0`.

```console
lake build
lake exe leanreach_tests
lake exe leanreach_integration_tests
lake exe leanreach --help
```

Mathlib is already a Lake dependency. LeanReach does not download or maintain another copy.

## Source queries

The default root module is `Mathlib`, direction is `both`, and depth is one.

```console
# Build or validate the persistent source index.
lake exe leanreach index --profile

# Find ranked canonical declarations and their source positions.
lake exe leanreach search span_le --limit 10 --json

# Inspect direct source-visible dependencies and dependents.
lake exe leanreach Submodule.span_le --limit 30

# Use a smaller import closure.
lake exe leanreach Nat.gcd --module Mathlib.Data.Nat.GCD.Basic

# Traverse two source-reference hops.
lake exe leanreach Submodule.span --upstream --depth 2 --limit 50 --json
```

The first source command builds an index when no valid cache exists. Later processes map the cache
directly. `index` is an optional prewarm command; query and search perform the same validation
automatically.

Important options:

```text
-m, --module MODULE       root MODULE; repeatable (default: Mathlib)
    --direction DIR       both, upstream, or downstream
    --upstream            shorthand for upstream only
    --downstream          shorthand for downstream only
-d, --depth N             dependency depth, 0..8 (default: 1)
-n, --limit N             returned items per direction, 1..1000
-j, --json                structured JSON output
    --interactive         newline-delimited JSON session
    --include-internal    include generated/internal names
    --profile             cache and query timings on stderr
```

Name lookup ranks exact, suffix, case-insensitive, and substring matches. A query never silently
chooses between equally ranked suffixes; it returns candidates with locations instead.

## Persistent source index

For each root set, LeanReach:

1. reads Lake's `.trace` `depHash` as the transitive build fingerprint;
2. traverses `.ilean` imports, including Lean's implicit `Init` closure;
3. parses files with eight workers and a bounded 32-file window;
4. extracts `.decls ∪ references.const.definition` locations;
5. assigns dense declaration IDs and builds both directions of the direct graph as CSR arrays;
6. caches lowercase names and a 64-bit trigram filter for fast ranked substring search;
7. saves the payload with `Lean.CompactedRegion`.

The payload has an explicit format version and a stable cache name derived from the complete sorted
root set; the stored build fingerprint controls invalidation and overwrite. Any missing `.ilean` in
the traversed closure is an error, so a partial index cannot produce complete-looking results. A
mapped compacted region is bracketed around one command or interactive session and released
afterwards.

This is lighter than an imported Mathlib environment and deliberately omits declaration types,
values, transitive closure, and full edge paths. Both dependency directions follow persistent
direct-edge arrays, so a warm query does not reopen `.ilean` files.

## Dependency semantics

An edge is a resolved source identifier attributed to its enclosing `parentDecl` by Lean's language
server data. This matches the declarations an agent can open and inspect in source. It deliberately
does not model constants introduced only by elaboration, such as some implicit instances, notation
expansions, or generated declarations.

`.ilean` contains exact selection ranges but no declaration type. For only the declarations that
will be returned, LeanReach memory-maps the owning `.olean`, passes its exported `ConstantInfo`
and the constants directly referenced by its type through Lean's own `PrettyPrinter.ppSignature`
in a temporary minimal environment, materializes the resulting string, and releases the mappings.
The session caches those strings, so repeated NDJSON requests do not render them again. This
preserves lightweight startup while returning an exact, canonical signature; some notation remains
explicit because no dependency environment is imported.

## Agent session protocol

Start one process and reuse its mapped source index:

```console
lake exe leanreach --interactive --profile
```

Write one JSON object per line. LeanReach emits the query result, search result, or error directly as
one compact response per nonblank request and flushes stdout immediately.

```json
{"command":"search","query":"span_le","limit":10}
{"command":"query","query":"Submodule.span_le","direction":"downstream","limit":20}
```

`command` and `query` are required. Supported commands are `query` and `search`; a request may
override `direction`, `depth`, and `limit`. Root modules and `--include-internal` are fixed for the
session. EOF ends the session. Malformed requests return `{"error":...,"candidates":[]}` without
terminating the process.

## Output contract

Lines and columns are one-based.

```json
{
  "name": "Nat.gcd_comm",
  "signature": "Nat.gcd_comm (m n : Nat) : Eq (m.gcd n) (n.gcd m)",
  "source": {
    "moduleName": "Init.Data.Nat.Gcd",
    "file": ".../Init/Data/Nat/Gcd.lean",
    "line": 109,
    "column": 9,
    "endLine": 109,
    "endColumn": 17
  }
}
```

Relations add `distance` and, beyond the first hop, one lightweight `via` witness. `limit` bounds
serialized items while `total` reports the full number found.

## Measured performance

On the development Windows machine with a warm filesystem cache:

- full-Mathlib v4 index rebuild and save: `38.763 s`;
- index contents: 387,200 source-visible declarations and 2,379,347 direct relations whose two
  endpoints are both source-visible;
- cache size: 144,814,648 bytes, smaller than the previous one-direction v2 cache;
- mapped-cache restore: `1–2 ms`;
- interactive exact `Submodule.span_le` neighborhood: `94 ms` including first signature rendering,
  then `1 ms` from the session cache;
- interactive `search span_le --limit 5`: `149 ms` including first signature rendering, then
  `27 ms`, versus roughly `708 ms` before cached trigram filtering;
- the intentionally broad `search a --limit 1`: about `336 ms`, versus about `50 s` when every
  matching name was accumulated and sorted.

Cold setup is paid once per Mathlib build fingerprint. `lake exe` adds Lake startup time; an
installed/native invocation should run with the project's `LEAN_PATH`, while an interactive session
amortizes process startup entirely.

In a five-task end-to-end theorem-finding pilot, fresh matched subagents both achieved 5/5:
LeanReach-only used 6 search commands and 230.982 seconds; rg-only used 15 commands and 299.017
seconds. LeanReach was 22.8% faster overall, but rg was slightly faster on three simple names; the
largest LeanReach win was the namespace-heavy `IsLimit.hom_ext` task. See
[the benchmark report](docs/benchmark.md) for the full protocol and per-task timings.

## Repository layout

```text
Main.lean                         Lake.ArgsT CLI parser
LeanReach/Cli.lean                source-index lifecycle and command dispatch
LeanReach/Interactive.lean        typed NDJSON request and transport loop
LeanReach/SourceIndex.lean        indexed source search and bounded BFS
LeanReach/SourceIndex/Build.lean  .ilean traversal and persistent cache
LeanReach/Signatures.lean         selective .olean signature rendering
LeanReach/Query/Ilean.lean        shared .ilean and source-path utilities
LeanReach/Protocol.lean           compact public request/result models
Tests/Smoke.lean                  semantic and cache lifecycle tests
Tests/Integration.lean            CLI and NDJSON process tests
```
