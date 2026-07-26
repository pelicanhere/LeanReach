# LeanReach

LeanReach is a Lean-native command-line tool for navigating declaration neighborhoods. It resolves
declaration names, reports their source positions, and follows upstream or downstream dependencies
without building a full declaration DAG.

It is intended for coding agents that need a stronger first navigation step than raw text search:

- declaration-aware exact, suffix, case-insensitive, and substring lookup;
- canonical declaration kinds and `SourceInfo` file/line/column ranges;
- resolved source-reference edges from `.ilean` files;
- elaborated constant edges from `.olean` environments;
- bounded output and dependency depth;
- a long-lived NDJSON mode that amortizes Mathlib import time.

The interaction model is influenced by
[Lean REPL](https://github.com/leanprover-community/repl), while the Lean-native search direction is
influenced by [Loogle](https://github.com/nomeata/loogle).

## Build and test

The project is pinned to Lean and Mathlib `v4.32.0`.

```console
lake build
lake exe leanreach_tests
lake exe leanreach --help
```

## One-shot queries

The default module is `Mathlib`, dependency mode is `source`, direction is `both`, and depth is one.

```console
# Resolve a declaration and inspect both sides of its neighborhood.
lake exe leanreach Submodule.span

# Restrict startup to a smaller import closure.
lake exe leanreach Nat.gcd --module Mathlib.Data.Nat.GCD.Basic

# Follow elaborated constants rather than source references.
lake exe leanreach Nat.gcd_comm --mode kernel --upstream

# Traverse two source-reference hops and return JSON.
lake exe leanreach Submodule.span --upstream --depth 2 --limit 50 --json

# Find ranked declaration-name candidates without choosing an ambiguous suffix.
lake exe leanreach search gcd_comm --limit 20 --json
```

Important options:

```text
-m, --module MODULE       import MODULE; repeatable (default: Mathlib)
    --mode MODE           source or kernel (default: source)
    --direction DIR       both, upstream, or downstream
    --upstream            shorthand for upstream only
    --downstream          shorthand for downstream only
-d, --depth N             dependency depth, 0..8 (default: 1)
-n, --limit N             returned items per direction, 1..1000
-j, --json                pretty JSON output
    --include-internal    include generated/internal declarations
    --profile             timings on stderr
```

`limit` bounds serialized output, while each relation list retains the total number found. Name
resolution never silently chooses between equally ranked suffixes: an ambiguous query returns
ranked candidates with source positions.

## Dependency semantics

LeanReach deliberately exposes two graphs because “dependency” has two useful meanings.

| Mode | Edge meaning | Best use | Cost profile |
|---|---|---|---|
| `source` | A resolved identifier occurrence in `.ilean`, attributed to its parent declaration | agent navigation and nearby source | upstream reads the owning file; downstream scans only modules that can import the target |
| `kernel` | A constant occurs in the elaborated declaration type or value | implicit arguments, instances, notation expansion, generated declarations | upstream is in-memory; downstream scans all loaded constants per layer |

Source mode is the default because it stays close to code an agent can open and edit. Kernel mode
can reveal dependencies that are not written as tokens, but a full-Mathlib downstream scan is
intentionally explicit and can be expensive.

Generated projections illustrate the difference: a field such as
`CategoryTheory.Limits.IsLimit.lift` may have no independently attributed source-upstream references,
while kernel mode still sees the constants in its elaborated declaration.

## Agent session protocol

Start one process and reuse its imported environment:

```console
lake exe leanreach --interactive --module Mathlib --profile
```

Write one JSON object per line to stdin. LeanReach writes exactly one compact JSON response per
nonblank request and flushes stdout immediately. Arbitrary JSON `id` values are echoed.

```json
{"id":1,"command":"ping"}
{"id":2,"command":"query","query":"Submodule.span","direction":"upstream","depth":2,"limit":30}
{"id":3,"command":"search","query":"span_le","limit":10}
{"id":4,"command":"quit"}
```

Successful response:

```json
{"id":1,"ok":true,"result":{"mode":"source","status":"ready"}}
```

Protocol or resolution failure:

```json
{"id":2,"ok":false,"error":"missing required field 'query'"}
```

Supported commands are:

- `query` (the default when `command` is omitted);
- `search`;
- `ping`;
- `quit`.

A request may override `direction`, `depth`, `limit`, and `includeInternal`. Imported modules and
`source`/`kernel` mode are fixed when the process starts because they determine the environment's
`.olean` loading level. Malformed requests return an error and the session continues. EOF also
closes the session.

## Lightweight downstream strategy

LeanReach does not materialize a global declaration DAG. A source-downstream query instead:

1. finds the module that owns the target declaration;
2. makes one topological pass over the import graph to retain only possible dependent modules;
3. checks `.ilean` text for the exact serialized resolved-reference key;
4. parses only matching `.ilean` files;
5. reads `parentDecl` owners and expands only the requested number of layers.

Candidate files are read in bounded parallel batches. This keeps persistent state at zero and
memory proportional to matching files, while remaining semantically more useful than a token grep.
Long-lived sessions amortize the dominant cold import.

## Output contract

JSON payloads currently use `schemaVersion: 1`. Source lines and columns are one-based. Each
declaration contains:

```json
{
  "name": "Submodule.span",
  "kind": "definition",
  "source": {
    "moduleName": "Mathlib.LinearAlgebra.Span.Defs",
    "file": ".../Mathlib/LinearAlgebra/Span/Defs.lean",
    "line": 48,
    "column": 5,
    "endLine": 48,
    "endColumn": 9
  }
}
```

Relations add `distance` and, after the first hop, one lightweight `via` witness.

## Performance and rg comparison

See [docs/benchmark.md](docs/benchmark.md) for the measured six-declaration baseline, current
LeanReach session timings, and the proposed hidden-set agent A/B protocol.

The current tradeoff is explicit:

- hot declaration resolution and source-upstream queries take tens of milliseconds in a reused
  process;
- full-Mathlib source-downstream queries currently range from hundreds of milliseconds to a few
  seconds depending on the target module;
- importing all of Mathlib is still the dominant cold cost, so agents should use `--interactive`
  or import a smaller module closure;
- `rg` remains excellent for literal text, while LeanReach addresses canonical resolution,
  implicit semantic edges, and declaration-owned source locations.

## Repository layout

```text
Main.lean                 executable entrypoint
LeanReach/Cli.lean        argument parsing and environment lifetime
LeanReach/Interactive.lean
                           NDJSON request loop
LeanReach/Query.lean      resolution, locations, and both dependency modes
LeanReach/Output.lean     human and JSON rendering
LeanReach/Options.lean    shared validated limits/options
Tests/Smoke.lean          source/kernel semantic smoke coverage
```
