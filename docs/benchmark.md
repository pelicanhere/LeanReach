# LeanReach and ripgrep navigation baseline

This report records the first local baseline used to guide LeanReach. It separates three questions:

1. Can text search locate the canonical declaration?
2. Can text visible in a declaration recover its semantic upstream constants?
3. Can full-name text hits recover declarations that semantically depend on a target?

The semantic gold set was generated with Lean. The `rg` arm was run by a separate subagent that was
not allowed to modify the implementation.

## Environment and method

- date: 2026-07-27;
- platform: Windows, warm filesystem cache;
- Lean: `4.32.0`;
- Mathlib: `v4.32.0`, commit `81a5d257c8e410db227a6665ed08f64fea08e997`;
- ripgrep: `14.1.0`;
- `Mathlib/`: 8,264 Lean source files;
- complete mathlib checkout: 8,795 Lean files, approximately 101.6 MB.

Each full-tree `rg` timing was preceded by one warm-up and then measured in 15 fresh processes.
Hardware details were not recorded, so absolute timings are indicative rather than portable.

The six targets intentionally cover ordinary declarations, namespace-heavy APIs, high fan-out
foundations, and a generated structure projection:

- `Submodule.span`;
- `Filter.Tendsto`;
- `Polynomial.derivative`;
- `MeasureTheory.Integrable`;
- `CategoryTheory.Limits.IsLimit`;
- `CategoryTheory.Limits.IsLimit.lift`.

## Declaration location

Searching the full canonical name did not locate the defining declaration for any target. Lean code
usually declares only the final name component inside a namespace, and generated projections may
not appear as declaration commands at all.

| Declaration | SourceInfo selection line | Full-name hit lines / files | Definition found | Tail-regex candidates | `rg` p50 / p95 |
|---|---:|---:|---:|---:|---:|
| `Submodule.span` | 48 | 918 / 275 | no | 13 | 264 / 297 ms |
| `Filter.Tendsto` | 321 | 430 / 170 | no | 135 | 298 / 343 ms |
| `Polynomial.derivative` | 46 | 40 / 12 | no | 5 | 268 / 284 ms |
| `MeasureTheory.Integrable` | 58 | 57 / 20 | no | 177 | 265 / 305 ms |
| `CategoryTheory.Limits.IsLimit` | 55 | 9 / 8 | no | 35 | 263 / 278 ms |
| `CategoryTheory.Limits.IsLimit.lift` | 57 | 0 / 0 | no | 47 | 274 / 299 ms |

Aggregate results:

- full-name definition recall: `0 / 6`;
- tail declaration-regex recall: `6 / 6`;
- tail candidates: 412, of which 6 were the targets;
- tail-candidate micro precision: `1.46%`;
- full-tree `rg` p50: approximately `266 ms`.

The projection required a field-specific regex (`^\s+lift\s*:`); a normal
`def|theorem|structure|class|inductive` declaration regex misses it.

LeanReach resolves all six through the loaded environment and obtains their canonical selection
ranges from Lean's declaration-range data, without guessing a declaration regex.

## Upstream semantic visibility

The gold set is the deduplicated set of non-internal constants in each declaration's elaborated type
and value. The table asks how many gold constants are visibly recoverable inside the declaration's
source range.

| Declaration | Direct public constants | Full canonical name visible | Short final component visible |
|---|---:|---:|---:|
| `Submodule.span` | 12 | 2 | 3 |
| `Filter.Tendsto` | 6 | 1 | 2 |
| `Polynomial.derivative` | 40 | 0 | 4 |
| `MeasureTheory.Integrable` | 9 | 1 | 5 |
| `CategoryTheory.Limits.IsLimit` | 3 | 0 | 1 |
| `CategoryTheory.Limits.IsLimit.lift` | 8 | 0 | 2 |
| **Total** | **78** | **4 (5.13%)** | **17 (21.8%)** |

Missing edges come from namespace elision, notation, section parameters, implicit instances, and
elaborator-generated constants. The short-name column is only an optimistic upper bound: a token
match still does not resolve which declaration that token denotes.

LeanReach exposes both interpretations:

- `--mode source` reports resolved source identifiers attributed by `.ilean`;
- `--mode kernel` reports the elaborated constant gold definition used above.

These modes should not be expected to return identical counts.

## Downstream semantic visibility

The offline gold builder scanned public declarations after `import Mathlib` and found 10,418 direct
kernel dependents across the six targets. Of those, 10,094 had readable declaration ranges.

| Declaration | Locatable dependents | Full-name declaration recall | Hit-line precision | File precision / recall |
|---|---:|---:|---:|---:|
| `Submodule.span` | 1,938 | 30.60% | 90.31% | 96.00% / 60.27% |
| `Filter.Tendsto` | 4,312 | 7.07% | 76.05% | 95.88% / 22.93% |
| `Polynomial.derivative` | 379 | 6.60% | 82.50% | 91.67% / 19.30% |
| `MeasureTheory.Integrable` | 1,542 | 2.72% | 75.44% | 95.00% / 10.61% |
| `CategoryTheory.Limits.IsLimit` | 1,581 | 0.19% | 33.33% | 75.00% / 2.07% |
| `CategoryTheory.Limits.IsLimit.lift` | 342 | 0% | no hits | 0% / 0% |

Aggregate results:

- declaration-level micro recall: `968 / 10,094 = 9.59%`;
- hit-line micro precision: `1,235 / 1,454 = 84.94%`;
- file-level precision: `95.46%`;
- file-level recall: `25.87%`;
- short-final-component declaration recall upper bound: `72.46%`.

The pattern is high precision when a fully qualified token is present, but systematic omissions for
short names, projections, dot notation, and implicit dependencies.

The full kernel gold construction took approximately 224 seconds. That is an offline benchmark cost,
not a proposed LeanReach single-query path.

## Current LeanReach source-session timing

The same six targets were queried in one `--interactive` process after a single `import Mathlib`.
Each target received one depth-one source-upstream and one depth-one source-downstream request.
Output was limited to ten items, but `total` still counted every discovered relation.

| Declaration | Source upstream count / time | Source downstream count / time |
|---|---:|---:|
| `Submodule.span` | 3 / 16 ms | 935 / 936 ms |
| `Filter.Tendsto` | 2 / 34 ms | 3,086 / 2,425 ms |
| `Polynomial.derivative` | 17 / 27 ms | 295 / 367 ms |
| `MeasureTheory.Integrable` | 4 / 21 ms | 1,216 / 268 ms |
| `CategoryTheory.Limits.IsLimit` | 4 / 38 ms | 811 / 2,190 ms |
| `CategoryTheory.Limits.IsLimit.lift` | 0 / 8 ms | 267 / 490 ms |

For this run:

- cold Mathlib import: `12,025 ms`;
- six source-upstream requests: 8–38 ms, median approximately 24 ms;
- six source-downstream requests: 268–2,425 ms, median approximately 713 ms;
- all 12 requests: `6,820 ms`;
- process total: `18,845 ms`.

This is not a claim that LeanReach is universally faster than `rg`. Warm source-upstream navigation
is much faster than a fresh full-tree `rg` process here, while foundational downstream scans remain
slower. The advantage is that returned hits are resolved declaration-owned edges with exact source
positions. The NDJSON mode amortizes the much larger cold import.

Likely next performance work, if measurements justify it, is a compact per-module reference filter
that is invalidated by Lean version and `.ilean` identity. A persistent full declaration DAG remains
out of scope.

## Reproducing the text timings

From the LeanReach repository in PowerShell:

```powershell
$M = (Resolve-Path .lake\packages\mathlib).Path
$S = Join-Path $M Mathlib

rg --version
git -C $M rev-parse HEAD
@(rg --files $S -g '*.lean').Count

$args = @(
  '--no-heading',
  '--line-number',
  '--glob', '*.lean',
  '-F', 'Filter.Tendsto',
  $S
)

& rg @args | Out-Null
$times = 1..15 | ForEach-Object {
  $sw = [Diagnostics.Stopwatch]::StartNew()
  & rg @args | Out-Null
  $sw.Stop()
  $sw.Elapsed.TotalMilliseconds
}
$times | Sort-Object
```

Tail declaration heuristic:

```powershell
rg -n --glob '*.lean' `
  '^\s*(?:(?:protected|noncomputable|private|unsafe)\s+)*(?:def|abbrev|theorem|lemma|structure|class|inductive)\s+Tendsto\b' `
  $S
```

Projection-specific heuristic:

```powershell
rg -n --glob '*.lean' '^\s+lift\s*:' $S
```

Run the LeanReach timing arm with `--profile`; request timings go to stderr:

```powershell
$requests = @(
  '{"id":1,"command":"query","query":"Filter.Tendsto","direction":"upstream","limit":10}',
  '{"id":2,"command":"query","query":"Filter.Tendsto","direction":"downstream","limit":10}',
  '{"id":3,"command":"quit"}'
)
$requests | lake exe leanreach --interactive --profile
```

## Proposed agent A/B evaluation

The next evaluation should measure task success, not only search primitives.

- Start with a 24-task pilot, then use a 100-task hidden set.
- Arm A may use only `rg` plus file reads.
- Arm B may use only LeanReach plus file reads.
- An optional third arm may combine both, which is likely the realistic workflow.
- Keep model, prompt, token budget, tool-call budget, 90-second timeout, and environment fixed.
- Run each task with three randomized seeds and an independent context.
- Disallow network access and ad-hoc Lean metaprograms that bypass the assigned search tool.

Use four balanced task families:

1. locate a canonical declaration, module, file, and selection line;
2. recover direct public upstream constants;
3. recover low-degree downstream sets or Precision@10 for high-degree targets;
4. navigate one or two semantic hops to a declaration matching a description.

Stratify the hidden set across ordinary definitions/theorems, repeated final names, notation and
implicit dependencies, generated projections/constructors, mathematical domains, and graph degree.

Primary metrics:

- exact location accuracy and MRR@5;
- upstream/downstream micro and macro precision, recall, and F1;
- hallucinated declaration rate;
- source-line accuracy;
- end-to-end task success;
- tool calls, tokens, wall time, and timeout rate;
- CLI cold import and hot query p50/p95.

Use paired bootstrap 95% confidence intervals; use McNemar's test for paired binary task success.
