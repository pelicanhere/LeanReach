# End-to-end theorem-finding benchmark

This report replaces the earlier static text-hit baseline. The benchmark unit is now the task the
tool is intended to help with: give an agent a mathematical description, let it guess a declaration
name, search with its assigned tool, and require a canonical declaration plus verified source
evidence.

The result is a small pilot, not a statistically powered claim.

## Environment

- date: 2026-07-27;
- platform: Windows, warm filesystem cache;
- Lean: `4.32.0`;
- Mathlib: `v4.32.0`, commit `81a5d257c8e410db227a6665ed08f64fea08e997`;
- ripgrep: `14.1.0`;
- both arms: fresh subagent context, same model and high reasoning effort;
- network and ad-hoc Lean metaprograms: forbidden.

The LeanReach arm used the compiled native executable with `LEAN_PATH` already set. It did not pay
`lake exe` startup. Its full-Mathlib index had been built before the tasks. That one-time setup is
reported separately below and excluded from theorem-finding time.

## Paired protocol

Two fresh subagents received the same five natural-language goals without the expected declaration
names:

1. characterize `span R s ≤ p` by `s ⊆ p`;
2. show polynomial formal derivative preserves addition;
3. compose two `Filter.Tendsto` relations;
4. prove the generic `IsLimit` morphism extensionality principle;
5. show a Bochner integral preserves addition for two integrable functions.

Both arms had to return:

- the exact canonical Lean declaration;
- absolute file path and one-based line;
- a source statement confirming the semantics;
- tool-command count;
- per-task and total wall time.

The restrictions differed only in the search tool:

| Arm | Allowed | Forbidden |
|---|---|---|
| rg-only | `rg`, then `Get-Content` on exact hits | LeanReach, Lean/Lake queries, other search tools, web |
| LeanReach-only | LeanReach `search`/query, then `Get-Content` at returned locations | `rg`, `Select-String`, recursive enumeration, Lean/Lake queries, web |

Every answer required actual tool evidence; memory-only answers were invalid. Each task had a
90-second limit. Agents recorded Unix millisecond timestamps before and after every task and around
the full batch, so elapsed time includes name guessing, commands, result interpretation, and source
verification.

## Results

Both arms found all five declarations correctly.

| Task | Canonical declaration | rg-only | LeanReach-only | Faster arm |
|---|---|---:|---:|---|
| span characterization | `Submodule.span_le` | 43.518 s / 3 commands | 44.612 s / 2 commands | rg by 1.094 s |
| derivative of a sum | `Polynomial.derivative_add` | 40.018 s / 3 commands | 31.192 s / 1 command | LeanReach by 8.826 s |
| Tendsto composition | `Filter.Tendsto.comp` | 25.281 s / 2 commands | 32.126 s / 1 command | rg by 6.845 s |
| generic limit hom extensionality | `CategoryTheory.Limits.IsLimit.hom_ext` | 87.673 s / 5 commands | 30.314 s / 1 command | LeanReach by 57.359 s |
| Bochner integral addition | `MeasureTheory.integral_add` | 29.165 s / 2 commands | 34.450 s / 1 command | rg by 5.285 s |

Aggregate:

| Metric | rg-only | LeanReach-only | Difference |
|---|---:|---:|---:|
| task success | 5/5 | 5/5 | tied |
| summed task time | 225.655 s | 172.694 s | LeanReach 23.5% lower |
| median task time | 40.018 s | 32.126 s | LeanReach 19.7% lower |
| full batch elapsed | 299.017 s | 230.982 s | LeanReach 22.8% lower |
| search commands | 15 | 6 | LeanReach 60% fewer |
| per-task wins | 3 | 2 | rg won more simple tasks |

The result is deliberately nuanced. `rg` was slightly faster on three goals whose likely theorem
names and directory scopes were straightforward. LeanReach's aggregate advantage came from fewer
iterations and one large win on the namespace-heavy `IsLimit.hom_ext` goal, where text search had to
disambiguate many specialized cone extensionality theorems.

This pilot supports the intended claim—canonical ranked declarations and exact locations can reduce
agent search work—but does not show that LeanReach is faster for every theorem.

## Verified answers

| Declaration | Source |
|---|---|
| `Submodule.span_le` | `Mathlib/LinearAlgebra/Span/Defs.lean:82` |
| `Polynomial.derivative_add` | `Mathlib/Algebra/Polynomial/Derivative.lean:125` |
| `Filter.Tendsto.comp` | `Mathlib/Order/Filter/Tendsto.lean:123` |
| `CategoryTheory.Limits.IsLimit.hom_ext` | `Mathlib/CategoryTheory/Limits/IsLimit.lean:246` |
| `MeasureTheory.integral_add` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:237` |

The LeanReach agent used six commands because its first attempt on task 1 searched the whole
mathematical statement, returned no name match, and then switched to the guessed canonical fragment.
The rg agent used fifteen commands, including one failed candidate-file search on task 4. Both are
counted rather than removed as warm-up.

## Index setup and native query cost

The full Mathlib `.ilean` corpus contains 8,275 files and 267.62 MiB of JSON. LeanReach's first
indexed run measured:

| Stage or artifact | Result |
|---|---:|
| build and save | 58.133 s |
| source-visible declarations | 387,200 |
| direct reference postings | 2,406,834 |
| compacted cache | 147,386,416 bytes |

Fresh native processes with the cache already present measured:

| Command | Init | Restore | Query | Total |
|---|---:|---:|---:|---:|
| exact `Submodule.span_le` neighborhood | 148 ms | 1 ms | 26 ms | 175 ms |
| ranked `search span_le --limit 5` | 149 ms | 16 ms | 708 ms | 873 ms |

The previous Environment-based implementation spent about 506 seconds importing full Mathlib before
a one-shot search on this machine. The current `.ilean` implementation does not perform that import.

An attempted exact-name interning pass was rejected after measurement: it left the 147,386,416-byte
cache unchanged and did not improve the 58-second internal build. The experiment was not committed.

## Limitations and next evaluation

This pilot has only five goals, one context per arm, and no randomized seeds. The targets are
representative but not hidden from the benchmark designer. Agent scheduling and tool-call overhead
also dominate the subsecond native search time.

A larger evaluation should use at least 24 pilot tasks and then a hidden set near 100 tasks. It
should stratify:

- obvious and non-obvious theorem names;
- repeated final names across namespaces;
- declarations, generated projections, and constructors;
- upstream, downstream, and one- or two-hop navigation;
- several mathematical domains and graph degrees.

Keep model, prompt, tool budget, timeout, filesystem state, and source-verification requirements
paired. Add a realistic third arm that may combine LeanReach and `rg`; the tools are complementary,
and that arm is likely to be the best practical workflow.
