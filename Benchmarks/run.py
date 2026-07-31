from __future__ import annotations

import argparse
import csv
import json
import os
import statistics
import subprocess
import threading
import time
from pathlib import Path


def exact_queries(*queries: str) -> tuple[tuple[str, str], ...]:
    return tuple((query, query) for query in queries)


SESSION_QUERIES = exact_queries(
    "span_eq_bot",
    "rootSet_derivative_subset_convexHull_rootSet",
    "isCompact_convexHull",
    "ideal_oper_maxTrivSubmodule_eq_bot",
    "spanSingleton_eq_zero_iff",
    "ker_map_of_surjective",
    "krullDimLE_of_isLocalization_maximal",
    "range_asIdeal",
    "coeff_Φ_ne_zero",
)

PROCESS_QUERIES = (
    *exact_queries(
        "isDomain_of_atPrime",
        "of_finite_maximals",
        "of_isLocalization_maximal",
        "natDegree_Φ_le",
        "intermediate_value_Icc",
        "AntitoneOn.image_Icc_subset",
        "rootSet_derivative",
        "padicValuation_cast",
        "surjective_padicValuation",
    ),
    ("(?i)^.*surject.*padic.*$", "surjective_padicValuation"),
    *exact_queries("stationaryPoint_spec"),
)


def elapsed_ms(started: float) -> float:
    return (time.perf_counter() - started) * 1000


def result_items(data: dict) -> list[dict]:
    if "items" in data:
        return data["items"]
    return [data["target"], *data["upstream"], *data["downstream"]]


def measure_process(command: list[str | Path], timeout: float) -> tuple[float, str]:
    started = time.perf_counter()
    result = subprocess.run(
        command,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    elapsed = elapsed_ms(started)
    if result.returncode:
        raise RuntimeError(f"{' '.join(map(str, command))} failed:\n{result.stderr}")
    return elapsed, result.stdout or ""


def measure_session(
    executable: Path,
    queries: tuple[tuple[str, str], ...],
    timeout: float,
    module_args: list[str],
) -> list[tuple[float, int]]:
    process = subprocess.Popen(
        [
            executable,
            *module_args,
            "--limit",
            "10",
            "--interactive",
            "--json",
        ],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        bufsize=0,
    )
    assert process.stdin and process.stdout
    timed_out = threading.Event()

    def stop() -> None:
        timed_out.set()
        process.kill()

    watchdog = threading.Timer(timeout, stop)
    watchdog.daemon = True
    watchdog.start()
    samples = []

    def exchange(query: str) -> bytes:
        process.stdin.write(f"{query}\n".encode())
        process.stdin.flush()
        line = process.stdout.readline()
        if line:
            return line
        if timed_out.is_set():
            raise TimeoutError("LeanReach session timed out")
        raise RuntimeError(
            f"LeanReach session stopped with exit code {process.poll()}"
        )

    try:
        json.loads(exchange("__leanreach_benchmark_ready__"))
        for query, expected in queries:
            started = time.perf_counter()
            data = json.loads(exchange(query))
            items = result_items(data)
            if not any(expected in item["name"] for item in items):
                raise RuntimeError(
                    f"LeanReach session did not find {expected!r} for {query!r}"
                )
            samples.append((elapsed_ms(started), len(items)))
        process.stdin.write(b"\n")
        process.stdin.flush()
        process.wait(timeout=timeout)
    finally:
        watchdog.cancel()
        if process.poll() is None:
            process.kill()
            process.wait()
    return samples


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Benchmark a fixed corpus of distinct declaration searches."
    )
    parser.add_argument("--stage", default="baseline")
    parser.add_argument("--output", default="Benchmarks/latest.csv")
    parser.add_argument("--history", default="Benchmarks/history.csv")
    parser.add_argument("--append-history", action="store_true")
    parser.add_argument("--skip-session", action="store_true")
    parser.add_argument(
        "--auto-roots",
        action="store_true",
        help="benchmark the auto-detected local view instead of Mathlib alone",
    )
    parser.add_argument(
        "--query-set", choices=("all", "session", "process"), default="all"
    )
    parser.add_argument("--timeout", type=float, default=300)
    args = parser.parse_args()
    run_session = args.query_set in ("all", "session") and not args.skip_session
    run_process = args.query_set in ("all", "process")

    root = Path(__file__).resolve().parent.parent
    executable = root / ".lake/build/bin" / (
        "leanreach.exe" if os.name == "nt" else "leanreach"
    )
    mathlib = root / ".lake/packages/mathlib/Mathlib"
    if not executable.exists():
        raise SystemExit("Run 'lake build' first.")
    module_args = [] if args.auto_roots else ["--module", "Mathlib"]

    measure_process([executable, "--help"], args.timeout)
    measure_process(
        [
            executable,
            *module_args,
            "__leanreach_benchmark_ready__",
            "--json",
        ],
        args.timeout,
    )
    measure_process(["rg", "--version"], args.timeout)
    measure_process(
        [
            "rg",
            "--count-matches",
            "--glob",
            "*.lean",
            "theorem|lemma|def",
            mathlib,
        ],
        args.timeout,
    )
    rows = []
    if run_session:
        session = measure_session(
            executable, SESSION_QUERIES, args.timeout, module_args
        )
        for (query, _), (latency, found) in zip(
            SESSION_QUERIES, session, strict=True
        ):
            rows.append((query, "leanreach_session", latency, found))
    if run_process:
        for query, expected in PROCESS_QUERIES:
            latency, output = measure_process(
                [
                    executable,
                    *module_args,
                    query,
                    "--limit",
                    "10",
                    "--json",
                ],
                args.timeout,
            )
            data = json.loads(output)
            items = result_items(data)
            if not any(expected in item["name"] for item in items):
                raise RuntimeError(
                    f"LeanReach process did not find {expected!r} for {query!r}"
                )
            rows.append((query, "leanreach_process", latency, len(items)))
    for queries, tool in (
        (SESSION_QUERIES if run_session else (), "rg_session"),
        (PROCESS_QUERIES if run_process else (), "rg_process"),
    ):
        for query, expected in queries:
            latency, output = measure_process(
                ["rg", "-n", "--glob", "*.lean", query, str(mathlib)],
                args.timeout,
            )
            if expected not in output:
                raise RuntimeError(f"rg did not find {expected!r} for {query!r}")
            rows.append((query, tool, latency, len(output.splitlines())))

    if not rows:
        raise SystemExit("No benchmark set selected.")
    view = "auto-detected roots" if args.auto_roots else "Mathlib root"
    records = [
        {
            "stage": args.stage,
            "query": query,
            "tool": tool,
            "latency_ms": f"{latency:.3f}",
            "found": found,
            "note": f"one use per run from a fixed corpus with complete PP sidecars; {view}",
        }
        for query, tool, latency, found in rows
    ]
    fields = tuple(records[0])
    output_path = root / args.output
    with output_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fields)
        writer.writeheader()
        writer.writerows(records)
    if args.append_history:
        history_path = root / args.history
        write_header = not history_path.exists()
        with history_path.open("a", newline="", encoding="utf-8") as stream:
            writer = csv.DictWriter(stream, fields)
            if write_header:
                writer.writeheader()
            writer.writerows(records)

    by_tool = {
        tool: [latency for _, row_tool, latency, _ in rows if row_tool == tool]
        for tool in (
            "leanreach_session",
            "rg_session",
            "leanreach_process",
            "rg_process",
        )
        if any(row_tool == tool for _, row_tool, _, _ in rows)
    }
    for tool, samples in by_tool.items():
        total = sum(samples)
        median = statistics.median(samples)
        print(
            f"{tool:18} total={total:9.3f}ms "
            f"median={median:8.3f}ms"
        )
    for leanreach, rg in (
        ("leanreach_session", "rg_session"),
        ("leanreach_process", "rg_process"),
    ):
        if leanreach in by_tool and rg in by_tool:
            ratio = statistics.median(by_tool[leanreach]) / statistics.median(
                by_tool[rg]
            )
            print(f"{leanreach:18} / {rg} median ratio={ratio:7.3%}")


if __name__ == "__main__":
    main()
