from __future__ import annotations

import argparse
import csv
import json
import statistics
import subprocess
import threading
import time
from pathlib import Path


QUERIES = (
    "padicValuation_cast",
    "surjective_padicValuation",
    "stationaryPoint_spec",
    "equiv_zero_of_val_eq_of_equiv_zero",
    "norm_eq_zpow_neg_valuation",
    "norm_values_discrete",
    "eq_padic_norm'",
    "exi_rat_seq_conv_cauchy",
    "norm_intCast_lt_one_iff",
)

SUBSTRING_QUERIES = (
    "span_image",
    "localization_atprime",
    "orderiso",
    "measurable_equiv",
    "continuouslinearmap",
    "finite_dimensional",
    "polynomial.derivative",
    "convexhull",
    "aestrongly",
    "integral_comp",
)


def elapsed_ms(started: float) -> float:
    return (time.perf_counter() - started) * 1000


def measure_process(
    command: list[str], timeout: float, capture: bool = True
) -> tuple[float, str]:
    started = time.perf_counter()
    result = subprocess.run(
        command,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE if capture else subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    elapsed = elapsed_ms(started)
    if result.returncode:
        raise RuntimeError(f"{' '.join(command)} failed:\n{result.stderr}")
    return elapsed, result.stdout or ""


def measure_session(
    executable: Path, queries: tuple[str, ...], timeout: float
) -> list[tuple[float, int]]:
    process = subprocess.Popen(
        [
            executable,
            "--module",
            "Mathlib",
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
        process.stdin.write(f"search {query}\n".encode())
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
        for query in queries:
            started = time.perf_counter()
            data = json.loads(exchange(query))
            samples.append((elapsed_ms(started), len(data["items"])))
        process.stdin.write(b"\n")
        process.stdin.flush()
        process.wait(timeout=timeout)
    finally:
        watchdog.cancel()
        if process.poll() is None:
            process.kill()
    return samples


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Benchmark a chain of distinct, first-use declaration searches."
    )
    parser.add_argument("--stage", default="baseline")
    parser.add_argument("--output", default="Benchmarks/latest.csv")
    parser.add_argument("--history", default="Benchmarks/history.csv")
    parser.add_argument("--append-history", action="store_true")
    parser.add_argument("--skip-session", action="store_true")
    parser.add_argument("--query-set", choices=("leaf", "substring"), default="leaf")
    parser.add_argument("--timeout", type=float, default=300)
    args = parser.parse_args()
    queries = SUBSTRING_QUERIES if args.query_set == "substring" else QUERIES

    root = Path(__file__).resolve().parent.parent
    executable = root / ".lake/build/bin/leanreach.exe"
    mathlib = root / ".lake/packages/mathlib/Mathlib"
    if not executable.exists():
        raise SystemExit("Run 'lake build' first.")

    measure_process([executable, "--help"], args.timeout)
    measure_process(
        [
            executable,
            "--module",
            "Mathlib",
            "search",
            "__leanreach_benchmark_ready__",
            "--json",
        ],
        args.timeout,
    )
    measure_process(["rg", "--version"], args.timeout)
    rows = []
    if not args.skip_session:
        session = measure_session(executable, queries, args.timeout)
        for query, (latency, found) in zip(queries, session, strict=True):
            rows.append((query, "leanreach_session", latency, found))
    for query in queries:
        latency, output = measure_process(
            [
                executable,
                "--module",
                "Mathlib",
                "search",
                query,
                "--limit",
                "10",
                "--json",
            ],
            args.timeout,
        )
        rows.append((query, "leanreach_process", latency, len(json.loads(output)["items"])))
    for query in queries:
        latency, _ = measure_process(
            ["rg", "-n", "-i", "--glob", "*.lean", query, str(mathlib)],
            args.timeout,
            capture=False,
        )
        rows.append((query, "rg", latency, 1))

    records = [
        {
            "stage": args.stage,
            "query": query,
            "tool": tool,
            "latency_ms": f"{latency:.3f}",
            "found": found,
            "note": "distinct query with fully precomputed module PP sidecars",
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
        for tool in ("leanreach_session", "leanreach_process", "rg")
        if any(row_tool == tool for _, row_tool, _, _ in rows)
    }
    rg_median = statistics.median(by_tool["rg"])
    for tool, samples in by_tool.items():
        total = sum(samples)
        median = statistics.median(samples)
        ratio = median / rg_median
        print(
            f"{tool:18} total={total:9.3f}ms "
            f"median={median:8.3f}ms ratio={ratio:7.3%}"
        )


if __name__ == "__main__":
    main()
