from __future__ import annotations

import argparse
import csv
import json
import statistics
import subprocess
import threading
import time
from pathlib import Path


SESSION_QUERIES = (
    ("padicValuation_cast", "padicValuation_cast"),
    ("surjective_padicValuation", "surjective_padicValuation"),
    ("stationaryPoint_spec", "stationaryPoint_spec"),
    ("equiv_zero_of_val_eq_of_equiv_zero", "equiv_zero_of_val_eq_of_equiv_zero"),
    ("norm_eq_zpow_neg_valuation", "norm_eq_zpow_neg_valuation"),
    ("norm_values_discrete", "norm_values_discrete"),
    ("eq_padic_norm'", "eq_padic_norm'"),
    ("exi_rat_seq_conv_cauchy", "exi_rat_seq_conv_cauchy"),
    ("norm_intCast_lt_one_iff", "norm_intCast_lt_one_iff"),
)

PROCESS_QUERIES = (
    ("span_image", "span_image"),
    ("localization_.*maximal", "localization_maximal"),
    ("OrderIso", "OrderIso"),
    ("measurable_equiv", "measurable_equiv"),
    ("ContinuousLinearMap", "ContinuousLinearMap"),
    ("finite_dimensional", "finite_dimensional"),
    (r"Polynomial\.derivative", "Polynomial.derivative"),
    ("convexHull", "convexHull"),
    ("AEStrongly", "AEStrongly"),
    ("integral_comp", "integral_comp"),
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
    executable: Path, queries: tuple[tuple[str, str], ...], timeout: float
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
        for query, expected in queries:
            started = time.perf_counter()
            data = json.loads(exchange(query))
            if not any(expected in item["name"] for item in data["items"]):
                raise RuntimeError(
                    f"LeanReach session did not find {expected!r} for {query!r}"
                )
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
    parser.add_argument(
        "--query-set", choices=("all", "session", "process"), default="all"
    )
    parser.add_argument("--timeout", type=float, default=300)
    args = parser.parse_args()
    run_session = args.query_set in ("all", "session") and not args.skip_session
    run_process = args.query_set in ("all", "process")

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
    if run_session:
        session = measure_session(executable, SESSION_QUERIES, args.timeout)
        for (query, _), (latency, found) in zip(
            SESSION_QUERIES, session, strict=True
        ):
            rows.append((query, "leanreach_session", latency, found))
    if run_process:
        for query, expected in PROCESS_QUERIES:
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
            data = json.loads(output)
            if not any(expected in item["name"] for item in data["items"]):
                raise RuntimeError(
                    f"LeanReach process did not find {expected!r} for {query!r}"
                )
            rows.append((query, "leanreach_process", latency, len(data["items"])))
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
