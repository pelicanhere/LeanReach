from __future__ import annotations

import csv
import html
import math
import statistics
import sys
from collections import defaultdict
from pathlib import Path


COLORS = {
    "leanreach_session": "#16a34a",
    "leanreach_process": "#2563eb",
    "rg": "#f97316",
}


def main() -> None:
    source = Path(sys.argv[1] if len(sys.argv) > 1 else "Benchmarks/history.csv")
    target = Path(sys.argv[2] if len(sys.argv) > 2 else "Benchmarks/history.svg")
    samples: dict[str, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
    for row in csv.DictReader(source.open(encoding="utf-8")):
        samples[row["stage"]][row["tool"]].append(float(row["latency_ms"]))
    medians = {
        stage: {tool: statistics.median(values) for tool, values in tools.items()}
        for stage, tools in samples.items()
    }
    stages = list(medians)
    tools = tuple(COLORS)
    maximum = max(
        (value for stage in medians.values() for value in stage.values()), default=1
    )
    log_max = math.log10(maximum + 1)
    width, height, margin = max(720, len(stages) * 220 + 160), 440, 70
    chart_height = height - 2 * margin
    bars, labels = [], []
    for stage_index, stage in enumerate(stages):
        center = margin + 110 + stage_index * 220
        for tool_index, tool in enumerate(tools):
            value = medians[stage].get(tool, 0)
            bar_height = math.log10(value + 1) / log_max * chart_height
            x = center + (tool_index - 1) * 48 - 18
            y = height - margin - bar_height
            bars.append(
                f'<rect x="{x}" y="{y:.1f}" width="36" height="{bar_height:.1f}" '
                f'fill="{COLORS[tool]}"><title>{tool}: {value:.3f} ms</title></rect>'
            )
            labels.append(
                f'<text x="{x + 18}" y="{y - 5:.1f}" text-anchor="middle" '
                f'font-size="10">{value:.2f}</text>'
            )
        rg = medians[stage].get("rg", 0)
        leanreach = medians[stage].get(
            "leanreach_session", medians[stage].get("leanreach_process", 0)
        )
        ratio = leanreach / rg if rg else 0
        label = "session" if "leanreach_session" in medians[stage] else "process"
        labels.append(
            f'<text x="{center}" y="{height - margin + 20}" text-anchor="middle" '
            f'font-size="12">{html.escape(stage)}</text>'
            f'<text x="{center}" y="{height - margin + 37}" text-anchor="middle" '
            f'font-size="11">{label}/rg {ratio:.2%}</text>'
        )
    legend = "".join(
        f'<rect x="{width - 205}" y="{16 + i * 18}" width="11" height="11" '
        f'fill="{COLORS[tool]}"/><text x="{width - 188}" y="{26 + i * 18}" '
        f'font-size="11">{tool}</text>'
        for i, tool in enumerate(tools)
    )
    target.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">
<rect width="100%" height="100%" fill="white"/>
<text x="{margin}" y="28" font-size="18" font-family="sans-serif">Distinct-query median latency (log scale)</text>
<line x1="{margin}" y1="{height-margin}" x2="{width-margin}" y2="{height-margin}" stroke="#444"/>
{''.join(bars)}{''.join(labels)}{legend}
</svg>""",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
