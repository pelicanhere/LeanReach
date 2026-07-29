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
    samples: dict[str, dict[str, list[float]]] = defaultdict(
        lambda: defaultdict(list)
    )
    for row in csv.DictReader(source.open(encoding="utf-8")):
        samples[row["stage"]][row["tool"]].append(float(row["latency_ms"]))

    stages = list(samples)
    values = [
        value
        for tools in samples.values()
        for measurements in tools.values()
        for value in measurements
    ]
    low = min(values, default=0.1)
    high = max(values, default=1)
    log_low = math.floor(math.log10(max(0.1, low)))
    log_high = math.ceil(math.log10(high))
    width, height = 1600, 680
    left, right, top, bottom = 75, 210, 55, 245
    plot_width, plot_height = width - left - right, height - top - bottom

    def x(stage: int, tool: int) -> float:
        center = left + (stage + 0.5) * plot_width / max(1, len(stages))
        return center + (tool - 1) * 5

    def y(value: float) -> float:
        position = (math.log10(max(0.1, value)) - log_low) / max(
            1, log_high - log_low
        )
        return top + plot_height * (1 - position)

    grid = []
    for exponent in range(log_low, log_high + 1):
        value = 10**exponent
        row = y(value)
        grid.append(
            f'<line x1="{left}" y1="{row:.1f}" x2="{width-right}" '
            f'y2="{row:.1f}" stroke="#e5e7eb"/>'
            f'<text x="{left-10}" y="{row+4:.1f}" text-anchor="end" '
            f'font-size="11">{value:g} ms</text>'
        )

    points, labels = [], []
    tools = tuple(COLORS)
    for stage_index, stage in enumerate(stages):
        center = x(stage_index, 1)
        for tool_index, tool in enumerate(tools):
            measurements = samples[stage].get(tool, [])
            for sample_index, value in enumerate(measurements):
                jitter = (sample_index % 5 - 2) * 0.65
                points.append(
                    f'<circle cx="{x(stage_index, tool_index)+jitter:.1f}" '
                    f'cy="{y(value):.1f}" r="2.2" fill="{COLORS[tool]}" '
                    f'fill-opacity=".42"><title>{html.escape(stage)} · '
                    f'{tool}: {value:.3f} ms</title></circle>'
                )
            if measurements:
                median = statistics.median(measurements)
                points.append(
                    f'<rect x="{x(stage_index, tool_index)-3:.1f}" '
                    f'y="{y(median)-3:.1f}" width="6" height="6" '
                    f'fill="{COLORS[tool]}"><title>median: '
                    f'{median:.3f} ms</title></rect>'
                )
        labels.append(
            f'<text transform="translate({center:.1f},{height-bottom+12}) '
            f'rotate(55)" text-anchor="start" font-size="10">'
            f'{html.escape(stage)}</text>'
        )

    legend = "".join(
        f'<circle cx="{width-right+25}" cy="{top+8+i*20}" r="4" '
        f'fill="{COLORS[tool]}"/><text x="{width-right+38}" '
        f'y="{top+12+i*20}" font-size="11">{tool}</text>'
        for i, tool in enumerate(tools)
    )
    grid_svg = "\n".join(grid)
    points_svg = "\n".join(points)
    labels_svg = "\n".join(labels)
    target.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">
<rect width="100%" height="100%" fill="white"/>
<text x="{left}" y="28" font-size="18" font-family="sans-serif">Distinct-query latency samples (log scale)</text>
{grid_svg}
<line x1="{left}" y1="{top+plot_height}" x2="{width-right}" y2="{top+plot_height}" stroke="#444"/>
{points_svg}
{labels_svg}
{legend}
<text x="{width-right+18}" y="{top+82}" font-size="10">square = median</text>
</svg>""",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
