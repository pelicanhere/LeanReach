from __future__ import annotations

import csv
import html
import sys
from collections import defaultdict
from pathlib import Path


def main() -> None:
    source = Path(sys.argv[1] if len(sys.argv) > 1 else "Benchmarks/history.csv")
    target = Path(sys.argv[2] if len(sys.argv) > 2 else "Benchmarks/history.svg")
    rows = list(csv.DictReader(source.open(encoding="utf-8")))
    values: dict[str, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
    for row in rows:
        if row["metric"] != "end_to_end":
            continue
        values[row["commit"]][row["tool"]].append(float(row["median_ms"]))

    commits = list(values)
    means = {
        commit: {
            tool: sum(samples) / len(samples)
            for tool, samples in tools.items()
        }
        for commit, tools in values.items()
    }
    maximum = max((value for tools in means.values() for value in tools.values()), default=1)
    width, height, margin = max(640, len(commits) * 150 + 120), 420, 60
    chart_height = height - 2 * margin
    colors = {"leanreach": "#2563eb", "rg": "#f97316"}
    bars = []
    labels = []
    for index, commit in enumerate(commits):
        center = margin + 75 + index * 150
        for offset, tool in ((-24, "leanreach"), (24, "rg")):
            value = means[commit].get(tool, 0)
            bar_height = value / maximum * chart_height
            x, y = center + offset - 18, height - margin - bar_height
            bars.append(
                f'<rect x="{x:.1f}" y="{y:.1f}" width="36" height="{bar_height:.1f}" '
                f'fill="{colors[tool]}"><title>{tool}: {value:.2f} ms</title></rect>'
            )
            labels.append(
                f'<text x="{center + offset:.1f}" y="{y - 6:.1f}" text-anchor="middle" '
                f'font-size="11">{value:.1f}</text>'
            )
        labels.append(
            f'<text x="{center}" y="{height - margin + 22}" text-anchor="middle" '
            f'font-size="12">{html.escape(commit[:9])}</text>'
        )
    svg = f"""<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">
<rect width="100%" height="100%" fill="white"/>
<text x="{margin}" y="28" font-size="18" font-family="sans-serif">Median end-to-end time (lower is better)</text>
<line x1="{margin}" y1="{height-margin}" x2="{width-margin}" y2="{height-margin}" stroke="#444"/>
{''.join(bars)}
{''.join(labels)}
<rect x="{width-170}" y="18" width="12" height="12" fill="{colors['leanreach']}"/>
<text x="{width-152}" y="29" font-size="12">LeanReach</text>
<rect x="{width-82}" y="18" width="12" height="12" fill="{colors['rg']}"/>
<text x="{width-64}" y="29" font-size="12">rg</text>
</svg>"""
    target.write_text(svg, encoding="utf-8")


if __name__ == "__main__":
    main()
