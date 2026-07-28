from __future__ import annotations

import csv
import html
import sys
from pathlib import Path


def main() -> None:
    source = Path(sys.argv[1] if len(sys.argv) > 1 else "Benchmarks/pp_history.csv")
    target = Path(sys.argv[2] if len(sys.argv) > 2 else "Benchmarks/pp_history.svg")
    rows = list(csv.DictReader(source.open(encoding="utf-8")))
    maximum = max((float(row["latency_ms"]) for row in rows), default=1)
    width, height, margin = max(640, len(rows) * 170 + 120), 400, 70
    chart_height = height - 2 * margin
    bars = []
    labels = []
    for index, row in enumerate(rows):
        value = float(row["latency_ms"])
        bar_height = value / maximum * chart_height
        x = margin + 70 + index * 170
        y = height - margin - bar_height
        bars.append(
            f'<rect x="{x}" y="{y:.1f}" width="72" height="{bar_height:.1f}" '
            f'fill="#16a34a"><title>{html.escape(row["note"])}: {value:.0f} ms</title></rect>'
        )
        labels.append(
            f'<text x="{x + 36}" y="{y - 7:.1f}" text-anchor="middle" '
            f'font-size="12">{value / 1000:.2f}s</text>'
            f'<text x="{x + 36}" y="{height - margin + 20}" text-anchor="middle" '
            f'font-size="12">{html.escape(row["stage"])}</text>'
            f'<text x="{x + 36}" y="{height - margin + 37}" text-anchor="middle" '
            f'font-size="10">{row["modules"]} modules / {row["declarations"]} decls</text>'
        )
    target.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">
<rect width="100%" height="100%" fill="white"/>
<text x="{margin}" y="28" font-size="18" font-family="sans-serif">Cold PP construction and first-use latency</text>
<line x1="{margin}" y1="{height-margin}" x2="{width-margin}" y2="{height-margin}" stroke="#444"/>
{''.join(bars)}{''.join(labels)}
</svg>""",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
