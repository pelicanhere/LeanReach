from __future__ import annotations

import csv
import html
import math
import sys
from pathlib import Path


def latency_color(value: float) -> str:
    if value < 100:
        return "#16a34a"
    if value < 10_000:
        return "#2563eb"
    return "#dc2626"


def main() -> None:
    source = Path(sys.argv[1] if len(sys.argv) > 1 else "Benchmarks/pp_history.csv")
    target = Path(sys.argv[2] if len(sys.argv) > 2 else "Benchmarks/pp_history.svg")
    rows = list(csv.DictReader(source.open(encoding="utf-8")))
    values = [max(float(row["latency_ms"]), 1) for row in rows]
    width, height = 1280, 620
    left, right, top, bottom = 90, 35, 65, 125
    chart_width = width - left - right
    chart_height = height - top - bottom
    low_power = math.floor(math.log10(min(values, default=1)))
    high_power = math.ceil(math.log10(max(values, default=1)))
    power_span = max(1, high_power - low_power)

    def x_position(index: int) -> float:
        return left + chart_width * (index + 0.5) / max(1, len(rows))

    def y_position(value: float) -> float:
        fraction = (math.log10(max(value, 1)) - low_power) / power_span
        return top + chart_height * (1 - fraction)

    grid = []
    for power in range(low_power, high_power + 1):
        value = 10**power
        y = y_position(value)
        label = f"{value / 1000:g}s" if value >= 1000 else f"{value:g}ms"
        grid.append(
            f'<line x1="{left}" y1="{y:.1f}" x2="{width-right}" y2="{y:.1f}" '
            f'stroke="#d1d5db" stroke-dasharray="4 5"/>'
            f'<text x="{left-12}" y="{y+4:.1f}" text-anchor="end" '
            f'font-size="12">{label}</text>'
        )

    points = []
    labels = []
    label_stride = max(1, math.ceil(len(rows) / 16))
    for index, row in enumerate(rows):
        value = float(row["latency_ms"])
        x = x_position(index)
        y = y_position(value)
        tooltip = html.escape(
            f'{index + 1}. {row["stage"]}: {value:.0f} ms; '
            f'{row["modules"]} modules / {row["declarations"]} decls; {row["note"]}'
        )
        points.append(
            f'<circle cx="{x:.1f}" cy="{y:.1f}" r="5.5" '
            f'fill="{latency_color(value)}" stroke="white" stroke-width="1.5">'
            f"<title>{tooltip}</title></circle>"
        )
        if index % label_stride == 0 or index == len(rows) - 1:
            labels.append(
                f'<text x="{x:.1f}" y="{height-bottom+22}" '
                f'transform="rotate(45 {x:.1f} {height-bottom+22})" '
                f'text-anchor="start" font-size="10">{html.escape(row["stage"])}</text>'
            )

    target.write_text(
        f"""<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">
<rect width="100%" height="100%" fill="white"/>
<g font-family="sans-serif" fill="#111827">
<text x="{left}" y="30" font-size="19">Cache construction and query latency</text>
<text x="{left}" y="50" font-size="12" fill="#4b5563">Chronological benchmark history · logarithmic latency scale · hover points for details</text>
{''.join(grid)}
<line x1="{left}" y1="{height-bottom}" x2="{width-right}" y2="{height-bottom}" stroke="#374151"/>
<line x1="{left}" y1="{top}" x2="{left}" y2="{height-bottom}" stroke="#374151"/>
{''.join(points)}
{''.join(labels)}
<circle cx="{width-300}" cy="28" r="5" fill="#16a34a"/><text x="{width-288}" y="32" font-size="11">&lt; 100 ms</text>
<circle cx="{width-210}" cy="28" r="5" fill="#2563eb"/><text x="{width-198}" y="32" font-size="11">100 ms–10 s</text>
<circle cx="{width-100}" cy="28" r="5" fill="#dc2626"/><text x="{width-88}" y="32" font-size="11">≥ 10 s</text>
</g>
</svg>""",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
