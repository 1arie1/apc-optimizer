#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib>=3.8"]
# ///
"""Plot the sha256 optimizer runtime per merged PR from `sha256-runtime.csv`.

One point per merged PR, in merge order: the wall time CI measured for that PR's own
branch on the dedicated sha256 runner (the `runtime_branch_s` column), i.e. the runtime
main had once the PR landed.

    Benchmarks/history/plot_sha256_runtime.py            # writes sha256-runtime.{svg,png}
    Benchmarks/history/plot_sha256_runtime.py --show
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from pathlib import Path

import matplotlib
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent

SURFACE = "#fafaf8"
PANEL = "#f7f9f6"
GRID = "#e4e9e1"
INK = "#1a1a1a"
INK_MUTED = "#8b8b86"
SERIES = "#2f6fde"


def load(csv_path: Path) -> list[dict]:
    with csv_path.open(newline="") as fh:
        rows = list(csv.DictReader(fh))
    rows.sort(key=lambda r: r["merged_at"])
    return rows


def plot(rows: list[dict], out_prefix: Path, show: bool) -> None:
    xs = list(range(len(rows)))
    ys = [float(r["runtime_branch_s"]) for r in rows]
    when = [datetime.strptime(r["merged_at"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc) for r in rows]

    matplotlib.rcParams["font.family"] = ["Helvetica Neue", "Helvetica", "Arial", "DejaVu Sans"]
    matplotlib.rcParams["svg.fonttype"] = "none"

    fig, ax = plt.subplots(figsize=(11.0, 5.4))
    fig.patch.set_facecolor(SURFACE)
    ax.set_facecolor(PANEL)
    fig.subplots_adjust(left=0.085, right=0.975, top=0.845, bottom=0.215)

    ax.set_axisbelow(True)
    ax.grid(axis="y", color=GRID, linewidth=0.9)
    for spine in ax.spines.values():
        spine.set_color(GRID)
        spine.set_linewidth(0.9)
    ax.tick_params(length=0, pad=8)

    ax.plot(xs, ys, color=SERIES, linewidth=2.2, marker="o", markersize=9,
            markerfacecolor=SERIES, markeredgecolor=PANEL, markeredgewidth=2, clip_on=False,
            zorder=3)

    lo, hi = min(ys), max(ys)
    pad = (hi - lo) * 0.16
    ax.set_ylim(lo - pad, hi + pad)
    ax.set_xlim(-0.45, len(rows) - 0.55)
    ax.set_yticks([t for t in range(200, 1400, 200) if lo - pad <= t <= hi + pad])
    ax.set_yticklabels([f"{t}s" for t in ax.get_yticks()], color=INK_MUTED, fontsize=11)
    ax.set_ylabel("seconds", color=INK_MUTED, fontsize=11, labelpad=10)

    # Endpoints only — a number on every point would just be the table again.
    for i in (0, len(rows) - 1):
        ax.annotate(f"{ys[i]:.0f} s", (xs[i], ys[i]), textcoords="offset points",
                    xytext=(0, 16), ha="center", color=INK, fontsize=11, fontweight="bold")

    ax.set_xticks(xs)
    ax.set_xticklabels([f"#{r['pr']}" for r in rows], color=INK, fontsize=11.5, fontweight="bold")
    xaxis = ax.get_xaxis_transform()
    for x, t in zip(xs, when):
        ax.text(x, -0.075, f"{t:%b} {t.day}", transform=xaxis, ha="center", va="top",
                color=INK_MUTED, fontsize=10)
        ax.text(x, -0.135, t.strftime("%H:%M"), transform=xaxis, ha="center", va="top",
                color=INK_MUTED, fontsize=10)

    ax.set_title("runtime — optimizer wall time (sha256, 1 basic block)", loc="left",
                 color=INK, fontsize=13.5, fontweight="bold", pad=26)
    ax.text(0.0, 1.028, "as measured by CI on the dedicated sha256 runner", transform=ax.transAxes,
            color=INK_MUTED, fontsize=10.5, ha="left", va="bottom")
    fig.text(0.53, 0.045, "pull request · merge time UTC (chronological →)",
             color=INK_MUTED, fontsize=10.5, ha="center")

    for ext in ("svg", "png"):
        out = out_prefix.with_suffix(f".{ext}")
        fig.savefig(out, format=ext, dpi=200, facecolor=SURFACE)
        print(f"wrote {out}")
    if show:
        plt.show()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--csv", type=Path, default=HERE / "sha256-runtime.csv")
    ap.add_argument("--out-prefix", type=Path, default=HERE / "sha256-runtime")
    ap.add_argument("--show", action="store_true")
    args = ap.parse_args()
    plot(load(args.csv), args.out_prefix, args.show)


if __name__ == "__main__":
    main()
