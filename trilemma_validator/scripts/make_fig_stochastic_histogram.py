"""Stochastic-defense histograms with a tighter paper-friendly layout."""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def main() -> None:
    r = json.load(
        open("/Users/mbhatt/stuff/trilemma_validator/live_runs/stochastic/summary.json")
    )
    raw = r["raw_samples"]
    cells = sorted({s["cell_id"] for s in raw})
    cell_labels = {
        s["cell_id"]: tuple(per["grid_position"])
        for s in raw
        for per in r["per_cell"]
        if per["cell_id"] == s["cell_id"]
    }

    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.size": 9,
            "axes.titlesize": 9,
            "axes.labelsize": 9,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
        }
    )
    fig, axes = plt.subplots(1, len(cells), figsize=(10.0, 2.8), sharey=True)
    if len(cells) == 1:
        axes = [axes]

    for ax, cid in zip(axes, cells):
        samples = [s["ad"] for s in raw if s["cell_id"] == cid]
        ax.hist(samples, bins=12, range=(0, 1), color="#5677A6", edgecolor="white")
        ax.axvline(0.5, color="#C44E52", linestyle=":", linewidth=1.3)
        ax.set_title(f"{cell_labels[cid]}", pad=6)
        ax.set_xlabel(r"$f(D(x))$")
        ax.set_xlim(0, 1)
        ax.grid(axis="y", alpha=0.18, linewidth=0.6)
    axes[0].set_ylabel("count (30 samples)")

    fig.tight_layout(pad=0.6, w_pad=0.7)
    out = Path("/Users/mbhatt/stuff/figures/stochastic_histogram.pdf")
    fig.savefig(str(out), format="pdf", bbox_inches="tight", dpi=200)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
