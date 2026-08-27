"""Regenerate judge_scatter.pdf with a tighter, paper-friendly layout."""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ARCHIVES = {
    "gpt-4.1": "/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json",
    "gpt-4o": "/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_judge_gpt4o/source_archive.json",
    "gpt-4.1-mini": "/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_judge_gpt41_mini/source_archive.json",
    "gpt-4o-mini": "/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_judge_gpt4o_mini/source_archive.json",
}


def load_cells(p: str) -> dict:
    with open(p) as f:
        a = json.load(f)
    return {tuple(c["grid_position"]): float(c["quality"]) for c in a["cells"]}


def main() -> int:
    per_judge = {name: load_cells(p) for name, p in ARCHIVES.items()}
    common = set.intersection(*[set(d.keys()) for d in per_judge.values()])
    keys = sorted(common)
    print(f"[judge_scatter] common cells: {len(keys)}")
    if len(keys) < 10:
        raise SystemExit("too few common cells to plot")

    names = list(ARCHIVES.keys())
    scores = np.array([[per_judge[n][k] for k in keys] for n in names])  # (4, n)

    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.size": 8,
            "axes.labelsize": 8,
            "xtick.labelsize": 7,
            "ytick.labelsize": 7,
        }
    )

    n = len(names)
    fig, axes = plt.subplots(n, n, figsize=(7.2, 7.2))
    for i in range(n):
        for j in range(n):
            ax = axes[i, j]
            if i == j:
                ax.hist(scores[i], bins=18, range=(0, 1), color="#5677A6", edgecolor="white")
                ax.set_xlim(0, 1)
                ax.set_yticks([])
            else:
                ax.scatter(scores[j], scores[i], s=14, alpha=0.6, color="#CF5C5C", edgecolors="none")
                ax.plot([0, 1], [0, 1], color="black", linewidth=0.6, linestyle=":", alpha=0.35)
                ax.set_xlim(0, 1)
                ax.set_ylim(0, 1)
                # Pearson r
                if scores[j].std() > 0 and scores[i].std() > 0:
                    r = float(np.corrcoef(scores[j], scores[i])[0, 1])
                    ax.text(
                        0.03,
                        0.92,
                        f"r={r:.2f}",
                        transform=ax.transAxes,
                        fontsize=7,
                        color="#333333",
                    )
            # Labels only on edges
            if j == 0:
                ax.set_ylabel(names[i])
            else:
                ax.set_yticklabels([])
            if i == n - 1:
                ax.set_xlabel(names[j])
            else:
                ax.set_xticklabels([])
            ax.grid(alpha=0.10, linewidth=0.5)
    fig.tight_layout(pad=0.5, w_pad=0.35, h_pad=0.35)

    out = Path("/Users/mbhatt/stuff/figures/judge_scatter.pdf")
    fig.savefig(str(out), format="pdf", bbox_inches="tight", dpi=200)
    print(f"[judge_scatter] wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
