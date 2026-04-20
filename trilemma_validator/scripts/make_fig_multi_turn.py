#!/usr/bin/env python3
"""Regenerate the multi-turn running-max figure with a tighter paper layout."""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


ROOT = Path("/Users/mbhatt/stuff")
TRAJECTORIES = ROOT / "trilemma_validator/live_runs/multi_turn/trajectories.json"
OUT = ROOT / "figures/multi_turn_plot.pdf"


def main() -> None:
    payload = json.load(TRAJECTORIES.open("r"))
    trajectories = payload["trajectories"]

    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.size": 9,
            "axes.labelsize": 10,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
            "legend.fontsize": 7,
        }
    )

    fig, ax = plt.subplots(figsize=(7.0, 3.9), dpi=200)
    cmap = plt.get_cmap("viridis")

    for idx, traj in enumerate(trajectories):
        running_max = traj["running_max"]
        xs = list(range(1, len(running_max) + 1))
        color = cmap(idx / max(1, len(trajectories) - 1))
        ax.plot(
            xs,
            running_max,
            marker="o",
            markersize=4.5,
            linewidth=1.5,
            color=color,
            alpha=0.9,
            label=f"T{idx + 1}",
        )

    ax.set_xlabel("Turn $k$")
    ax.set_ylabel(r"Running max $\max_{j \leq k}\,\mathrm{AD}_j$")
    ax.set_xticks(range(1, len(trajectories[0]["running_max"]) + 1))
    ax.set_ylim(0.0, 1.02)
    ax.grid(alpha=0.20, linewidth=0.6)
    ax.legend(
        loc="upper center",
        bbox_to_anchor=(0.5, -0.18),
        ncol=5,
        frameon=False,
        handlelength=1.8,
        columnspacing=1.0,
    )
    fig.tight_layout(pad=0.5)
    fig.savefig(OUT, dpi=200, bbox_inches="tight")
    plt.close(fig)
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
