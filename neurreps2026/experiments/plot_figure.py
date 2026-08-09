"""Figure: boundary coupling along interpolation paths, per model.

Two rows of small multiples, one column per model, one axis per panel.
Row 1 shows the truth-probe field delta_F(alpha), normalized per path
by its endpoint scale. Row 2 shows the independent confidence head
c(alpha). Median across paths with an interquartile band. The vertical
line marks the mean probe zero crossing. The predictions are visible
directly. delta_F crosses zero, and c crosses 1/2 at the same place.
"""

import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE = "#3B6FB6"    # truth field row
ORANGE = "#C4552D"  # confidence row
INK = "#333333"
MUTED = "#8A8A8A"
GRID = "#DDDDDD"

results = json.load(open("results.json"))
models = [m for m in results if "error" not in results[m]]

fig, axes = plt.subplots(2, len(models), figsize=(2.6 * len(models), 3.4),
                         sharex=True)
if len(models) == 1:
    axes = axes.reshape(2, 1)

for j, name in enumerate(models):
    z = np.load(f"curves_{name}.npz")
    D, C, alphas = z["D"], z["C"], z["alphas"]
    scale = np.maximum(np.abs(D[:, [0]]), np.abs(D[:, [-1]]))
    Dn = D / scale
    cross = alphas[np.array([np.argmin(np.abs(d)) for d in D])].mean()

    for i, (Y, color, ylab, ref) in enumerate([
            (Dn, BLUE, r"truth field  $\delta_F$ (norm.)", 0.0),
            (C, ORANGE, r"confidence  $c$", 0.5)]):
        ax = axes[i, j]
        lo, mid, hi = np.percentile(Y, [25, 50, 75], axis=0)
        ax.fill_between(alphas, lo, hi, color=color, alpha=0.18, lw=0)
        ax.plot(alphas, mid, color=color, lw=1.6)
        ax.axhline(ref, color=MUTED, lw=0.8, ls=(0, (4, 3)))
        ax.axvline(cross, color=MUTED, lw=0.8, ls=(0, (1, 2)))
        ax.spines[["top", "right"]].set_visible(False)
        ax.spines[["left", "bottom"]].set_color(GRID)
        ax.tick_params(colors=INK, labelsize=7, width=0.6)
        ax.set_xlim(0, 1)
        if i == 0:
            ax.set_title(f"{name}\nprobe acc "
                         f"{results[name]['probe_test_acc']:.2f}",
                         fontsize=8, color=INK)
            ax.set_ylim(-1.6, 1.6)
        else:
            ax.set_ylim(-0.05, 1.05)
            ax.set_xlabel(r"interpolation  $\alpha$  (true $\to$ false)",
                          fontsize=7.5, color=INK)
        if j == 0:
            ax.set_ylabel(ylab, fontsize=8, color=INK)

axes[0, 0].annotate("zero", xy=(0.02, 0.06), xycoords="axes fraction",
                    fontsize=6.5, color=MUTED)
axes[1, 0].annotate("threshold 1/2", xy=(0.02, 0.54),
                    xycoords="axes fraction", fontsize=6.5, color=MUTED)

fig.tight_layout(pad=0.6)
fig.savefig("boundary_coupling.pdf", bbox_inches="tight")
fig.savefig("boundary_coupling.png", dpi=200, bbox_inches="tight")
print("saved boundary_coupling.pdf/.png")
