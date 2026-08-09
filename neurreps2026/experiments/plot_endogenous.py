"""Figure: endogenous confidence along interpolation paths, per model.

Same layout as plot_figure.py but the confidence row is the model's own
p(true) from activation patching, restricted to decisive paths where
that signal actually separates the endpoints. Median across paths with
an interquartile band.
"""

import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE = "#3B6FB6"
GREEN = "#3A7D44"
INK = "#333333"
MUTED = "#8A8A8A"
GRID = "#DDDDDD"

results = json.load(open("results_endogenous.json"))
models = [m for m in results
          if "error" not in results[m].get("endogenous", {"error": 1})]

fig, axes = plt.subplots(2, len(models), figsize=(2.6 * len(models), 3.4),
                         sharex=True)
if len(models) == 1:
    axes = axes.reshape(2, 1)

for j, name in enumerate(models):
    z = np.load(f"curves_endog_{name}.npz")
    D, C, alphas, dec = z["D"], z["C"], z["alphas"], z["decisive"]
    if dec.any():
        D, C = D[dec], C[dec]
    scale = np.maximum(np.abs(D[:, [0]]), np.abs(D[:, [-1]]))
    Dn = D / scale
    cross = alphas[np.array([np.argmin(np.abs(d)) for d in D])].mean()

    for i, (Y, color, ylab, ref) in enumerate([
            (Dn, BLUE, r"truth field  $\delta_F$ (norm.)", 0.0),
            (C, GREEN, r"model's own $p(\mathrm{true})$", 0.5)]):
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
            n_dec = int(dec.sum())
            ax.set_title(f"{name}\n{n_dec} decisive paths",
                         fontsize=8, color=INK)
            ax.set_ylim(-1.6, 1.6)
        else:
            ax.set_xlabel(r"interpolation  $\alpha$  (true $\to$ false)",
                          fontsize=7.5, color=INK)
        if j == 0:
            ax.set_ylabel(ylab, fontsize=8, color=INK)

axes[0, 0].annotate("zero", xy=(0.02, 0.06), xycoords="axes fraction",
                    fontsize=6.5, color=MUTED)
axes[1, 0].annotate("threshold 1/2", xy=(0.02, 0.85),
                    xycoords="axes fraction", fontsize=6.5, color=MUTED)

fig.tight_layout(pad=0.6)
fig.savefig("endogenous_coupling.pdf", bbox_inches="tight")
fig.savefig("endogenous_coupling.png", dpi=200, bbox_inches="tight")
print("saved endogenous_coupling.pdf/.png")
