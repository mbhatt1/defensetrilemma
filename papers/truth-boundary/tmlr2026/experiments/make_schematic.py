"""Schematic figure: the boundary coupling theorem in one picture.

A path through a connected representation space from a strictly true
query to a strictly false one. The realized truth field crosses zero,
separation forces confidence above tau on the true side and below on
the false side, so confidence crosses tau, and the two crossings
coincide at the coupled point, surrounded by the ambiguity tube.
Same palette as the data figures.
"""

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE = "#3B6FB6"    # truth field
ORANGE = "#C4552D"  # confidence
INK = "#333333"
MUTED = "#8A8A8A"
TRUE_BG = "#3A7D44"
FALSE_BG = "#C4552D"

x = np.linspace(0, 1, 400)
x0 = 0.52
dF = np.tanh(6 * (x - x0))                     # truth field, - true / + false
conf = 0.5 - 0.42 * np.tanh(6 * (x - x0))      # confidence, crosses 1/2 at x0
tube = 0.10

fig, ax = plt.subplots(figsize=(7.0, 2.6))

# region shading
ax.axvspan(0, x0 - tube, color=TRUE_BG, alpha=0.07, lw=0)
ax.axvspan(x0 + tube, 1, color=FALSE_BG, alpha=0.07, lw=0)
ax.axvspan(x0 - tube, x0 + tube, color=MUTED, alpha=0.15, lw=0)

# reference lines
ax.axhline(0.5, color=MUTED, lw=0.9, ls=(0, (4, 3)))
ax.axhline(0.0, color=MUTED, lw=0.9, ls=(0, (1, 2)))
ax.axvline(x0, color=INK, lw=0.8, ls=(0, (1, 2)))

# fields
ax.plot(x, dF, color=BLUE, lw=2.2)
ax.plot(x, conf, color=ORANGE, lw=2.2)

# coupled point markers
ax.plot([x0], [0.0], "o", color=BLUE, ms=6, zorder=5)
ax.plot([x0], [0.5], "o", color=ORANGE, ms=6, zorder=5)

# annotations
ax.annotate(r"truth field $\delta_F$", xy=(0.88, 0.86), color=BLUE,
            fontsize=10, ha="center")
ax.annotate(r"confidence $c$", xy=(0.88, -0.10), color=ORANGE,
            fontsize=10, ha="center")
ax.annotate(r"$\tau = \frac{1}{2}$", xy=(0.015, 0.56), color=MUTED,
            fontsize=9)
ax.annotate(r"$\delta_F = 0$", xy=(0.015, 0.045), color=MUTED,
            fontsize=9)
ax.annotate("strictly true\nseparation forces $c > \\tau$",
            xy=(0.16, -0.72), color="#2E6337", fontsize=9, ha="center")
ax.annotate("strictly false\nseparation forces $c < \\tau$",
            xy=(0.84, 0.36), color="#9C4426", fontsize=9, ha="center")
ax.annotate("coupled point $x_0$\n$c = \\tau$ and $\\delta_F = 0$",
            xy=(x0, 0.25), xytext=(0.30, 0.72), fontsize=9.5,
            color=INK, ha="center",
            arrowprops=dict(arrowstyle="->", color=INK, lw=0.9))
ax.annotate("ambiguity\ntube", xy=(x0, -0.92), fontsize=8.5,
            color=MUTED, ha="center")

ax.set_xlim(0, 1)
ax.set_ylim(-1.05, 1.05)
ax.set_xticks([])
ax.set_yticks([])
for side in ["top", "right", "left"]:
    ax.spines[side].set_visible(False)
ax.spines["bottom"].set_color(MUTED)
ax.set_xlabel("a continuous path through connected representation "
              "space, true query to false query", fontsize=9.5,
              color=INK)

fig.tight_layout(pad=0.4)
fig.savefig("schematic_coupling.pdf", bbox_inches="tight")
fig.savefig("schematic_coupling.png", dpi=200, bbox_inches="tight")
print("saved schematic_coupling.pdf/.png")
