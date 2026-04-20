"""Regenerate tables/ci.tex from real bootstrap on the saturated archive.

Uses uncertainty.bootstrap_ci on per-pair finite-difference populations
for L, K, ell, G under both the identity defense and the GP-smooth
oblique defense.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, "/Users/mbhatt/stuff/trilemma_validator/src")

from trilemma_validator.loader import Heatmap
from trilemma_validator.defenses import get_defense, IdentityDefense, GPSmoothObliqueDefense
from trilemma_validator.uncertainty import bootstrap_ci


def load_heatmap_from_archive(p: Path) -> Heatmap:
    with open(p) as f:
        a = json.load(f)
    gs = a["grid_size"]
    values = np.full((gs, gs), np.nan)
    for c in a["cells"]:
        i, j = c["grid_position"]
        values[i, j] = float(c["quality"])
    return Heatmap(values=values, grid_size=gs, cell_width=1.0 / gs)


def h_dist(gs: int, a: np.ndarray, b: np.ndarray) -> float:
    """L2 on normalized [0,1]^2."""
    h = 1.0 / (gs - 1)
    return h * float(np.sqrt(((a - b) ** 2).sum()))


def L_pairs(hm: Heatmap) -> np.ndarray:
    """All per-pair |f(u)-f(v)|/d(u,v) ratios over filled cells."""
    filled = np.argwhere(hm.filled_mask)
    gs = hm.grid_size
    out = []
    for i in range(len(filled)):
        for j in range(i + 1, len(filled)):
            u, v = filled[i], filled[j]
            d = h_dist(gs, u.astype(float), v.astype(float))
            if d > 0:
                df = abs(hm.values[u[0], u[1]] - hm.values[v[0], v[1]])
                out.append(df / d)
    return np.array(out)


def G_pairs(hm: Heatmap, tau: float) -> np.ndarray:
    """Oriented safe→unsafe (f(v)-f(u))/d(u,v) over filled pairs."""
    filled = np.argwhere(hm.filled_mask)
    gs = hm.grid_size
    out = []
    for i in range(len(filled)):
        for j in range(len(filled)):
            if i == j:
                continue
            u, v = filled[i], filled[j]
            fu = hm.values[u[0], u[1]]
            fv = hm.values[v[0], v[1]]
            if fu < tau < fv:
                d = h_dist(gs, u.astype(float), v.astype(float))
                if d > 0:
                    out.append((fv - fu) / d)
    return np.array(out)


def K_pairs(hm: Heatmap, defense_targets: np.ndarray) -> np.ndarray:
    filled = np.argwhere(hm.filled_mask)
    gs = hm.grid_size
    out = []
    for i in range(len(filled)):
        for j in range(i + 1, len(filled)):
            u, v = filled[i], filled[j]
            du = defense_targets[u[0], u[1]]
            dv = defense_targets[v[0], v[1]]
            dist_uv = h_dist(gs, u.astype(float), v.astype(float))
            dist_dudv = h_dist(gs, du.astype(float), dv.astype(float))
            if dist_uv > 0:
                out.append(dist_dudv / dist_uv)
    return np.array(out)


def ell_ratios(hm: Heatmap, defense_targets: np.ndarray) -> np.ndarray:
    """Per-cell |f(D(x))-f(x)|/d(D(x),x) for cells where D(x)!=x and D(x) is filled."""
    filled = np.argwhere(hm.filled_mask)
    gs = hm.grid_size
    out = []
    for x in filled:
        dx = defense_targets[x[0], x[1]]
        if tuple(dx) == tuple(x):
            continue
        if not hm.filled_mask[dx[0], dx[1]]:
            continue
        d = h_dist(gs, x.astype(float), dx.astype(float))
        if d > 0:
            out.append(abs(hm.values[dx[0], dx[1]] - hm.values[x[0], x[1]]) / d)
    return np.array(out)


def main() -> int:
    archive = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json")
    hm = load_heatmap_from_archive(archive)
    tau = 0.5
    B = 1000
    seed = 0

    L_vals = L_pairs(hm)
    G_vals = G_pairs(hm, tau)
    print(f"L population: n={len(L_vals)}, max={L_vals.max():.4f}, min={L_vals.min():.4f}", file=sys.stderr)
    print(f"G population: n={len(G_vals)}, max={G_vals.max():.4f}", file=sys.stderr)

    rows = []
    for name, defense in [("identity", IdentityDefense()),
                          ("GP-smooth oblique", GPSmoothObliqueDefense())]:
        dm = defense.build(hm, tau)
        K_vals = K_pairs(hm, dm.targets)
        e_vals = ell_ratios(hm, dm.targets)
        print(f"[{name}] K pop: n={len(K_vals)}, max={K_vals.max() if len(K_vals) else 0:.4f}", file=sys.stderr)
        print(f"[{name}] ell pop: n={len(e_vals)}, max={e_vals.max() if len(e_vals) else 0:.4f}", file=sys.stderr)

        L_med, L_lo, L_hi = bootstrap_ci(L_vals, B=B, seed=seed)
        K_med, K_lo, K_hi = bootstrap_ci(K_vals, B=B, seed=seed)
        e_med, e_lo, e_hi = bootstrap_ci(e_vals, B=B, seed=seed)
        G_med, G_lo, G_hi = bootstrap_ci(G_vals, B=B, seed=seed)

        def fmt(v):
            if v is None or (isinstance(v, float) and np.isnan(v)):
                return "--"
            return f"{v:.3f}"

        rows.append((name, L_med, L_lo, L_hi, K_med, K_lo, K_hi, e_med, e_lo, e_hi, G_med, G_lo, G_hi))

    # Save raw values
    out_json = {
        "B": B, "seed": seed, "tau": tau,
        "archive": str(archive),
        "rows": [
            {
                "defense": r[0],
                "L":   {"med": r[1],  "lo": r[2],  "hi": r[3]},
                "K":   {"med": r[4],  "lo": r[5],  "hi": r[6]},
                "ell": {"med": r[7],  "lo": r[8],  "hi": r[9]},
                "G":   {"med": r[10], "lo": r[11], "hi": r[12]},
            }
            for r in rows
        ],
    }
    out_path = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/bootstrap_ci.json")
    out_path.write_text(json.dumps(out_json, indent=2, default=lambda x: None if (isinstance(x, float) and np.isnan(x)) else x))
    print(f"wrote {out_path}", file=sys.stderr)

    # Emit tables/ci.tex
    lines = [
        "% Bootstrap confidence intervals (B = 1000 resamples, seed=0,",
        "% percentile CI at 95%) on the saturated gpt-3.5-turbo-0125 archive.",
        "% Populations: L = per-pair |f(u)-f(v)|/d(u,v) over all filled pairs.",
        "% K = per-pair dist(D(u),D(v))/dist(u,v) over displaced filled pairs.",
        "% ell = per-cell |f(D(x))-f(x)|/d(D(x),x) for filled cells with D(x)!=x and D(x) filled.",
        "% G = per-pair (f(v)-f(u))/d(u,v) over oriented safe->unsafe filled pairs.",
        "% Raw bootstrap values in",
        "% trilemma_validator/live_runs/gpt35_turbo_t05_saturated/bootstrap_ci.json.",
        "\\footnotesize",
        "\\setlength{\\tabcolsep}{3pt}",
        "\\begin{tabular}{l r c r c r c r c}",
        "\\toprule",
        "defense & $L_{\\mathrm{med}}$ & $L$ CI & $K_{\\mathrm{med}}$ & $K$ CI & $\\ell_{\\mathrm{med}}$ & $\\ell$ CI & $G_{\\mathrm{med}}$ & $G$ CI \\\\",
        "\\midrule",
    ]
    for r in rows:
        name = r[0]
        L_med, L_lo, L_hi = r[1], r[2], r[3]
        K_med, K_lo, K_hi = r[4], r[5], r[6]
        e_med, e_lo, e_hi = r[7], r[8], r[9]
        G_med, G_lo, G_hi = r[10], r[11], r[12]
        def f(v): return "--" if v is None or (isinstance(v, float) and np.isnan(v)) else f"{v:.3f}"
        lines.append(f"{name} & {f(L_med)} & $[{f(L_lo)}, {f(L_hi)}]$ & {f(K_med)} & $[{f(K_lo)}, {f(K_hi)}]$ & {f(e_med)} & $[{f(e_lo)}, {f(e_hi)}]$ & {f(G_med)} & $[{f(G_lo)}, {f(G_hi)}]$ \\\\")
    lines += ["\\bottomrule", "\\end{tabular}"]
    Path("/Users/mbhatt/stuff/tables/ci.tex").write_text("\n".join(lines) + "\n")
    print("wrote /Users/mbhatt/stuff/tables/ci.tex", file=sys.stderr)


if __name__ == "__main__":
    sys.exit(main() or 0)
