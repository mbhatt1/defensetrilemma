"""Regenerate tables/ci.tex by bootstrapping the EXACT per-pair K and
per-cell ell populations stored in gp_smooth_result_oblique.json. This
guarantees the point estimates in the paper's narrative exactly match
the bootstrap populations — no code-path divergence.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, "/Users/mbhatt/stuff/trilemma_validator/src")
from trilemma_validator.loader import Heatmap
from trilemma_validator.uncertainty import bootstrap_ci


def L_pairs(values: np.ndarray, filled_mask: np.ndarray, gs: int) -> np.ndarray:
    h = 1.0 / (gs - 1)
    filled = np.argwhere(filled_mask)
    out = []
    for i in range(len(filled)):
        for j in range(i + 1, len(filled)):
            u, v = filled[i], filled[j]
            d = h * float(np.sqrt(((u - v) ** 2).sum()))
            if d > 0:
                out.append(abs(values[u[0], u[1]] - values[v[0], v[1]]) / d)
    return np.array(out)


def G_pairs(values: np.ndarray, filled_mask: np.ndarray, gs: int, tau: float) -> np.ndarray:
    h = 1.0 / (gs - 1)
    filled = np.argwhere(filled_mask)
    out = []
    for i in range(len(filled)):
        for j in range(len(filled)):
            if i == j: continue
            u, v = filled[i], filled[j]
            fu, fv = values[u[0], u[1]], values[v[0], v[1]]
            if fu < tau < fv:
                d = h * float(np.sqrt(((u - v) ** 2).sum()))
                if d > 0:
                    out.append((fv - fu) / d)
    return np.array(out)


def main():
    archive = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json")
    with open(archive) as f:
        a = json.load(f)
    gs = a["grid_size"]
    values = np.full((gs, gs), np.nan)
    filled = np.zeros((gs, gs), dtype=bool)
    for c in a["cells"]:
        i, j = c["grid_position"]
        values[i, j] = float(c["quality"])
        filled[i, j] = True
    tau = 0.5

    L_pop = L_pairs(values, filled, gs)
    G_pop = G_pairs(values, filled, gs, tau)
    print(f"L: n={len(L_pop)}, max={L_pop.max():.4f}", file=sys.stderr)
    print(f"G: n={len(G_pop)}, max={G_pop.max():.4f}", file=sys.stderr)

    # Load exact per-cell ell + per-pair K from the figure's stored output
    oblique_path = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/gp_smooth_result_oblique.json")
    with open(oblique_path) as f:
        ob = json.load(f)
    ell_obl = np.array(ob["per_cell_ell_ratios"])
    K_obl = np.array(ob["per_pair_K_ratios"])
    print(f"oblique K: n={len(K_obl)}, max={K_obl.max():.4f} (stored K_emp={ob['K_empirical']:.4f})", file=sys.stderr)
    print(f"oblique ell: n={len(ell_obl)}, max={ell_obl.max():.4f} (stored ell_emp={ob['ell_empirical']:.4f})", file=sys.stderr)

    B, seed = 1000, 0

    def ci(values):
        if len(values) == 0:
            return (None, None, None)
        return bootstrap_ci(np.asarray(values, dtype=float), B=B, seed=seed)

    # identity: K all 1.0, ell empty
    rows = [
        ("identity", L_pop, np.ones_like(L_pop), np.array([]), G_pop),
        ("GP-smooth oblique", L_pop, K_obl, ell_obl, G_pop),
    ]
    out_rows = []
    for name, Lv, Kv, ev, Gv in rows:
        out_rows.append({
            "defense": name,
            "L": ci(Lv), "K": ci(Kv), "ell": ci(ev), "G": ci(Gv),
            "L_max": float(Lv.max()) if len(Lv) else None,
            "K_max": float(Kv.max()) if len(Kv) else None,
            "ell_max": float(ev.max()) if len(ev) else None,
            "G_max": float(Gv.max()) if len(Gv) else None,
        })

    out_path = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/bootstrap_ci.json")
    out_path.write_text(
        json.dumps({"B": B, "seed": seed, "tau": tau, "archive": str(archive), "rows": out_rows},
                   indent=2,
                   default=lambda x: None if (isinstance(x, float) and np.isnan(x)) else x)
    )
    print(f"wrote {out_path}", file=sys.stderr)

    def f(v):
        if v is None or (isinstance(v, float) and np.isnan(v)):
            return "--"
        return f"{v:.3f}"

    lines = [
        "% Bootstrap percentile CIs (B=1000, seed=0, 95% level) on the",
        "% saturated gpt-3.5-turbo-0125 archive. L and G bootstrapped from",
        "% per-pair finite-difference populations over all filled pairs.",
        "% K and ell bootstrapped from the per-pair/per-cell populations",
        "% stored in gp_smooth_result_oblique.json (exactly the populations",
        "% that produced K_empirical and ell_empirical). Bootstrap output at",
        "% trilemma_validator/live_runs/gpt35_turbo_t05_saturated/bootstrap_ci.json.",
        "\\footnotesize",
        "\\setlength{\\tabcolsep}{3pt}",
        "\\begin{tabular}{l r c r c r c r c}",
        "\\toprule",
        "defense & $L_{\\mathrm{med}}$ & $L$ CI & $K_{\\mathrm{med}}$ & $K$ CI & $\\ell_{\\mathrm{med}}$ & $\\ell$ CI & $G_{\\mathrm{med}}$ & $G$ CI \\\\",
        "\\midrule",
    ]
    for r in out_rows:
        L, K, E, G = r["L"], r["K"], r["ell"], r["G"]
        lines.append(
            f"{r['defense']} & {f(L[0])} & $[{f(L[1])}, {f(L[2])}]$ & "
            f"{f(K[0])} & $[{f(K[1])}, {f(K[2])}]$ & "
            f"{f(E[0])} & $[{f(E[1])}, {f(E[2])}]$ & "
            f"{f(G[0])} & $[{f(G[1])}, {f(G[2])}]$ \\\\"
        )
    lines += ["\\bottomrule", "\\end{tabular}"]
    Path("/Users/mbhatt/stuff/tables/ci.tex").write_text("\n".join(lines) + "\n")
    print("wrote /Users/mbhatt/stuff/tables/ci.tex", file=sys.stderr)


if __name__ == "__main__":
    sys.exit(main() or 0)
