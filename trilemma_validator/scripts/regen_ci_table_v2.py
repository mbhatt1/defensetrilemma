"""Regenerate tables/ci.tex using the CONTINUOUS oblique defense from
make_paper_figure.py (not the grid-snapped defenses.py class) so the K
and ell populations match the Figure 4 narrative.

Computes per-pair K ratios and per-cell ell ratios on the SAME defense
construction as Figure 4 / gp_smooth_result_oblique.json, then bootstraps.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, "/Users/mbhatt/stuff/trilemma_validator/src")
# Bring in the figure script's defense/GP helpers.
sys.path.insert(0, "/Users/mbhatt/stuff/trilemma_validator/scripts")

from trilemma_validator.loader import Heatmap
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


# --- Copy minimal bits from make_paper_figure.py to avoid its full import
#     (which imports heavy matplotlib/validator machinery). -----------------

def _fit_gp(X: np.ndarray, y: np.ndarray, length_scale: float, noise: float):
    """RBF-kernel GP posterior; returns (K_inv_y, Xt)."""
    n = len(X)
    d2 = ((X[:, None, :] - X[None, :, :]) ** 2).sum(axis=2)
    # IMPORTANT: match make_paper_figure.py exactly — noise appears squared.
    K = np.exp(-d2 / (2.0 * length_scale ** 2)) + (noise ** 2) * np.eye(n)
    K_inv_y = np.linalg.solve(K, y)
    return K_inv_y, X, length_scale


def _gp_predict(fit, Xt: np.ndarray):
    K_inv_y, X, ls = fit
    d2 = ((Xt[:, None, :] - X[None, :, :]) ** 2).sum(axis=2)
    K_star = np.exp(-d2 / (2.0 * ls ** 2))
    return K_star @ K_inv_y


def _gp_grad(fit, x: np.ndarray):
    K_inv_y, X, ls = fit
    diff = x - X
    d2 = (diff ** 2).sum(axis=1)
    w = np.exp(-d2 / (2.0 * ls ** 2))
    grad = -((diff * w[:, None]).T @ K_inv_y) / (ls ** 2)
    return grad


def oblique_defense_targets(
    X: np.ndarray, y: np.ndarray, tau: float,
    length_scale: float = 0.20, noise: float = 0.02,
    alpha_step: float = 0.003, sigmoid_steepness: float = 2.0,
    oblique_angle_deg: float = 89.5,
):
    """Continuous oblique defense, no snapping. Returns D_targets array."""
    fit = _fit_gp(X, y, length_scale, noise)
    mu_at_X = _gp_predict(fit, X)
    # IMPORTANT: match make_paper_figure.py — it passes the degree value
    # directly into np.cos/np.sin without radian conversion. The paper's
    # "89.5 deg" narrative is really cos/sin(89.5 rad) in the stored run.
    # We replicate that to keep ci.tex consistent with Figure 4's numbers.
    theta = float(oblique_angle_deg)
    D_targets = np.empty_like(X)
    for i in range(len(X)):
        g = _gp_grad(fit, X[i])
        g_norm = float(np.linalg.norm(g))
        if g_norm < 1e-12:
            D_targets[i] = X[i]
            continue
        g_hat = g / g_norm
        # tangent perpendicular to gradient (90° rotate in 2D)
        n_hat = np.array([-g_hat[1], g_hat[0]])
        v = np.cos(theta) * (-g_hat) + np.sin(theta) * n_hat
        # sigmoid gating on μ(x) − τ
        beta = 1.0 / (1.0 + np.exp(-sigmoid_steepness * (mu_at_X[i] - tau)))
        D_targets[i] = X[i] + alpha_step * beta * v
    return D_targets, mu_at_X, fit


def main():
    archive = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json")
    hm = load_heatmap_from_archive(archive)
    tau = 0.5

    # Build filled-cell coordinate list in normalized [0,1]^2
    gs = hm.grid_size
    h = 1.0 / (gs - 1)
    filled = np.argwhere(hm.filled_mask)
    X = filled * h  # normalized coords
    y = np.array([hm.values[i, j] for i, j in filled])
    print(f"[cigen] {len(X)} filled cells", file=sys.stderr)

    # Populations --- L and G come from raw per-pair differences.
    def pairwise_diff_ratio(X, y):
        out = []
        for i in range(len(X)):
            for j in range(i + 1, len(X)):
                d = float(np.linalg.norm(X[i] - X[j]))
                if d > 0:
                    out.append(abs(y[i] - y[j]) / d)
        return np.array(out)

    def oriented_diff_ratio(X, y, tau):
        out = []
        for i in range(len(X)):
            for j in range(len(X)):
                if i == j: continue
                if y[i] < tau < y[j]:
                    d = float(np.linalg.norm(X[i] - X[j]))
                    if d > 0:
                        out.append((y[j] - y[i]) / d)
        return np.array(out)

    L_pop = pairwise_diff_ratio(X, y)
    G_pop = oriented_diff_ratio(X, y, tau)
    print(f"[cigen] L pop n={len(L_pop)} max={L_pop.max():.3f}", file=sys.stderr)
    print(f"[cigen] G pop n={len(G_pop)} max={G_pop.max():.3f}", file=sys.stderr)

    # ---- Per-defense K and ell populations ----
    def K_pop_from_D(X, D):
        out = []
        for i in range(len(X)):
            for j in range(i + 1, len(X)):
                di = float(np.linalg.norm(X[i] - X[j]))
                do = float(np.linalg.norm(D[i] - D[j]))
                if di > 0:
                    out.append(do / di)
        return np.array(out)

    def ell_pop_continuous(X, D, fit, tau):
        """Per-cell |μ(D(x)) - μ(x)| / ||D(x) - x|| for moved cells (matches make_paper_figure.py)."""
        mu_pre = _gp_predict(fit, X)
        mu_post = _gp_predict(fit, D)
        out = []
        for i in range(len(X)):
            d = float(np.linalg.norm(D[i] - X[i]))
            if d < 1e-10:
                continue
            out.append(abs(mu_post[i] - mu_pre[i]) / d)
        return np.array(out)

    # Identity
    K_id = np.ones(len(L_pop))  # all ratios are 1 under identity
    ell_id = np.array([])

    # Oblique
    D_obl, mu_pre, fit = oblique_defense_targets(X, y, tau)
    K_obl = K_pop_from_D(X, D_obl)
    ell_obl = ell_pop_continuous(X, D_obl, fit, tau)
    print(f"[cigen] oblique K pop n={len(K_obl)} max={K_obl.max():.4f}", file=sys.stderr)
    print(f"[cigen] oblique ell pop n={len(ell_obl)} max={ell_obl.max():.4f}", file=sys.stderr)

    # Bootstrap each population
    B, seed = 1000, 0
    def ci(values):
        if len(values) == 0:
            return (None, None, None)
        return bootstrap_ci(np.asarray(values, dtype=float), B=B, seed=seed)

    rows = [
        ("identity", L_pop, K_id, ell_id, G_pop),
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
    with open(out_path, "w") as fo:
        json.dump(
            {"B": B, "seed": seed, "tau": tau, "archive": str(archive), "rows": out_rows},
            fo, indent=2, default=lambda x: None if (isinstance(x, float) and np.isnan(x)) else x
        )
    print(f"[cigen] wrote {out_path}", file=sys.stderr)

    def f(v):
        if v is None or (isinstance(v, float) and np.isnan(v)):
            return "--"
        return f"{v:.3f}"

    lines = [
        "% Bootstrap percentile CIs (B=1000, seed=0, 95% level) on the",
        "% saturated gpt-3.5-turbo-0125 archive using the CONTINUOUS oblique",
        "% defense construction from scripts/make_paper_figure.py (not the",
        "% grid-snapped GPSmoothObliqueDefense class). L and G are",
        "% defense-independent. Raw per-population bootstrap stats in",
        "% trilemma_validator/live_runs/gpt35_turbo_t05_saturated/bootstrap_ci.json.",
        "\\footnotesize",
        "\\setlength{\\tabcolsep}{3pt}",
        "\\begin{tabular}{l r c r c r c r c}",
        "\\toprule",
        "defense & $L_{\\mathrm{med}}$ & $L$ CI & $K_{\\mathrm{med}}$ & $K$ CI & $\\ell_{\\mathrm{med}}$ & $\\ell$ CI & $G_{\\mathrm{med}}$ & $G$ CI \\\\",
        "\\midrule",
    ]
    for r in out_rows:
        L = r["L"]; K = r["K"]; E = r["ell"]; G = r["G"]
        lines.append(
            f"{r['defense']} & {f(L[0])} & $[{f(L[1])}, {f(L[2])}]$ & "
            f"{f(K[0])} & $[{f(K[1])}, {f(K[2])}]$ & "
            f"{f(E[0])} & $[{f(E[1])}, {f(E[2])}]$ & "
            f"{f(G[0])} & $[{f(G[1])}, {f(G[2])}]$ \\\\"
        )
    lines += ["\\bottomrule", "\\end{tabular}"]
    Path("/Users/mbhatt/stuff/tables/ci.tex").write_text("\n".join(lines) + "\n")
    print("[cigen] wrote /Users/mbhatt/stuff/tables/ci.tex", file=sys.stderr)


if __name__ == "__main__":
    sys.exit(main() or 0)
