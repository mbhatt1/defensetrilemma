"""Theorem 9.3 pipeline Lipschitz-degradation demo (offline, no API).

Composes two continuous defenses on the saturated archive, measures the
empirical Lipschitz constant K of each stage and of the composition,
and compares to the theorem's predicted K_composed <= K_1 * K_2.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, "/Users/mbhatt/stuff/trilemma_validator/src")
from trilemma_validator.defenses import (
    SmoothNearestSafeDefense,
    KernelSmoothedDefense,
    SoftlyConstrainedProjectionDefense,
)
from trilemma_validator.loader import Heatmap


def grid_positions_from_archive(path: Path):
    with open(path) as f:
        a = json.load(f)
    gs = a["grid_size"]
    values = np.full((gs, gs), np.nan)
    for c in a["cells"]:
        i, j = c["grid_position"]
        values[i, j] = float(c["quality"])
    return Heatmap(values=values, grid_size=gs, cell_width=1.0 / gs)


def pairwise_K(defense_map_targets: np.ndarray, filled_mask: np.ndarray, grid_size: int) -> float:
    """Empirical K = max dist(D(u), D(v)) / dist(u, v) over filled pairs."""
    h = 1.0 / (grid_size - 1)
    filled = np.argwhere(filled_mask)
    if len(filled) < 2:
        return 0.0
    max_ratio = 0.0
    for i in range(len(filled)):
        for j in range(i + 1, len(filled)):
            u = filled[i]; v = filled[j]
            du = defense_map_targets[u[0], u[1]]
            dv = defense_map_targets[v[0], v[1]]
            dist_uv = h * np.sqrt(((u - v) ** 2).sum())
            dist_dudv = h * np.sqrt(((du - dv) ** 2).sum())
            if dist_uv > 0:
                max_ratio = max(max_ratio, dist_dudv / dist_uv)
    return float(max_ratio)


def compose(D1: np.ndarray, D2: np.ndarray) -> np.ndarray:
    """Composed targets: first D1, then D2 applied at D1's output."""
    gs = D1.shape[0]
    out = np.empty_like(D1)
    for i in range(gs):
        for j in range(gs):
            ti, tj = D1[i, j]
            out[i, j] = D2[ti, tj]
    return out


def main():
    archive = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json")
    out_dir = Path("/Users/mbhatt/stuff/trilemma_validator/live_runs/pipeline")
    out_dir.mkdir(parents=True, exist_ok=True)

    hm = grid_positions_from_archive(archive)
    tau = 0.5
    print(f"loaded {hm.filled_mask.sum()} filled cells", file=sys.stderr)

    D1 = SmoothNearestSafeDefense(radius=3.0).build(hm, tau)
    D2 = KernelSmoothedDefense(bandwidth=2.5).build(hm, tau)
    D3 = SoftlyConstrainedProjectionDefense(alpha=2.0).build(hm, tau)

    K1 = pairwise_K(D1.targets, hm.filled_mask, hm.grid_size)
    K2 = pairwise_K(D2.targets, hm.filled_mask, hm.grid_size)
    K3 = pairwise_K(D3.targets, hm.filled_mask, hm.grid_size)
    print(f"K(smooth_nearest_safe) = {K1:.3f}", file=sys.stderr)
    print(f"K(kernel_smoothed) = {K2:.3f}", file=sys.stderr)
    print(f"K(soft_projection) = {K3:.3f}", file=sys.stderr)

    results = []
    for name1, t1, k1 in [("smooth_nearest_safe", D1.targets, K1),
                          ("kernel_smoothed", D2.targets, K2)]:
        for name2, t2, k2 in [("smooth_nearest_safe", D1.targets, K1),
                              ("kernel_smoothed", D2.targets, K2),
                              ("soft_projection", D3.targets, K3)]:
            if name1 == name2: continue
            composed = compose(t1, t2)
            K12 = pairwise_K(composed, hm.filled_mask, hm.grid_size)
            bound = k1 * k2
            holds = K12 <= bound + 1e-9
            results.append({
                "stage1": name1, "K1": k1,
                "stage2": name2, "K2": k2,
                "K_composed_empirical": K12,
                "K_bound_K1_times_K2": bound,
                "bound_holds": holds,
                "slack": bound - K12,
            })
            print(f"  {name1} -> {name2}: K_composed={K12:.3f}, K1*K2={bound:.3f}, holds={holds}", file=sys.stderr)

    out = {
        "archive": str(archive),
        "tau": tau,
        "filled_cells": int(hm.filled_mask.sum()),
        "compositions": results,
    }
    (out_dir / "summary.json").write_text(json.dumps(out, indent=2))
    # tex table
    tex_path = Path("/Users/mbhatt/stuff/tables/pipeline.tex")
    tex_path.parent.mkdir(parents=True, exist_ok=True)
    with open(tex_path, "w") as f:
        f.write("% Pipeline Lipschitz-degradation empirical check (Theorem 9.3).\n")
        f.write("\\small\n")
        f.write("\\begin{tabular}{llrrrrc}\n")
        f.write("\\toprule\n")
        f.write("stage 1 & stage 2 & $K_1$ & $K_2$ & $K_1 K_2$ & $K_{\\mathrm{comp}}$ & $K_{\\mathrm{comp}} \\le K_1 K_2$? \\\\\n")
        f.write("\\midrule\n")
        for r in results:
            ok = "\\checkmark" if r["bound_holds"] else "$\\times$"
            f.write(f"\\texttt{{{r['stage1'].replace('_','-')}}} & "
                   f"\\texttt{{{r['stage2'].replace('_','-')}}} & "
                   f"{r['K1']:.2f} & {r['K2']:.2f} & {r['K_bound_K1_times_K2']:.2f} & "
                   f"{r['K_composed_empirical']:.2f} & {ok} \\\\\n")
        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")
    print(f"wrote {tex_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
