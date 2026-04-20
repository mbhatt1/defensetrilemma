"""Recompute L, K, ell, G using a higher-dimensional distance metric.

Default: sentence-transformers/all-mpnet-base-v2 (768-d), the same
embedder rethinking-evals uses for behavioral descriptors.

Rationale: Hoque-style concern (technical gap #4) is that the
2D (indirection, authority) MAP-Elites projection might make the
alignment-deviation surface LOOK smoother/rougher than it is in the
higher-dim semantic embedding where prompts actually live. This
script recomputes the same estimators with the same formulas, on
the same 82 filled cells, but with pairwise Euclidean distances in
the 768-d embedding instead of the 2D grid.

If the ratios between 2D and 768-d are approximately stable, the
paper's 2D estimates are not artifacts of the projection. If they
explode, the paper should state the 768-d values as the honest
bound and the 2D as a projection-dependent summary.

Emits:
  - tables/higher_dim_lipschitz.tex — 2D vs 768-d side by side
  - outputs/higher_dim_lipschitz.md — short writeup
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Tuple

import numpy as np


def normalize_grid_coords(cells, grid_size: int) -> np.ndarray:
    """Return (n, 2) normalized grid coordinates in [0,1]^2."""
    coords = np.array([c["grid_position"] for c in cells], dtype=float)
    return coords / float(grid_size - 1)  # match validator's metric


def encode_prompts(prompts: list, model_name: str) -> np.ndarray:
    """Encode via sentence-transformers. Runs on whatever device is available."""
    from sentence_transformers import SentenceTransformer

    print(f"[hdim] loading {model_name}", file=sys.stderr)
    enc = SentenceTransformer(model_name)
    print(f"[hdim] encoding {len(prompts)} prompts", file=sys.stderr)
    return enc.encode(prompts, show_progress_bar=False, normalize_embeddings=False)


def pairwise_l2(X: np.ndarray) -> np.ndarray:
    """Dense pairwise L2 distance matrix (n, n)."""
    diff = X[:, None, :] - X[None, :, :]
    return np.sqrt((diff ** 2).sum(-1))


def lipschitz_max(f: np.ndarray, D: np.ndarray) -> float:
    """Max over ordered pairs i != j of |f_i - f_j| / D_ij."""
    n = len(f)
    df = np.abs(f[:, None] - f[None, :])
    # Avoid division by zero on diagonal
    D_safe = np.where(D > 0, D, np.inf)
    return float((df / D_safe).max())


def directional_G(f: np.ndarray, D: np.ndarray, tau: float) -> float:
    """Max over safe i, unsafe j of (f_j - f_i) / D_ij."""
    safe = f < tau
    unsafe = f > tau
    if not safe.any() or not unsafe.any():
        return 0.0
    D_sub = D[np.ix_(safe, unsafe)]
    f_safe = f[safe][:, None]
    f_unsafe = f[unsafe][None, :]
    diff = f_unsafe - f_safe
    D_safe = np.where(D_sub > 0, D_sub, np.inf)
    return float((diff / D_safe).max())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", required=True, type=Path)
    ap.add_argument("--tau", type=float, default=0.5)
    ap.add_argument(
        "--model", default="sentence-transformers/all-mpnet-base-v2"
    )
    ap.add_argument("--tex-out", required=True, type=Path)
    ap.add_argument("--md-out", required=True, type=Path)
    ap.add_argument("--json-out", required=True, type=Path)
    args = ap.parse_args()

    arch = json.load(open(args.source))
    cells = arch["cells"]
    grid_size = int(arch.get("grid_size", 25))
    f = np.array([float(c["quality"]) for c in cells])
    prompts = [c["prompt"] for c in cells]
    print(f"[hdim] {len(cells)} cells, grid_size={grid_size}", file=sys.stderr)

    # 2D baseline (grid metric, normalized)
    coords2d = normalize_grid_coords(cells, grid_size)
    D2 = pairwise_l2(coords2d)
    L2D = lipschitz_max(f, D2)
    G2D = directional_G(f, D2, args.tau)

    # 768-d embedding
    emb = encode_prompts(prompts, args.model)
    Dhd = pairwise_l2(emb)
    # Rescale to be comparable: normalize so max pairwise distance = 1.
    max_d = Dhd[Dhd > 0].max()
    Dhd_norm = Dhd / max_d
    Lhd = lipschitz_max(f, Dhd_norm)
    Ghd = directional_G(f, Dhd_norm, args.tau)

    # Also report raw (un-normalized) for reference
    Lhd_raw = lipschitz_max(f, Dhd)
    Ghd_raw = directional_G(f, Dhd, args.tau)

    result = {
        "n_cells": int(len(cells)),
        "tau": args.tau,
        "model": args.model,
        "embedding_dim": int(emb.shape[1]),
        "2d_grid_normalized": {
            "L_hat": L2D,
            "G_hat": G2D,
            "max_pairwise_distance": float(D2[D2 > 0].max()),
        },
        "hdim_normalized": {
            "L_hat": Lhd,
            "G_hat": Ghd,
            "max_pairwise_distance": 1.0,
        },
        "hdim_raw": {
            "L_hat": Lhd_raw,
            "G_hat": Ghd_raw,
            "max_pairwise_distance": float(max_d),
        },
        "ratios": {
            "L_ratio_hdim_over_2d_normalized": Lhd / L2D if L2D > 0 else float("inf"),
            "G_ratio_hdim_over_2d_normalized": Ghd / G2D if G2D > 0 else float("inf"),
        },
    }

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2))

    # LaTeX table
    tex_lines = [
        "% Auto-generated by scripts/higher_dim_lipschitz.py",
        "\\begin{tabular}{lrr}",
        "\\toprule",
        "Metric & $\\hat L$ & $\\hat G$ \\\\",
        "\\midrule",
        f"2D grid coordinates (normalized to $[0,1]^2$) & {L2D:.3f} & {G2D:.3f} \\\\",
        f"{emb.shape[1]}-d MPNet embedding (pairwise-max normalized) & {Lhd:.3f} & {Ghd:.3f} \\\\",
        "\\bottomrule",
        "\\end{tabular}",
        f"% ratio L(hdim)/L(2d) = {result['ratios']['L_ratio_hdim_over_2d_normalized']:.3f}, "
        f"G ratio = {result['ratios']['G_ratio_hdim_over_2d_normalized']:.3f}",
    ]
    args.tex_out.parent.mkdir(parents=True, exist_ok=True)
    args.tex_out.write_text("\n".join(tex_lines) + "\n")

    md = [
        f"# Higher-dimensional Lipschitz check",
        "",
        f"Saturated gpt-3.5-turbo-0125 archive, {len(cells)} filled cells, tau={args.tau}.",
        f"Comparison of empirical $\\hat L$ and $\\hat G$ computed in two metrics:",
        "",
        f"- **2D grid**: normalized grid coordinates in $[0,1]^2$ (the paper's main estimator)",
        f"- **{emb.shape[1]}-d embedding**: `{args.model}` sentence embeddings, "
        f"pairwise distances normalized so max = 1 (comparable to the 2D case)",
        "",
        "| Metric | L_hat | G_hat |",
        "|---|---:|---:|",
        f"| 2D grid (normalized) | {L2D:.3f} | {G2D:.3f} |",
        f"| {emb.shape[1]}-d MPNet (normalized) | {Lhd:.3f} | {Ghd:.3f} |",
        f"| ratio hdim/2d | {result['ratios']['L_ratio_hdim_over_2d_normalized']:.3f} | "
        f"{result['ratios']['G_ratio_hdim_over_2d_normalized']:.3f} |",
        "",
        "## Interpretation",
        "",
        "If the ratio is close to 1, the 2D MAP-Elites projection is not an "
        "artifact of the projection — the Lipschitz estimates are comparable "
        "in the higher-dimensional semantic embedding. If the ratio is small "
        "(< 0.5) the 2D projection over-estimates the local slope (Lipschitz "
        "constants are artifacts of the tight 2D grid). If the ratio is large "
        "(> 2), the 2D projection under-estimates the slope, and the theorem "
        "still applies with the larger constant.",
    ]
    args.md_out.parent.mkdir(parents=True, exist_ok=True)
    args.md_out.write_text("\n".join(md) + "\n")

    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
