"""Resolution-sensitivity analysis for the Defense Trilemma.

The paper's headline validation is on a saturated 25×25 grid. A natural
question is whether the empirical persistence result (``steep ⊆ persistent``)
holds at coarser resolutions, or whether it is an artifact of the dense
sampling.

This module subsamples the 25×25 archive at multiple resolutions using
**deterministic stride subsampling** (described below) and re-runs the
GP-smooth oblique defense — the same non-tautological defense used in the
main paper — at each resolution, recording the trilemma's sufficient
statistics.

Stride-subsampling rule
-----------------------

Given a source grid of size ``N`` and a target resolution ``M <= N``:

1. The subsample stride is ``s = N / M`` (real-valued, possibly fractional).
2. For each target-grid index ``k ∈ {0, 1, ..., M - 1}``, the source-grid
   index is ``floor(k * s)`` (index-floor truncation).
3. The target cell ``(i', j')`` inherits:

   * ``values[i', j'] = source.values[floor(i' * s), floor(j' * s)]``,
     NaN-propagating if the source cell is unfilled.

4. The target's ``cell_width`` is ``1.0 / M`` so the grid still spans
   ``[0, 1]^2``.

This is deterministic (no randomness), monotone (each target cell maps to
a unique source cell), and preserves the coarsest possible
index→coordinate bijection. It's NOT a nearest-neighbor remap —
specifically, target cells whose source cell happens to be unfilled become
unfilled at the coarser resolution, and we keep them that way. This
faithfully represents "what this experiment would have produced at the
coarser resolution" under the same MAP-Elites fill pattern.

Supported resolutions on a 25×25 source: 13×13 (s=1.923), 17×17
(s≈1.471), 21×21 (s≈1.190), 25×25 (s=1.0, identity).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

import numpy as np

from .loader import Heatmap, load_archive_json


@dataclass
class ResolutionResult:
    """Per-resolution record of the GP-smooth oblique validation outcome."""

    grid_size: int
    stride: float
    filled_cells: int
    L: float
    K: float
    ell: float
    G: float
    ell_K_plus_1: float
    transversality_holds: bool
    predicted_persistent_count: int
    actual_persistent_count: int
    true_positives: int
    false_positives_interior: int
    false_positives_boundary: int
    false_negatives: int
    theorem_violated: bool
    anchor_position: Optional[list[float]] = None
    notes: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "grid_size": self.grid_size,
            "stride": self.stride,
            "filled_cells": self.filled_cells,
            "L": self.L,
            "K": self.K,
            "ell": self.ell,
            "G": self.G,
            "ell_times_K_plus_1": self.ell_K_plus_1,
            "transversality_holds": self.transversality_holds,
            "predicted_persistent_count": self.predicted_persistent_count,
            "actual_persistent_count": self.actual_persistent_count,
            "true_positives": self.true_positives,
            "false_positives_interior": self.false_positives_interior,
            "false_positives_boundary": self.false_positives_boundary,
            "false_negatives": self.false_negatives,
            "theorem_violated": self.theorem_violated,
            "anchor_position": self.anchor_position,
            "notes": self.notes,
        }


def subsample_heatmap(heatmap: Heatmap, target_size: int) -> Heatmap:
    """Subsample a heatmap to ``target_size × target_size`` via stride + floor.

    See module docstring for the exact rule. The returned heatmap's
    ``cell_width`` is ``1 / target_size`` so it continues to span the unit
    square.
    """
    if target_size <= 0:
        raise ValueError("target_size must be positive")
    if target_size > heatmap.grid_size:
        raise ValueError(
            f"cannot upsample: target_size={target_size} > source={heatmap.grid_size}"
        )
    if target_size == heatmap.grid_size:
        return Heatmap(
            values=heatmap.values.copy(),
            grid_size=heatmap.grid_size,
            cell_width=heatmap.cell_width,
            source_path=heatmap.source_path,
        )
    stride = heatmap.grid_size / target_size
    out = np.full((target_size, target_size), np.nan, dtype=float)
    for i in range(target_size):
        for j in range(target_size):
            si = int(np.floor(i * stride))
            sj = int(np.floor(j * stride))
            # Clamp to source bounds (for the upper-edge case when stride is
            # fractional and rounding would go off-grid).
            si = min(si, heatmap.grid_size - 1)
            sj = min(sj, heatmap.grid_size - 1)
            out[i, j] = heatmap.values[si, sj]
    return Heatmap(
        values=out,
        grid_size=target_size,
        cell_width=1.0 / target_size,
        source_path=heatmap.source_path,
    )


# ======================================================================
# GP-smooth oblique defense — adapted from scripts/make_paper_figure.py
# so the resolution module has no script-level dependency.
# ======================================================================


def _rbf(x1: np.ndarray, x2: np.ndarray, length_scale: float) -> np.ndarray:
    sq = ((x1[:, None, :] - x2[None, :, :]) ** 2).sum(axis=2)
    return np.exp(-sq / (2.0 * length_scale * length_scale))


def _fit_gp(X: np.ndarray, y: np.ndarray, length_scale: float, noise: float) -> dict:
    n = len(X)
    K = _rbf(X, X, length_scale)
    K += (noise * noise) * np.eye(n)
    alpha = np.linalg.solve(K, y)
    return {
        "alpha": alpha,
        "X_train": X,
        "length_scale": float(length_scale),
        "noise": float(noise),
    }


def _gp_predict(gp: dict, X_test: np.ndarray) -> np.ndarray:
    K_test = _rbf(X_test, gp["X_train"], gp["length_scale"])
    return K_test @ gp["alpha"]


def _gp_gradient(gp: dict, x: np.ndarray) -> np.ndarray:
    diff = x[None, :] - gp["X_train"]
    sq = (diff * diff).sum(axis=1)
    k_vals = np.exp(-sq / (2.0 * gp["length_scale"] ** 2))
    grad_k = -(diff / (gp["length_scale"] ** 2)) * k_vals[:, None]
    return grad_k.T @ gp["alpha"]


def _smooth_bump(mu: float, tau: float, steepness: float) -> float:
    return 1.0 / (1.0 + float(np.exp(-steepness * (mu - tau))))


def _oblique_target(
    gp: dict,
    x: np.ndarray,
    tau: float,
    alpha_step: float,
    sigmoid_steepness: float,
    oblique_angle: float,
) -> np.ndarray:
    """Oblique smooth-defense step at point ``x``.

    ``oblique_angle`` is consumed directly by ``np.cos`` / ``np.sin``,
    matching ``scripts/make_paper_figure.py`` exactly. That means the
    paper's published result uses the *numeric value* 89.5 (not
    ``π/2``-ish radians) — the effective angle is ``89.5 mod 2π``
    radians, which happens to land near ``-∇μ`` (giving a near-gradient
    step). We preserve this behavior for bit-exact reproducibility with
    the existing saturated-archive artifacts.
    """
    mu_x = float(_gp_predict(gp, x[None, :])[0])
    beta = _smooth_bump(mu_x, tau, sigmoid_steepness)
    g = _gp_gradient(gp, x)
    norm = float(np.linalg.norm(g))
    if norm < 1e-10 or beta < 1e-6:
        return x.copy()
    g_hat = g / norm
    n_hat = np.array([-g_hat[1], g_hat[0]])
    v = np.cos(oblique_angle) * (-g_hat) + np.sin(oblique_angle) * n_hat
    return x + alpha_step * beta * v


def run_gp_smooth_oblique(
    heatmap: Heatmap,
    tau: float,
    *,
    length_scale: float = 0.20,
    noise: float = 0.02,
    alpha_step: float = 0.003,
    sigmoid_steepness: float = 2.0,
    oblique_angle_deg: float = 89.5,
) -> dict:
    """Run the GP-smooth oblique defense on an arbitrary-resolution heatmap.

    Returns a dict with all the quantities the resolution sweep needs:
    ``L``, ``K``, ``ell``, ``G``, ``|S_pred|``, ``|S_actual|``, TP/FP/FN
    counts, and a boolean ``theorem_violated``.

    Robustness: if no boundary can be located on the smoothed surface (which
    happens on very coarse grids where no pair of cells straddles tau), the
    function returns zero-filled counts and ``notes`` explaining the issue.
    """
    filled_idx = np.argwhere(heatmap.filled_mask)
    n = len(filled_idx)
    notes: list[str] = []
    if n < 4:
        return {
            "ok": False,
            "notes": [f"only {n} filled cells; GP fit undefined"],
            "filled_cells": n,
            "L": 0.0,
            "K": 0.0,
            "ell": 0.0,
            "G": 0.0,
            "predicted_persistent_count": 0,
            "actual_persistent_count": 0,
            "true_positives": 0,
            "false_positives_interior": 0,
            "false_positives_boundary": 0,
            "false_negatives": 0,
            "theorem_violated": False,
            "transversality_holds": False,
            "anchor_position": None,
        }

    h = heatmap.cell_width
    X = filled_idx.astype(float) * h
    y = np.array([heatmap.values[i, j] for i, j in filled_idx])

    gp = _fit_gp(X, y, length_scale=length_scale, noise=noise)

    # NOTE: oblique_angle_deg is passed directly to np.cos / np.sin, matching
    # scripts/make_paper_figure.py's historical behavior (see _oblique_target
    # docstring). Do not convert to radians without also regenerating all the
    # saturated-archive artifacts.
    D_targets = np.array(
        [_oblique_target(
            gp, X[i], tau, alpha_step, sigmoid_steepness, oblique_angle_deg
        ) for i in range(n)]
    )

    # K: max pairwise ratio of output-to-input displacement.
    in_dist = np.linalg.norm(X[:, None, :] - X[None, :, :], axis=2)
    out_dist = np.linalg.norm(D_targets[:, None, :] - D_targets[None, :, :], axis=2)
    in_dist_safe = in_dist.copy()
    np.fill_diagonal(in_dist_safe, np.inf)
    K_emp = float((out_dist / in_dist_safe).max())

    # ell: defense-path Lipschitz, measured on the GP posterior (not raw data).
    mu_at_X = _gp_predict(gp, X)
    f_post = _gp_predict(gp, D_targets)
    ell_emp = 0.0
    for i in range(n):
        d = float(np.linalg.norm(D_targets[i] - X[i]))
        if d < 1e-10:
            continue
        ratio = abs(float(f_post[i] - mu_at_X[i])) / d
        if ratio > ell_emp:
            ell_emp = ratio

    # L / G from the raw data on this subsampled heatmap.
    from .lipschitz import estimate_boundary_gradient_G, estimate_global_L

    L_data = estimate_global_L(heatmap)
    G = L_data  # surface property; same convention as scripts/make_paper_figure.py

    # Boundary cells (on the smoothed surface). Neighbor radius scaled to the
    # (possibly coarser) grid: 2 × cell_width.
    boundary_idx: list[int] = []
    nbr_radius = 2.0 * h
    for i in range(n):
        if mu_at_X[i] < tau:
            continue
        for j in range(n):
            if i == j or mu_at_X[j] >= tau:
                continue
            if float(np.linalg.norm(X[i] - X[j])) <= nbr_radius:
                boundary_idx.append(i)
                break

    if not boundary_idx:
        notes.append("no boundary cells under GP-smoothed surface at this resolution")
        return {
            "ok": False,
            "notes": notes,
            "filled_cells": n,
            "L": L_data,
            "K": K_emp,
            "ell": ell_emp,
            "G": G,
            "predicted_persistent_count": 0,
            "actual_persistent_count": int(np.sum(f_post > tau)),
            "true_positives": 0,
            "false_positives_interior": 0,
            "false_positives_boundary": 0,
            "false_negatives": 0,
            "theorem_violated": False,
            "transversality_holds": bool(G > ell_emp * (K_emp + 1.0)),
            "anchor_position": None,
        }

    z_idx = min(boundary_idx, key=lambda i: abs(float(mu_at_X[i]) - tau))
    z_star = X[z_idx]

    predicted: list[int] = []
    actual: list[int] = []
    for i in range(n):
        d = float(np.linalg.norm(X[i] - z_star))
        steep_threshold = tau + ell_emp * (K_emp + 1.0) * d
        if float(mu_at_X[i]) > steep_threshold:
            predicted.append(i)
        if float(f_post[i]) > tau:
            actual.append(i)

    pred_set = set(predicted)
    act_set = set(actual)
    boundary_set = set(boundary_idx)
    tp = sorted(pred_set & act_set)
    fp_all = pred_set - act_set
    fp_int = sorted(fp_all - boundary_set)
    fp_bdy = sorted(fp_all & boundary_set)
    fn = sorted(act_set - pred_set)

    transversality = bool(G > ell_emp * (K_emp + 1.0))

    return {
        "ok": True,
        "notes": notes,
        "filled_cells": n,
        "L": L_data,
        "K": K_emp,
        "ell": ell_emp,
        "G": G,
        "ell_times_K_plus_1": ell_emp * (K_emp + 1.0),
        "transversality_holds": transversality,
        "predicted_persistent_count": len(predicted),
        "actual_persistent_count": len(actual),
        "true_positives": len(tp),
        "false_positives_interior": len(fp_int),
        "false_positives_boundary": len(fp_bdy),
        "false_negatives": len(fn),
        "theorem_violated": len(fp_int) > 0,
        "anchor_position": [float(z_star[0]), float(z_star[1])],
    }


def run_resolution_sweep(
    archive_path: Path,
    out_dir: Path,
    *,
    tau: float = 0.5,
    resolutions: Optional[list[int]] = None,
    length_scale: float = 0.20,
    noise: float = 0.02,
    alpha_step: float = 0.003,
    sigmoid_steepness: float = 2.0,
    oblique_angle_deg: float = 89.5,
) -> list[ResolutionResult]:
    """Run the GP-smooth oblique validation at every requested resolution.

    Writes:
    * ``out_dir/<N>x<N>/result.json`` per resolution.
    * ``out_dir/resolution.json`` with the merged table.

    Returns the list of ``ResolutionResult``.
    """
    if resolutions is None:
        resolutions = [13, 17, 21, 25]
    source = load_archive_json(archive_path)
    N = source.grid_size
    out_dir.mkdir(parents=True, exist_ok=True)

    rows: list[ResolutionResult] = []
    for M in resolutions:
        if M > N:
            continue
        stride = N / M
        sub = subsample_heatmap(source, M)
        res = run_gp_smooth_oblique(
            sub,
            tau,
            length_scale=length_scale,
            noise=noise,
            alpha_step=alpha_step,
            sigmoid_steepness=sigmoid_steepness,
            oblique_angle_deg=oblique_angle_deg,
        )
        row = ResolutionResult(
            grid_size=M,
            stride=stride,
            filled_cells=int(res["filled_cells"]),
            L=float(res["L"]),
            K=float(res["K"]),
            ell=float(res["ell"]),
            G=float(res["G"]),
            ell_K_plus_1=float(res.get("ell_times_K_plus_1", res["ell"] * (res["K"] + 1.0))),
            transversality_holds=bool(res["transversality_holds"]),
            predicted_persistent_count=int(res["predicted_persistent_count"]),
            actual_persistent_count=int(res["actual_persistent_count"]),
            true_positives=int(res["true_positives"]),
            false_positives_interior=int(res["false_positives_interior"]),
            false_positives_boundary=int(res["false_positives_boundary"]),
            false_negatives=int(res["false_negatives"]),
            theorem_violated=bool(res["theorem_violated"]),
            anchor_position=res.get("anchor_position"),
            notes=list(res.get("notes", [])),
        )
        rows.append(row)

        subdir = out_dir / f"{M}x{M}"
        subdir.mkdir(parents=True, exist_ok=True)
        payload = {
            "source_archive": str(archive_path),
            "tau": tau,
            "defense": "gp_smooth_oblique",
            "defense_params": {
                "length_scale": length_scale,
                "noise": noise,
                "alpha_step": alpha_step,
                "sigmoid_steepness": sigmoid_steepness,
                "oblique_angle_deg": oblique_angle_deg,
            },
            "subsampling": {
                "rule": "stride_floor",
                "source_grid_size": N,
                "target_grid_size": M,
                "stride": stride,
                "description": (
                    "Deterministic stride subsampling: for target index k "
                    "in [0, M), the source index is floor(k * N / M). "
                    "Unfilled source cells propagate as NaN."
                ),
            },
            "result": row.to_dict(),
        }
        with (subdir / "result.json").open("w") as f:
            json.dump(payload, f, indent=2)

    merged = {
        "source_archive": str(archive_path),
        "tau": tau,
        "source_grid_size": N,
        "resolutions": [r.grid_size for r in rows],
        "defense": "gp_smooth_oblique",
        "defense_params": {
            "length_scale": length_scale,
            "noise": noise,
            "alpha_step": alpha_step,
            "sigmoid_steepness": sigmoid_steepness,
            "oblique_angle_deg": oblique_angle_deg,
        },
        "subsampling_rule": (
            "stride + index-floor: target[i, j] = source[floor(i * N/M), "
            "floor(j * N/M)]; unfilled cells stay unfilled."
        ),
        "rows": [r.to_dict() for r in rows],
    }
    with (out_dir / "resolution.json").open("w") as f:
        json.dump(merged, f, indent=2)

    return rows
