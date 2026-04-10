#!/usr/bin/env python3
"""Generate the paper figure and the GP-smooth defense validation.

This script does two things from the same saturated archive:

1. ``make_figure()`` — produces the per-cell ε-robust margin scatter PDF
   used as Figure 4 in the paper.
2. ``gp_smooth_validation()`` — fits a 2D Gaussian Process to the 82
   filled cells (RBF kernel, implemented in pure numpy — no sklearn
   dependency), constructs a *continuous* gradient-step defense over the
   GP posterior, and checks Theorem 6.2's predicted-vs-actual containment
   non-tautologically. The identity-defense check on the same archive is
   tautological under ``ℓ = 0``; this is the non-trivial alternative.

Run with no arguments to write both
``figures/eps_robust_saturated.pdf`` and
``trilemma_validator/live_runs/gpt35_turbo_t05_saturated/gp_smooth_result.json``.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

from trilemma_validator.defenses import IdentityDefense
from trilemma_validator.lipschitz import estimate_global_L
from trilemma_validator.loader import load_archive_json
from trilemma_validator.theorems import _select_anchor, check_boundary_fixation


# ============================================================
# Pure-numpy 2D Gaussian Process with RBF kernel
# ============================================================
#
# We don't depend on sklearn. The GP we need is small (≤ 100 training
# points), uses an isotropic RBF kernel, and only needs posterior mean +
# its analytic gradient (no marginal likelihood, no hyperparameter
# optimization). The whole thing is ~30 lines of numpy.


def _rbf(x1: np.ndarray, x2: np.ndarray, length_scale: float) -> np.ndarray:
    """RBF (squared-exponential) kernel: k(a, b) = exp(-||a-b||^2 / (2 ℓ²))."""
    sq = ((x1[:, None, :] - x2[None, :, :]) ** 2).sum(axis=2)
    return np.exp(-sq / (2.0 * length_scale * length_scale))


def fit_gp_2d(
    X: np.ndarray, y: np.ndarray, length_scale: float, noise: float
) -> dict:
    """Fit a 2D GP with RBF kernel and Gaussian noise.

    Returns a dict containing the precomputed weights ``alpha``, training
    inputs, and hyperparameters; sufficient to predict the posterior mean
    and its gradient at any test point.
    """
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


def gp_predict(gp: dict, X_test: np.ndarray) -> np.ndarray:
    """Posterior mean of the GP at test points ``X_test`` (shape (m, 2))."""
    K_test = _rbf(X_test, gp["X_train"], gp["length_scale"])
    return K_test @ gp["alpha"]


def gp_gradient(gp: dict, x: np.ndarray) -> np.ndarray:
    """Analytic gradient of the posterior mean at a single 2D point ``x``.

    For an RBF kernel, ``∂_x k(x, x_i) = -(x - x_i)/ℓ² · k(x, x_i)``,
    so ``∇_x μ(x) = Σ_i α_i · ∂_x k(x, x_i)``.
    """
    diff = x[None, :] - gp["X_train"]  # (n, 2)
    sq = (diff * diff).sum(axis=1)
    k_vals = np.exp(-sq / (2.0 * gp["length_scale"] ** 2))
    grad_k = -(diff / (gp["length_scale"] ** 2)) * k_vals[:, None]  # (n, 2)
    return grad_k.T @ gp["alpha"]  # (2,)


def gp_max_grad_norm(gp: dict, n_samples: int = 600, seed: int = 0) -> float:
    """Estimate ``L_GP = sup_x ||∇μ(x)||`` by random sampling on [0, 1]²."""
    rng = np.random.default_rng(seed)
    samples = rng.uniform(0.0, 1.0, size=(n_samples, 2))
    best = 0.0
    for i in range(n_samples):
        gn = float(np.linalg.norm(gp_gradient(gp, samples[i])))
        if gn > best:
            best = gn
    return best


# ============================================================
# Continuous gradient-step defense built on the GP posterior
# ============================================================


def smooth_bump(mu: float, tau: float, steepness: float) -> float:
    """Sigmoid bump that ramps from ~0 (when μ ≪ τ) to ~1 (when μ ≫ τ)."""
    return 1.0 / (1.0 + float(np.exp(-steepness * (mu - tau))))


def smooth_defense_target(
    gp: dict,
    x: np.ndarray,
    tau: float,
    alpha_step: float,
    sigmoid_steepness: float,
) -> np.ndarray:
    """Apply the gradient-step smooth defense at point ``x``.

    ``D(x) = x - α · β(μ(x)) · ∇μ(x) / ||∇μ(x)||``

    where ``β`` is a smooth ramp that's ~0 in the safe region and ~1 in the
    unsafe region. By construction the displacement is along the negative
    gradient direction, so the empirical defense-path Lipschitz constant
    ``ℓ`` ends up equal to the global Lipschitz constant ``L`` of ``μ``
    (the directional rate along ``∇μ`` is exactly ``||∇μ||``). This
    defense is **continuous and Lipschitz**, so Theorem 6.2's hypotheses
    are satisfied, but it does not put the trilemma's anisotropy regime
    (``ℓ < L``) to a non-trivial test.
    """
    mu_x = float(gp_predict(gp, x[None, :])[0])
    beta = smooth_bump(mu_x, tau, sigmoid_steepness)
    g = gp_gradient(gp, x)
    norm = float(np.linalg.norm(g))
    if norm < 1e-10 or beta < 1e-6:
        return x.copy()
    return x - alpha_step * beta * (g / norm)


def smooth_defense_target_centroid(
    gp: dict,
    x: np.ndarray,
    centroid: np.ndarray,
    tau: float,
    alpha_step: float,
    sigmoid_steepness: float,
) -> np.ndarray:
    """Apply the centroid-contraction smooth defense at point ``x``.

    ``D(x) = x + α · β(μ(x)) · (c - x)``

    where ``c`` is the centroid of the safe region and ``β`` is the same
    sigmoid bump as ``smooth_defense_target``. This defense is also
    continuous and approximately utility-preserving, but its displacement
    direction is ``c - x`` — typically NOT aligned with the gradient
    ``∇μ(x)``. The directional rate of ``μ`` along ``c - x`` can be much
    smaller than ``||∇μ(x)||``, so the empirical ``ℓ`` here can satisfy
    ``ℓ < L`` and the persistence theorem's anisotropic regime becomes
    non-trivially testable.
    """
    mu_x = float(gp_predict(gp, x[None, :])[0])
    beta = smooth_bump(mu_x, tau, sigmoid_steepness)
    if beta < 1e-6:
        return x.copy()
    direction = centroid - x
    norm = float(np.linalg.norm(direction))
    if norm < 1e-10:
        return x.copy()
    return x + alpha_step * beta * direction


def make_figure(archive_path: Path, out_path: Path, tau: float = 0.5) -> None:
    """Side-by-side 'theory predicts' vs 'reality observed' heatmap.

    Each panel is the saturated 25x25 alignment-deviation grid. On the
    left, every filled cell is colored red if the theorem *predicts*
    it remains unsafe after defense, green otherwise. On the right,
    every filled cell is colored red if it *actually* remains unsafe
    after applying the canonical continuous defense (identity), green
    otherwise. If Theorem 6.2 holds, the two panels are identical.
    Any cell red on the left and green on the right would be a real
    counterexample.
    """
    heatmap = load_archive_json(archive_path)
    defense = IdentityDefense().build(heatmap, tau)
    bd = check_boundary_fixation(defense, heatmap, tau)
    if not bd.boundary_exists:
        raise RuntimeError(
            f"No boundary cells found at tau={tau}; cannot anchor the bound."
        )
    L = estimate_global_L(heatmap)
    vals = heatmap.values
    filled = heatmap.filled_mask
    gs = heatmap.grid_size
    boundary_set = set(bd.boundary_cells)

    # ----- Build the two classification grids -----
    # Each grid value: 0 = empty cell (not sampled), 1 = safe (f < tau),
    # 2 = unsafe (f > tau, in BOTH predicted and actual persistent set
    # under the canonical identity defense). Boundary cells get a separate
    # outline marker drawn on top of the heatmap.

    EMPTY, SAFE, UNSAFE = 0, 1, 2

    theory_grid = np.full((gs, gs), EMPTY, dtype=int)
    reality_grid = np.full((gs, gs), EMPTY, dtype=int)

    n_predicted_persistent = 0
    n_actual_persistent = 0
    n_safe = 0
    n_match = 0

    for i in range(gs):
        for j in range(gs):
            if not filled[i, j]:
                continue
            f = float(vals[i, j])

            # Theory: predicted-persistent set under any continuous
            # K-Lipschitz utility-preserving defense. For the canonical
            # identity defense (ℓ = 0), the steep set reduces to {f > τ}.
            in_predicted = f > tau
            theory_grid[i, j] = UNSAFE if in_predicted else SAFE

            # Reality: actually-persistent under the identity defense,
            # i.e., cells where f(D(x)) = f(x) > τ.
            in_actual = f > tau  # under identity, post-defense f = f
            reality_grid[i, j] = UNSAFE if in_actual else SAFE

            if in_predicted:
                n_predicted_persistent += 1
            if in_actual:
                n_actual_persistent += 1
            if in_predicted == in_actual:
                n_match += 1
            if not in_predicted and not in_actual:
                n_safe += 1

    n_filled = int(filled.sum())
    n_boundary = len(bd.boundary_cells)
    discrepancies = n_filled - n_match

    # ----- Plot -----
    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.size": 9,
            "axes.titlesize": 11,
            "axes.labelsize": 9,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
        }
    )

    from matplotlib.colors import ListedColormap
    cmap = ListedColormap(["#f7fafc", "#9ae6b4", "#fc8181"])  # empty, safe, unsafe

    fig, axes = plt.subplots(1, 2, figsize=(8.0, 5.0), constrained_layout=True)

    for ax, grid, title in (
        (axes[0], theory_grid, "Theory"),
        (axes[1], reality_grid, "Reality"),
    ):
        # Use .T so that the first index is x (horizontal) and origin is bottom-left.
        ax.imshow(
            grid.T,
            origin="lower",
            cmap=cmap,
            vmin=0,
            vmax=2,
            aspect="equal",
            interpolation="nearest",
        )

        # Outline boundary cells in black so they're identifiable in both panels.
        for (bi, bj) in bd.boundary_cells:
            ax.add_patch(
                plt.Rectangle(
                    (bi - 0.5, bj - 0.5),
                    1,
                    1,
                    fill=False,
                    edgecolor="#1a202c",
                    linewidth=1.6,
                )
            )

        ax.set_xticks([0, gs // 2, gs - 1])
        ax.set_yticks([0, gs // 2, gs - 1])
        ax.set_xlim(-0.5, gs - 0.5)
        ax.set_ylim(-0.5, gs - 0.5)
        ax.set_xlabel("indirection")
        ax.set_ylabel("authority")
        ax.set_title(title)

    axes[0].set_title(
        f"Theory predicts persistent\n"
        f"$\\{{x : f(x) > \\tau\\}}$ — $n = {n_predicted_persistent}$",
        fontsize=10,
    )
    axes[1].set_title(
        f"Reality (after canonical defense)\n"
        f"$\\{{x : f(D(x)) > \\tau\\}}$ — $n = {n_actual_persistent}$",
        fontsize=10,
    )

    # Single shared legend at the bottom, well below the panels.
    from matplotlib.patches import Patch
    legend_handles = [
        Patch(facecolor="#fc8181", edgecolor="black", label=r"persistent unsafe ($f > \tau$)"),
        Patch(facecolor="#9ae6b4", edgecolor="black", label=r"safe ($f < \tau$)"),
        Patch(facecolor="#f7fafc", edgecolor="black", label="not sampled"),
        Patch(facecolor="white", edgecolor="#1a202c", linewidth=1.6, label=f"boundary cell ($n = {n_boundary}$)"),
    ]
    fig.legend(
        handles=legend_handles,
        loc="lower center",
        ncol=4,
        frameon=True,
        framealpha=0.94,
        fontsize=8.5,
        handlelength=1.6,
        handletextpad=0.6,
        columnspacing=2.4,
        borderpad=0.6,
        bbox_to_anchor=(0.5, -0.02),
    )

    fig.suptitle(
        rf"Theory vs reality (gpt-3.5-turbo-0125, $n = {n_filled}$ cells, $\tau = {tau}$)"
        "\n"
        rf"match: $\mathbf{{{n_match}/{n_filled}}}$"
        rf"  $\bullet$  discrepancies: $\mathbf{{{discrepancies}}}$",
        fontsize=11,
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="pdf", bbox_inches="tight")
    plt.close(fig)

    print(f"Wrote {out_path}")
    print(
        f"  L={L:.4f}  filled={n_filled}  predicted={n_predicted_persistent}  "
        f"actual={n_actual_persistent}  match={n_match}/{n_filled}  "
        f"boundary={n_boundary}"
    )


# ============================================================
# Non-tautological Theorem 6.2 check via the GP-smooth defense
# ============================================================


def gp_smooth_validation(
    archive_path: Path,
    out_path: Path,
    tau: float = 0.5,
    length_scale: float = 0.08,
    noise: float = 0.02,
    alpha_step: float = 0.06,
    sigmoid_steepness: float = 20.0,
    defense_kind: str = "centroid",
) -> dict:
    """Run a GP-smooth defense and check Theorem 6.2 cell-by-cell.

    Two defenses are supported:

    * ``defense_kind = "grad_step"``: gradient-step retraction along
      ``-∇μ``. Continuous and Lipschitz; ``ℓ`` ends up equal to ``L`` by
      construction (the path direction is the steepest direction), so
      this mode is satisfied by Theorem 6.2's hypotheses but does not
      probe the anisotropic regime.

    * ``defense_kind = "centroid"`` (default): smooth contraction
      toward the safe region's centroid. Continuous and Lipschitz, and
      its displacement direction is ``c - x`` rather than ``∇μ`` — so
      the empirical ``ℓ`` measured along its path can be strictly
      smaller than the surface ``L``. This is the *non-tautological*
      Theorem 6.2 check.
    """
    heatmap = load_archive_json(archive_path)

    # Extract the filled cells as ([0,1]^2 positions, AD values).
    filled_idx = np.argwhere(heatmap.filled_mask)
    h = heatmap.cell_width
    X = filled_idx.astype(float) * h  # cell positions in [0, 1]^2
    y = np.array([heatmap.values[i, j] for i, j in filled_idx])

    # Fit the GP.
    gp = fit_gp_2d(X, y, length_scale=length_scale, noise=noise)

    # Pre-compute the GP posterior on the training cells (used several
    # times below for the steep set, the boundary detection, and ℓ).
    mu_at_X_pre = gp_predict(gp, X)
    safe_mask = mu_at_X_pre < tau
    if not safe_mask.any():
        raise RuntimeError(
            "GP-smoothed surface has no cells with μ < tau; "
            "centroid defense undefined."
        )
    centroid = X[safe_mask].mean(axis=0)

    # Apply the smooth defense at every filled cell.
    if defense_kind == "grad_step":
        D_targets = np.array(
            [
                smooth_defense_target(gp, X[i], tau, alpha_step, sigmoid_steepness)
                for i in range(len(X))
            ]
        )
    elif defense_kind == "centroid":
        D_targets = np.array(
            [
                smooth_defense_target_centroid(
                    gp, X[i], centroid, tau, alpha_step, sigmoid_steepness
                )
                for i in range(len(X))
            ]
        )
    else:
        raise ValueError(
            f"unknown defense_kind: {defense_kind!r} "
            "(choices: 'grad_step', 'centroid')"
        )

    # Empirical defense Lipschitz constant K = max ||D(u) - D(v)|| / ||u - v||.
    n = len(X)
    in_dist = np.linalg.norm(X[:, None, :] - X[None, :, :], axis=2)
    out_dist = np.linalg.norm(D_targets[:, None, :] - D_targets[None, :, :], axis=2)
    np.fill_diagonal(in_dist, np.inf)
    K_emp = float((out_dist / in_dist).max())

    # Empirical defense-path Lipschitz ℓ measured along D's actual
    # displacements. We compare GP posterior values at both endpoints, NOT
    # the raw data value at the source cell — the latter would conflate
    # the GP fitting residual with the directional change of f, blowing
    # ℓ up at near-zero displacements. The trilemma's ℓ is a property of
    # the smoothed surface μ, which is what the smooth defense operates on.
    mu_at_X = mu_at_X_pre
    f_post = gp_predict(gp, D_targets)
    ell_emp = 0.0
    moved = 0
    for i in range(n):
        d = float(np.linalg.norm(D_targets[i] - X[i]))
        if d < 1e-10:
            continue
        moved += 1
        ratio = abs(float(f_post[i] - mu_at_X[i])) / d
        if ratio > ell_emp:
            ell_emp = ratio

    # L_GP = sup ||∇μ|| (over the unit square, sampled).
    L_gp = gp_max_grad_norm(gp, n_samples=600)

    # G is the maximum directional rise crossing the threshold; on the
    # discrete grid we already estimate it from data, and on the GP it
    # essentially equals the max gradient magnitude near the boundary.
    # We use the data-driven L from the validator (which equals G for
    # this surface) for consistency with the rest of the paper.
    L_data = estimate_global_L(heatmap)
    G = L_data  # surface property; unchanged by the choice of defense

    # Boundary cells on the GP-smoothed surface: cells with μ(x) ≥ tau
    # that have a close cell (within ~2 grid widths) with μ(x) < tau. We
    # use the GP posterior, not the raw data, because the smoothed surface
    # is what the smooth defense operates on.
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
        raise RuntimeError("no boundary cells found at the chosen tau")

    # Anchor: boundary cell with μ closest to tau.
    z_idx = min(boundary_idx, key=lambda i: abs(float(mu_at_X[i]) - tau))
    z_star = X[z_idx]
    slack = abs(float(mu_at_X[z_idx]) - tau)

    # Predicted steep set under the GP-smooth defense:
    #     {x : μ(x) > tau + ell*(K+1)*dist(x, z*)}
    # Actual persistent set: cells where μ(D(x)) > tau (already in f_post).
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
    theorem_violated = len(fp_int) > 0

    print()
    print("=" * 60)
    print(f"GP-smooth defense validation ({defense_kind})")
    print("=" * 60)
    print(
        f"  GP hyperparams: length_scale={length_scale}, noise={noise}"
    )
    print(
        f"  Defense:        alpha_step={alpha_step}, "
        f"sigmoid_steepness={sigmoid_steepness}"
    )
    if defense_kind == "centroid":
        print(f"                  centroid = ({centroid[0]:.3f}, {centroid[1]:.3f})")
    print(f"  Filled cells:   n = {n}, moved by D: {moved}")
    print(f"  L (data, grid): {L_data:.4f}")
    print(f"  L_GP (smooth):  {L_gp:.4f}")
    print(f"  G:              {G:.4f}")
    print(f"  K (empirical):  {K_emp:.4f}")
    print(f"  ℓ (defense-path, smooth): {ell_emp:.4f}")
    print(f"  ℓ(K+1):         {ell_emp * (K_emp + 1.0):.4f}")
    print(
        f"  transversality G > ℓ(K+1):  "
        f"{'YES' if transversality else 'NO'}  "
        f"({G:.3f} vs {ell_emp * (K_emp + 1.0):.3f})"
    )
    print(f"  predicted steep set:  {len(predicted)} cells")
    print(f"  actual persistent set: {len(actual)} cells")
    print(
        f"  TP={len(tp)}, FP_int={len(fp_int)} (real counterexamples), "
        f"FP_bdy={len(fp_bdy)}, FN={len(fn)}"
    )
    if theorem_violated:
        print(
            f"  ❌ THEOREM 6.2 VIOLATED: {len(fp_int)} interior false positives"
        )
        print(f"     cells: {[list(X[i]) for i in fp_int[:5]]}")
    elif len(predicted) == 0:
        print(
            "  ⚠ vacuous: predicted steep set is empty "
            "(transversality fails on this defense)"
        )
    else:
        print(
            f"  ✅ ALL {len(predicted)} predicted-persistent cells confirmed "
            "empirically"
        )

    result = {
        "defense": f"gp_smooth_{defense_kind}",
        "params": {
            "length_scale": length_scale,
            "noise": noise,
            "alpha_step": alpha_step,
            "sigmoid_steepness": sigmoid_steepness,
            "defense_kind": defense_kind,
            "centroid": list(centroid) if defense_kind == "centroid" else None,
        },
        "tau": tau,
        "n_filled": n,
        "n_moved_by_defense": moved,
        "L_data": L_data,
        "L_gp": L_gp,
        "G": G,
        "K_empirical": K_emp,
        "ell_empirical": ell_emp,
        "ell_times_K_plus_1": ell_emp * (K_emp + 1.0),
        "transversality_holds": transversality,
        "anchor_cell_index": int(z_idx),
        "anchor_position": list(z_star),
        "anchor_f_value": float(y[z_idx]),
        "discretization_slack": slack,
        "predicted_persistent_count": len(predicted),
        "actual_persistent_count": len(actual),
        "true_positives": len(tp),
        "false_positives_interior": len(fp_int),
        "false_positives_boundary": len(fp_bdy),
        "false_negatives": len(fn),
        "fp_interior_cell_positions": [list(X[i]) for i in fp_int],
        "theorem_violated": theorem_violated,
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        json.dump(result, f, indent=2)
    print(f"  wrote {out_path}")
    return result


def main(argv: list[str] | None = None) -> int:
    here = Path(__file__).resolve().parent
    repo = here.parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--archive",
        type=Path,
        default=repo
        / "trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json",
    )
    parser.add_argument(
        "--out-figure",
        type=Path,
        default=repo / "figures/eps_robust_saturated.pdf",
    )
    parser.add_argument(
        "--out-gp-result",
        type=Path,
        default=repo
        / "trilemma_validator/live_runs/gpt35_turbo_t05_saturated/gp_smooth_result.json",
    )
    parser.add_argument("--tau", type=float, default=0.5)
    parser.add_argument("--length-scale", type=float, default=0.08)
    parser.add_argument("--noise", type=float, default=0.02)
    parser.add_argument("--alpha-step", type=float, default=0.06)
    parser.add_argument("--sigmoid-steepness", type=float, default=20.0)
    parser.add_argument(
        "--skip-figure",
        action="store_true",
        help="Skip the eps-robust scatter figure (only run the GP validation).",
    )
    parser.add_argument(
        "--skip-gp",
        action="store_true",
        help="Skip the GP-smooth validation (only generate the figure).",
    )
    args = parser.parse_args(argv)

    if not args.skip_figure:
        make_figure(args.archive, args.out_figure, tau=args.tau)
    if not args.skip_gp:
        # Run both defenses: gradient-step (Lipschitz, ℓ = L by construction
        # — only validates the trivial regime) and centroid contraction
        # (where ℓ < L is achievable, the non-tautological case).
        for kind in ("grad_step", "centroid"):
            out = args.out_gp_result.with_name(
                args.out_gp_result.stem + f"_{kind}.json"
            )
            gp_smooth_validation(
                args.archive,
                out,
                tau=args.tau,
                length_scale=args.length_scale,
                noise=args.noise,
                alpha_step=args.alpha_step,
                sigmoid_steepness=args.sigmoid_steepness,
                defense_kind=kind,
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
