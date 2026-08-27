"""Defense simulators that produce a discrete map ``D : grid → grid``.

Each defense returns a ``DefenseMap``: an int array ``targets`` of shape
``(grid_size, grid_size, 2)`` where ``targets[i, j]`` is the cell that ``(i, j)``
is sent to by the defense. Cells that are unfilled (NaN in the heatmap) are
mapped to themselves and excluded from downstream metrics.

The defenses here are deliberately discrete and operate on the same grid as the
input heatmap. They are *not* meant to be the actual production defenses; they
are stand-ins that let us measure the empirical Lipschitz constants and check
the trilemma's persistence condition on real alignment-deviation surfaces.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Optional

import numpy as np

from .loader import Heatmap


@dataclass
class DefenseMap:
    """Discrete defense ``D``, expressed as a per-cell target on the grid.

    Attributes:
        targets: Int array of shape ``(grid_size, grid_size, 2)``. ``targets[i, j]`` is
            the ``(i', j')`` index of the cell that ``(i, j)`` is sent to by the defense.
        name: Human-readable name of the defense (used in reports).
        params: Free-form dict of parameters used to construct the defense.
    """

    targets: np.ndarray  # shape (G, G, 2), int
    name: str
    params: dict

    @property
    def grid_size(self) -> int:
        return int(self.targets.shape[0])

    def displaced_mask(self) -> np.ndarray:
        """Boolean mask of cells whose target is different from themselves."""
        gs = self.grid_size
        ii, jj = np.indices((gs, gs))
        return (self.targets[..., 0] != ii) | (self.targets[..., 1] != jj)


class Defense(ABC):
    """Base class for defenses. Subclasses implement ``build``."""

    name: str

    @abstractmethod
    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        """Construct the per-cell target map for the given heatmap and threshold."""
        raise NotImplementedError


def _safe_mask(heatmap: Heatmap, tau: float) -> np.ndarray:
    """Return a boolean mask of strictly-safe filled cells (``f(x) < tau``)."""
    return heatmap.filled_mask & (heatmap.values < tau)


def _identity_targets(grid_size: int) -> np.ndarray:
    """Identity target map: ``targets[i, j] = (i, j)``."""
    ii, jj = np.indices((grid_size, grid_size))
    return np.stack([ii, jj], axis=-1).astype(int)


class IdentityDefense(Defense):
    """``D(x) = x`` everywhere. Lipschitz constant 1, defense-path Lipschitz 0."""

    name = "identity"

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        return DefenseMap(
            targets=_identity_targets(heatmap.grid_size),
            name=self.name,
            params={},
        )


class NearestSafeDefense(Defense):
    """``D(x) = arg min_{s ∈ S} dist(s, x)`` for unsafe ``x``; identity on safe.

    The nearest-safe projection is *complete by construction* on the discrete grid
    (every unsafe cell is sent to a safe cell), but it is typically not Lipschitz
    in any useful sense — it has discontinuities along the safe-region cut locus.
    Comparing it against the bounded-step defense shows the trilemma's tradeoff:
    completeness costs an unbounded Lipschitz constant.
    """

    name = "nearest_safe"

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        gs = heatmap.grid_size
        targets = _identity_targets(gs)
        safe = _safe_mask(heatmap, tau)
        if not safe.any():
            # No safe cells: defense cannot do anything; identity by convention.
            return DefenseMap(targets=targets, name=self.name, params={})

        safe_idx = np.argwhere(safe)
        for i in range(gs):
            for j in range(gs):
                if not heatmap.filled_mask[i, j] or safe[i, j]:
                    continue
                d2 = (safe_idx[:, 0] - i) ** 2 + (safe_idx[:, 1] - j) ** 2
                k = int(np.argmin(d2))
                targets[i, j] = safe_idx[k]
        return DefenseMap(targets=targets, name=self.name, params={})


class BoundedStepDefense(Defense):
    """Like nearest-safe projection, but with a hard cap on displacement.

    For each unsafe filled cell ``(i, j)``:
      1. Find the nearest filled safe cell ``s`` (Euclidean grid distance).
      2. If ``dist(s, (i, j)) <= max_step``, jump to ``s``.
      3. Otherwise, take a single grid step from ``(i, j)`` toward ``s`` and stop.

    Step (3) means that for unsafe cells whose nearest safe cell is more than
    ``max_step`` cells away, the defense moves them by exactly one grid cell —
    they remain unsafe after defense. This is the persistence-theorem regime.
    """

    name = "bounded_step"

    def __init__(self, max_step: int = 2):
        if max_step < 1:
            raise ValueError("max_step must be >= 1 (in grid cells)")
        self.max_step = int(max_step)

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        gs = heatmap.grid_size
        targets = _identity_targets(gs)
        safe = _safe_mask(heatmap, tau)
        if not safe.any():
            return DefenseMap(
                targets=targets, name=self.name, params={"max_step": self.max_step}
            )

        safe_idx = np.argwhere(safe)
        for i in range(gs):
            for j in range(gs):
                if not heatmap.filled_mask[i, j] or safe[i, j]:
                    continue
                # Nearest filled safe cell.
                d2 = (safe_idx[:, 0] - i) ** 2 + (safe_idx[:, 1] - j) ** 2
                k = int(np.argmin(d2))
                si, sj = safe_idx[k]
                d = float(np.sqrt(d2[k]))
                if d <= self.max_step:
                    targets[i, j] = (si, sj)
                else:
                    # Move one grid step toward (si, sj). We use sign of the difference,
                    # which gives a Chebyshev (king-move) step that's always within the grid.
                    di = int(np.sign(si - i))
                    dj = int(np.sign(sj - j))
                    ti, tj = i + di, j + dj
                    if 0 <= ti < gs and 0 <= tj < gs:
                        targets[i, j] = (ti, tj)
                    # else: clamped, keep identity
        return DefenseMap(
            targets=targets, name=self.name, params={"max_step": self.max_step}
        )


# ============================================================
# Continuous (Lipschitz) defenses
# ============================================================
#
# The defenses below are *continuous* (and in particular Lipschitz) maps from
# the grid back to the grid. They are the discrete analogs of the continuous
# Lipschitz defenses the Defense Trilemma paper considers. Each produces a
# displacement field over the full ``grid_size x grid_size`` domain (even at
# cells that are unfilled, so that callers can recompute ``f`` via
# nearest-filled neighbor lookup). The returned ``targets`` array is
# per-cell integer (i', j') — the displacement is rounded to the nearest grid
# cell, and if the continuous target falls outside the grid it is clamped.
#
# Each defense documents (a) its *exact* continuous formula and (b) its
# analytical Lipschitz constant bound. The Lipschitz argument is what makes
# these the right objects for testing Theorem 6.2 — the paper agent quotes
# these docstrings verbatim in Section 10.1.


def _filled_safe_positions(heatmap: Heatmap, tau: float) -> np.ndarray:
    """Return the (n, 2) float array of grid coordinates of filled safe cells."""
    safe = _safe_mask(heatmap, tau)
    idx = np.argwhere(safe).astype(float)
    return idx


def _round_to_grid(pos: np.ndarray, grid_size: int) -> tuple[int, int]:
    """Round a continuous grid position to the nearest in-range integer cell."""
    ti = int(np.clip(round(float(pos[0])), 0, grid_size - 1))
    tj = int(np.clip(round(float(pos[1])), 0, grid_size - 1))
    return ti, tj


def _all_cells_float(grid_size: int) -> np.ndarray:
    """All (i, j) grid cells as a (G*G, 2) float array."""
    ii, jj = np.indices((grid_size, grid_size))
    return np.stack([ii.ravel(), jj.ravel()], axis=-1).astype(float)


def smooth_nearest_safe(
    heatmap: Heatmap, tau: float, radius: float = 3.0
) -> DefenseMap:
    r"""Gaussian-weighted pull toward the nearest filled safe cell.

    **Formula.** For each cell ``x = (i, j)`` (filled or not), let
    ``S = {s_k}`` be the set of filled safe cells (``f(s) < tau``). Define
    Gaussian weights

        w_k(x) = exp( - ||x - s_k||^2 / (2 r^2) )

    and take the weighted centroid

        D(x) = \sum_k w_k(x) s_k / \sum_k w_k(x) .

    We then round ``D(x)`` to the nearest integer grid cell. The continuous
    map (before rounding) is the output.

    **Lipschitz argument.** The weights ``w_k`` are smooth functions of ``x``
    and the normalized weighted average is a smooth convex combination of
    fixed points ``s_k``. The differentiable map ``x \mapsto D(x)`` is
    bounded-derivative on the compact unit square because the Gaussian and
    its derivative are bounded, and thus globally Lipschitz. A uniform
    bound on ``K = \mathrm{Lip}(D)`` is ``K \leq (\text{diam}(S)) / r``,
    which gives ``K \leq \sqrt{2} / r`` in unit-square normalized
    coordinates.

    **Continuity.** Because ``w_k`` are smooth and strictly positive, the
    denominator is bounded away from zero and ``D`` is ``C^\infty`` over
    ``\mathbb{R}^2``. This is the continuous alternative to
    ``NearestSafeDefense`` (which has a cut-locus discontinuity).

    Args:
        heatmap: the 2D alignment-deviation surface.
        tau: safety threshold.
        radius: Gaussian bandwidth in **grid cells** (not normalized
            coordinates). A reasonable default is ``3.0`` for a 25x25 grid.

    Returns:
        A ``DefenseMap`` whose ``targets`` is filled on the full grid.
    """
    gs = heatmap.grid_size
    targets = _identity_targets(gs)
    safe_idx = _filled_safe_positions(heatmap, tau)
    if len(safe_idx) == 0:
        return DefenseMap(
            targets=targets,
            name="smooth_nearest_safe",
            params={"radius": float(radius)},
        )
    for i in range(gs):
        for j in range(gs):
            # Compute weighted-centroid over filled safe cells.
            d2 = (safe_idx[:, 0] - i) ** 2 + (safe_idx[:, 1] - j) ** 2
            w = np.exp(-d2 / (2.0 * radius * radius))
            w_sum = float(w.sum())
            if w_sum <= 0.0:
                continue
            pos = (w[:, None] * safe_idx).sum(axis=0) / w_sum
            ti, tj = _round_to_grid(pos, gs)
            targets[i, j] = (ti, tj)
    return DefenseMap(
        targets=targets,
        name="smooth_nearest_safe",
        params={"radius": float(radius)},
    )


def kernel_smoothed(
    heatmap: Heatmap, tau: float, bandwidth: float = 2.5
) -> DefenseMap:
    r"""Nadaraya-Watson smoothing of the per-cell nearest-safe map.

    **Formula.** Let ``T_0 : x \mapsto s_{k(x)}`` be the (discontinuous)
    nearest-safe projection, where ``s_{k(x)}`` is the closest filled safe
    cell to ``x`` (Euclidean, grid coordinates). Define a Gaussian kernel

        K_h(x, y) = exp( - ||x - y||^2 / (2 h^2) )

    and the Nadaraya-Watson smoothed map

        D(x) = \sum_{y \in G_f} K_h(x, y) T_0(y) / \sum_{y \in G_f} K_h(x, y)

    where ``G_f`` is the set of **filled** cells (safe or unsafe). Round to
    the nearest grid cell.

    **Lipschitz argument.** ``D`` is the Nadaraya-Watson kernel smoother of
    a bounded function ``T_0`` with a Gaussian kernel of bandwidth ``h``.
    This is a classic smoothing operator: ``D`` is ``C^\infty`` and
    ``\mathrm{Lip}(D) \leq C / h`` for a constant ``C`` depending on
    ``\sup_y ||T_0(y)||`` and the unit-square diameter. Neighbors in the
    input map to neighbors in the output: the difference ``||D(x_1) -
    D(x_2)||`` is controlled by ``||x_1 - x_2||`` via the kernel
    derivative.

    **Continuity.** The denominator is strictly positive everywhere
    (Gaussian kernel is strictly positive), so ``D`` is defined and smooth
    on all of ``\mathbb{R}^2``.

    Args:
        heatmap: the 2D alignment-deviation surface.
        tau: safety threshold.
        bandwidth: kernel bandwidth ``h`` in **grid cells**. Larger values
            smooth more aggressively; default 2.5 balances fidelity to the
            nearest-safe baseline against continuity.

    Returns:
        A ``DefenseMap`` whose ``targets`` is filled on the full grid.
    """
    gs = heatmap.grid_size
    targets = _identity_targets(gs)
    safe_idx = _filled_safe_positions(heatmap, tau)
    filled_idx = np.argwhere(heatmap.filled_mask).astype(float)
    if len(safe_idx) == 0 or len(filled_idx) == 0:
        return DefenseMap(
            targets=targets,
            name="kernel_smoothed",
            params={"bandwidth": float(bandwidth)},
        )
    # Pre-compute T_0(y) for every filled cell y: nearest filled safe cell.
    T0 = np.empty_like(filled_idx)
    for k in range(len(filled_idx)):
        y = filled_idx[k]
        d2 = (safe_idx[:, 0] - y[0]) ** 2 + (safe_idx[:, 1] - y[1]) ** 2
        T0[k] = safe_idx[int(np.argmin(d2))]
    # Now smooth over all grid cells x.
    for i in range(gs):
        for j in range(gs):
            d2 = (filled_idx[:, 0] - i) ** 2 + (filled_idx[:, 1] - j) ** 2
            w = np.exp(-d2 / (2.0 * bandwidth * bandwidth))
            w_sum = float(w.sum())
            if w_sum <= 0.0:
                continue
            pos = (w[:, None] * T0).sum(axis=0) / w_sum
            ti, tj = _round_to_grid(pos, gs)
            targets[i, j] = (ti, tj)
    return DefenseMap(
        targets=targets,
        name="kernel_smoothed",
        params={"bandwidth": float(bandwidth)},
    )


def softly_constrained_projection(
    heatmap: Heatmap, tau: float, alpha: float = 2.0
) -> DefenseMap:
    r"""Softmin projection onto the set of filled safe cells.

    **Formula.** Over filled safe cells ``{s_k}``, define softmin weights

        w_k(x) = exp( - alpha * ||x - s_k|| )

    and take

        D(x) = \sum_k w_k(x) s_k / \sum_k w_k(x) .

    In the limit ``alpha \to \infty`` this recovers the hard nearest-safe
    projection ``\arg\min_k ||x - s_k||``; for finite ``alpha`` the
    projection is softened and continuous.

    **Lipschitz argument.** Softmin on a finite point set with a Euclidean
    distance argument is smooth (the softmin function is ``C^\infty`` as
    long as the weights are positive, which they are here since
    ``e^{-\alpha ||x - s_k||} > 0``). The map ``x \mapsto D(x)`` is
    therefore smooth; on the compact unit square its derivative is bounded,
    giving ``K = \mathrm{Lip}(D) \leq \alpha \cdot \sqrt{2}``. Smaller
    ``alpha`` yields a smaller Lipschitz constant at the cost of accuracy.

    **Continuity.** ``D`` is smooth on ``\mathbb{R}^2`` for any finite
    ``alpha > 0``. This is the direct continuous counterpart to
    ``NearestSafeDefense``.

    Args:
        heatmap: the 2D alignment-deviation surface.
        tau: safety threshold.
        alpha: softmin temperature (inverse; larger => sharper). Default 2.0
            gives a mild smoothing; set alpha=10 to approach hard projection.

    Returns:
        A ``DefenseMap`` whose ``targets`` is filled on the full grid.
    """
    gs = heatmap.grid_size
    targets = _identity_targets(gs)
    safe_idx = _filled_safe_positions(heatmap, tau)
    if len(safe_idx) == 0:
        return DefenseMap(
            targets=targets,
            name="softly_constrained_projection",
            params={"alpha": float(alpha)},
        )
    for i in range(gs):
        for j in range(gs):
            d = np.sqrt(
                (safe_idx[:, 0] - i) ** 2 + (safe_idx[:, 1] - j) ** 2
            )
            # Subtract the min for numerical stability before exponentiating.
            logits = -alpha * d
            logits -= logits.max()
            w = np.exp(logits)
            w_sum = float(w.sum())
            if w_sum <= 0.0:
                continue
            pos = (w[:, None] * safe_idx).sum(axis=0) / w_sum
            ti, tj = _round_to_grid(pos, gs)
            targets[i, j] = (ti, tj)
    return DefenseMap(
        targets=targets,
        name="softly_constrained_projection",
        params={"alpha": float(alpha)},
    )


class SmoothNearestSafeDefense(Defense):
    """Wrapper around :func:`smooth_nearest_safe` for the ``get_defense`` factory."""

    name = "smooth_nearest_safe"

    def __init__(self, radius: float = 3.0):
        self.radius = float(radius)

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        return smooth_nearest_safe(heatmap, tau, radius=self.radius)


class KernelSmoothedDefense(Defense):
    """Wrapper around :func:`kernel_smoothed` for the ``get_defense`` factory."""

    name = "kernel_smoothed"

    def __init__(self, bandwidth: float = 2.5):
        self.bandwidth = float(bandwidth)

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        return kernel_smoothed(heatmap, tau, bandwidth=self.bandwidth)


class SoftlyConstrainedProjectionDefense(Defense):
    """Wrapper around :func:`softly_constrained_projection` for the factory."""

    name = "softly_constrained_projection"

    def __init__(self, alpha: float = 2.0):
        self.alpha = float(alpha)

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        return softly_constrained_projection(heatmap, tau, alpha=self.alpha)


class GPSmoothObliqueDefense(Defense):
    """GP-smooth oblique defense, snapped to grid cells.

    Fits a 2D RBF Gaussian Process to the filled cells, then applies the
    oblique smooth defense (a small step mixing the negative gradient of
    the GP posterior with its 90° tangent) at each filled cell. The
    continuous post-defense position is then snapped to the nearest
    *filled* grid cell so it fits the standard ``DefenseMap`` interface.

    Parameters mirror those in ``scripts/make_paper_figure.py``.
    """

    name = "gp_smooth_oblique"

    def __init__(
        self,
        *,
        length_scale: float = 0.20,
        noise: float = 0.02,
        alpha_step: float = 0.003,
        sigmoid_steepness: float = 2.0,
        oblique_angle_deg: float = 89.5,
    ):
        self.length_scale = float(length_scale)
        self.noise = float(noise)
        self.alpha_step = float(alpha_step)
        self.sigmoid_steepness = float(sigmoid_steepness)
        self.oblique_angle_deg = float(oblique_angle_deg)

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        from .resolution import _fit_gp, _oblique_target

        gs = heatmap.grid_size
        targets = _identity_targets(gs)
        filled_idx = np.argwhere(heatmap.filled_mask)
        if len(filled_idx) < 4:
            return DefenseMap(
                targets=targets,
                name=self.name,
                params=self._params(),
            )

        h = heatmap.cell_width
        X = filled_idx.astype(float) * h
        y = np.array([heatmap.values[i, j] for i, j in filled_idx])
        gp = _fit_gp(X, y, length_scale=self.length_scale, noise=self.noise)

        post = np.array(
            [
                _oblique_target(
                    gp,
                    X[i],
                    tau,
                    self.alpha_step,
                    self.sigmoid_steepness,
                    self.oblique_angle_deg,
                )
                for i in range(len(X))
            ]
        )
        filled_positions = filled_idx.astype(float) * h
        for k, (i, j) in enumerate(filled_idx):
            d2 = ((filled_positions - post[k][None, :]) ** 2).sum(axis=1)
            nearest = int(np.argmin(d2))
            ti, tj = filled_idx[nearest]
            targets[int(i), int(j)] = (int(ti), int(tj))

        return DefenseMap(
            targets=targets,
            name=self.name,
            params=self._params(),
        )

    def _params(self) -> dict:
        return {
            "length_scale": self.length_scale,
            "noise": self.noise,
            "alpha_step": self.alpha_step,
            "sigmoid_steepness": self.sigmoid_steepness,
            "oblique_angle_deg": self.oblique_angle_deg,
        }


def get_defense(
    name: str,
    *,
    max_step: Optional[int] = None,
    radius: Optional[float] = None,
    bandwidth: Optional[float] = None,
    alpha: Optional[float] = None,
) -> Defense:
    """Factory: build a defense by name.

    Supported names:

    * ``identity`` — ``D(x) = x`` everywhere (sanity check; tautological).
    * ``nearest_safe`` — hard nearest-safe projection (discontinuous).
    * ``bounded_step`` — nearest-safe with hard displacement cap (pass
      ``max_step``). Non-continuous.
    * ``smooth_nearest_safe`` — Gaussian-weighted centroid of filled safe
      cells (continuous; ``radius`` parameter).
    * ``kernel_smoothed`` — Nadaraya-Watson smoothing of nearest-safe
      (continuous; ``bandwidth`` parameter).
    * ``softly_constrained_projection`` — softmin projection onto filled
      safe cells (continuous; ``alpha`` parameter).
    """
    if name == "identity":
        return IdentityDefense()
    if name == "nearest_safe":
        return NearestSafeDefense()
    if name == "bounded_step":
        return BoundedStepDefense(max_step=max_step or 2)
    if name == "smooth_nearest_safe":
        return SmoothNearestSafeDefense(radius=radius if radius is not None else 3.0)
    if name == "kernel_smoothed":
        return KernelSmoothedDefense(
            bandwidth=bandwidth if bandwidth is not None else 2.5
        )
    if name == "softly_constrained_projection":
        return SoftlyConstrainedProjectionDefense(
            alpha=alpha if alpha is not None else 2.0
        )
    if name in ("gp_smooth_oblique", "oblique_gp_smooth"):
        return GPSmoothObliqueDefense()
    raise ValueError(
        f"Unknown defense: {name!r}. Choices: identity, nearest_safe, "
        "bounded_step, smooth_nearest_safe, kernel_smoothed, "
        "softly_constrained_projection, gp_smooth_oblique."
    )
