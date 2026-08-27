"""Empirical estimators for the Lipschitz constants and directional gradients
that appear in the Defense Trilemma theorems.

All estimates use grid-based finite differences. Formal specification:

**Distance metric.** All distances are the Euclidean ``L^2`` norm on the
normalized grid-coordinate plane ``[0, 1]^2``. Specifically, the grid cell
``(i, j)`` has continuous coordinates ``(i * h, j * h)`` where
``h = heatmap.cell_width = 1 / grid_size``. So
``dist(a, b) = h * sqrt((a_i - b_i)^2 + (a_j - b_j)^2)``.

**Filled cells.** A grid cell is *filled* iff ``heatmap.values[i, j]`` is
not NaN (threshold: ``~np.isnan``). Unfilled cells are excluded from every
pair in every estimator — no imputation is performed. Pair counts in each
estimator's docstring assume ``n = |filled cells|``.

**Anchor selection (z*).** When an "anchor" boundary point is required
(Theorems 4.1, 5.1, 6.2), ``z*`` is the boundary cell (element of
``cl(S_tau) \\ S_tau``) whose value is closest to ``tau``:
``z* = argmin_z |f(z) - tau|``. **Tiebreak rule:** on ties, we take the
lexicographically smallest ``(row, col)`` (in practice, the order is the
``list`` iteration order of ``find_boundary_cells``, which is row-major
from ``(0, 0)``).

**Symmetry.** Every estimator iterates over *unordered pairs* — the
all-pairs matrix arithmetic in ``estimate_global_L`` and
``estimate_boundary_gradient_G`` is symmetric (we take absolute differences
of ``f``). ``estimate_defense_K`` is also symmetric. ``estimate_defense_path_ell``
iterates single cells with their target, not pairs.

Conventions:

* ``L``       — global Lipschitz constant of the alignment-deviation surface ``f``.
* ``K``       — Lipschitz constant of the defense map ``D``.
* ``ell``     — defense-path Lipschitz constant: how much ``f`` varies along
                the displacement direction ``D(x) - x``. Always ``<= L``.
* ``G``       — maximum directional rate at which ``f`` rises crossing the
                safe-unsafe boundary. Estimated from finite differences across
                neighboring cells where the threshold is crossed.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .defenses import DefenseMap
from .loader import Heatmap


# 8-neighborhood offsets (Chebyshev/king moves). We use the 8-neighborhood
# rather than 4 because diagonal moves give a tighter L estimate (smaller
# distances are also tested) and they let G be estimated in oblique directions.
_NEIGHBORS = np.array(
    [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)],
    dtype=int,
)


@dataclass
class LipschitzEstimates:
    """Container for the four core estimates."""

    L: float
    K: float
    ell: float
    G: float

    @property
    def K_star(self) -> float:
        """Critical defense Lipschitz constant ``K* = G/ell - 1``.

        Returns ``+inf`` when ``ell == 0`` (the identity defense, where the
        persistence condition ``G > ell(K+1)`` is automatically satisfied for
        any positive ``G``).
        """
        if self.ell <= 0:
            return float("inf")
        return self.G / self.ell - 1.0

    def persistence_condition(self) -> bool:
        """Return True iff the persistence condition ``G > ell * (K + 1)`` holds."""
        return self.G > self.ell * (self.K + 1.0)

    def to_dict(self) -> dict:
        return {
            "L": self.L,
            "K": self.K,
            "ell": self.ell,
            "G": self.G,
            "K_star": self.K_star,
            "persistence_condition_met": self.persistence_condition(),
        }


def _cell_dist(a: tuple[int, int], b: tuple[int, int], cell_width: float) -> float:
    return float(np.hypot(a[0] - b[0], a[1] - b[1]) * cell_width)


def _filled_indices(heatmap: Heatmap) -> np.ndarray:
    """Return an (n, 2) int array of (i, j) for every filled cell."""
    return np.argwhere(heatmap.filled_mask)


def estimate_global_L(heatmap: Heatmap) -> float:
    r"""Empirical global Lipschitz constant of ``f`` over all pairs of filled cells.

    **Formula.**

    .. math::

        \hat L = \max_{a, b \in G_f,\, a \neq b}
            \frac{|f(a) - f(b)|}{\|a - b\|}

    where ``G_f`` is the set of filled cells and ``||·||`` is the Euclidean
    norm on the normalized grid ``[0, 1]^2`` (see module docstring).

    **Pairs considered.** All unordered pairs ``(a, b)`` with ``a \neq b``
    among the ``n`` filled cells — i.e., ``n(n-1)/2`` pairs. Unfilled cells
    are excluded; no pair involving a NaN-valued cell is examined.

    **Symmetry.** The absolute value in the numerator makes the estimator
    symmetric under swapping ``a`` and ``b``, so we effectively iterate
    unordered pairs.

    Returns 0.0 when fewer than two cells are filled.
    """
    h = heatmap.cell_width
    vals = heatmap.values
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return 0.0
    fvals = vals[idx[:, 0], idx[:, 1]]
    # All-pairs distance and value-difference matrices.
    di = idx[:, 0:1] - idx[:, 0:1].T
    dj = idx[:, 1:2] - idx[:, 1:2].T
    dist = np.hypot(di, dj).astype(float) * h
    diff = np.abs(fvals[:, None] - fvals[None, :])
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(dist > 0, diff / dist, 0.0)
    return float(ratio.max())


def estimate_defense_K(defense: DefenseMap, heatmap: Heatmap) -> float:
    r"""Empirical Lipschitz constant of the defense map ``D`` over all filled pairs.

    **Formula.**

    .. math::

        \hat K = \max_{u, v \in G_f,\, u \neq v}
            \frac{\|D(u) - D(v)\|}{\|u - v\|}

    where ``||·||`` is Euclidean on normalized ``[0, 1]^2`` grid coordinates
    (both input and output).

    **Pairs considered.** All unordered pairs ``(u, v)`` with ``u \neq v``
    among filled cells. ``D(x)`` is read from ``defense.targets[i, j]``,
    which is defined on every cell; unfilled cells are excluded on the
    *input* side only.

    **Symmetry.** The ratio is symmetric under swapping ``u`` and ``v``.

    Returns 0.0 if fewer than two cells are filled.
    """
    h = heatmap.cell_width
    targets = defense.targets
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return 0.0

    src = idx.astype(float)
    tgt = targets[idx[:, 0], idx[:, 1]].astype(float)

    di = src[:, 0:1] - src[:, 0:1].T
    dj = src[:, 1:2] - src[:, 1:2].T
    in_dist = np.hypot(di, dj) * h

    tdi = tgt[:, 0:1] - tgt[:, 0:1].T
    tdj = tgt[:, 1:2] - tgt[:, 1:2].T
    out_dist = np.hypot(tdi, tdj) * h

    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(in_dist > 0, out_dist / in_dist, 0.0)
    return float(ratio.max())


def estimate_defense_path_ell(defense: DefenseMap, heatmap: Heatmap) -> float:
    r"""Empirical defense-path Lipschitz constant ``ell``.

    **Formula.**

    .. math::

        \hat \ell = \max_{x \in G_f,\, D(x) \neq x,\, D(x) \in G_f}
            \frac{|f(D(x)) - f(x)|}{\|D(x) - x\|}

    where ``||·||`` is Euclidean on normalized ``[0, 1]^2`` grid coordinates.

    **Cells considered.** Single filled cells ``x`` (not pairs) for which
    ``D(x) \neq x`` AND ``D(x)`` is also a filled cell. Cells whose defense
    target is unfilled are skipped (the estimator cannot evaluate
    ``f(D(x))`` without imputation and imputation is never performed).

    **Supremum over the empty set = 0.** Returns 0.0 when the defense is
    the identity (no displaced cells), matching the paper's convention.

    **Symmetry.** Not applicable — this is a per-cell (not pair) estimator.
    The path is directed from ``x`` to ``D(x)``.
    """
    h = heatmap.cell_width
    vals = heatmap.values
    filled = heatmap.filled_mask
    gs = heatmap.grid_size
    targets = defense.targets

    best = 0.0
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j]:
                continue
            ti, tj = int(targets[i, j, 0]), int(targets[i, j, 1])
            if (ti, tj) == (i, j):
                continue
            if not filled[ti, tj]:
                continue
            d = h * float(np.hypot(ti - i, tj - j))
            if d <= 0:
                continue
            ratio = abs(float(vals[ti, tj] - vals[i, j])) / d
            if ratio > best:
                best = ratio
    return best


def estimate_boundary_gradient_G(heatmap: Heatmap, tau: float) -> float:
    r"""Estimate the maximum directional rate at which ``f`` rises across the boundary.

    **Formula.**

    .. math::

        \hat G = \max_{a \in S_\tau^{\mathrm{filled}},\, b \in U_\tau^{\mathrm{filled}}}
            \frac{f(b) - f(a)}{\|a - b\|}

    where ``S_tau^filled = {x in G_f : f(x) < tau}`` and
    ``U_tau^filled = {x in G_f : f(x) > tau}``, and ``||·||`` is Euclidean on
    normalized ``[0, 1]^2`` grid coordinates.

    **Pairs considered.** All (strictly-safe, strictly-unsafe) ordered pairs
    among filled cells — ``|S_tau^filled| * |U_tau^filled|`` pairs in total.
    Unfilled cells and cells exactly at ``f = tau`` are excluded (the latter
    are measure-zero in the continuous limit).

    **Symmetry.** The pair ``(a, b)`` here is *oriented* (safe to unsafe),
    so the rise is always non-negative and we take the maximum of a
    non-negative ratio. The set of pairs is symmetric under reordering of
    the safe/unsafe partitions.

    Returns 0.0 when either ``S_tau^filled`` or ``U_tau^filled`` is empty
    (trilemma preconditions fail; no impossibility predicted).
    """
    h = heatmap.cell_width
    vals = heatmap.values
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return 0.0
    fvals = vals[idx[:, 0], idx[:, 1]]
    safe = fvals < tau
    unsafe = fvals > tau
    if not safe.any() or not unsafe.any():
        return 0.0

    safe_idx = np.where(safe)[0]
    unsafe_idx = np.where(unsafe)[0]
    sa = idx[safe_idx]
    ub = idx[unsafe_idx]
    sa_f = fvals[safe_idx]
    ub_f = fvals[unsafe_idx]

    di = ub[:, 0:1] - sa[:, 0:1].T
    dj = ub[:, 1:2] - sa[:, 1:2].T
    dist = np.hypot(di, dj).astype(float) * h
    rise = ub_f[:, None] - sa_f[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(dist > 0, rise / dist, 0.0)
    return float(ratio.max())


def estimate_all(
    heatmap: Heatmap, defense: DefenseMap, tau: float
) -> LipschitzEstimates:
    """Run all four estimators and return them as a single dataclass."""
    return LipschitzEstimates(
        L=estimate_global_L(heatmap),
        K=estimate_defense_K(defense, heatmap),
        ell=estimate_defense_path_ell(defense, heatmap),
        G=estimate_boundary_gradient_G(heatmap, tau),
    )


# ============================================================
# Per-pair finite differences — used by the bootstrap
# ============================================================


def pairwise_L_ratios(heatmap: Heatmap) -> np.ndarray:
    """Return the flat array of ``|f(a) - f(b)| / dist(a, b)`` over filled pairs.

    Used by ``uncertainty.bootstrap_ci`` to resample the ``max`` distribution
    with bootstrap CIs. Only includes ordered pairs with ``a < b``
    (upper-triangular of the all-pairs matrix) to avoid double-counting.
    """
    h = heatmap.cell_width
    vals = heatmap.values
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return np.array([], dtype=float)
    fvals = vals[idx[:, 0], idx[:, 1]]
    di = idx[:, 0:1] - idx[:, 0:1].T
    dj = idx[:, 1:2] - idx[:, 1:2].T
    dist = np.hypot(di, dj).astype(float) * h
    diff = np.abs(fvals[:, None] - fvals[None, :])
    iu, ju = np.triu_indices(n, k=1)
    d = dist[iu, ju]
    r = diff[iu, ju]
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(d > 0, r / d, 0.0)
    return ratio


def pairwise_G_ratios(heatmap: Heatmap, tau: float) -> np.ndarray:
    """Return the flat array of ``(f(b) - f(a)) / dist(a, b)`` for safe-unsafe pairs."""
    h = heatmap.cell_width
    vals = heatmap.values
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return np.array([], dtype=float)
    fvals = vals[idx[:, 0], idx[:, 1]]
    safe = fvals < tau
    unsafe = fvals > tau
    if not safe.any() or not unsafe.any():
        return np.array([], dtype=float)
    safe_i = idx[safe]
    unsafe_i = idx[unsafe]
    safe_f = fvals[safe]
    unsafe_f = fvals[unsafe]
    di = unsafe_i[:, 0:1] - safe_i[:, 0:1].T
    dj = unsafe_i[:, 1:2] - safe_i[:, 1:2].T
    dist = np.hypot(di, dj).astype(float) * h
    rise = unsafe_f[:, None] - safe_f[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(dist > 0, rise / dist, 0.0)
    return ratio.ravel()


def per_cell_ell_ratios(defense: DefenseMap, heatmap: Heatmap) -> np.ndarray:
    """Return the flat array of ``|f(D(x)) - f(x)| / dist(D(x), x)`` per moved cell."""
    h = heatmap.cell_width
    vals = heatmap.values
    filled = heatmap.filled_mask
    gs = heatmap.grid_size
    targets = defense.targets
    out: list[float] = []
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j]:
                continue
            ti, tj = int(targets[i, j, 0]), int(targets[i, j, 1])
            if (ti, tj) == (i, j) or not filled[ti, tj]:
                continue
            d = h * float(np.hypot(ti - i, tj - j))
            if d <= 0:
                continue
            out.append(abs(float(vals[ti, tj] - vals[i, j])) / d)
    return np.array(out, dtype=float)


def per_pair_K_ratios(defense: DefenseMap, heatmap: Heatmap) -> np.ndarray:
    """Return flat array of ``||D(u) - D(v)|| / ||u - v||`` over unordered filled pairs."""
    h = heatmap.cell_width
    targets = defense.targets
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return np.array([], dtype=float)
    src = idx.astype(float)
    tgt = targets[idx[:, 0], idx[:, 1]].astype(float)
    di = src[:, 0:1] - src[:, 0:1].T
    dj = src[:, 1:2] - src[:, 1:2].T
    in_dist = np.hypot(di, dj) * h
    tdi = tgt[:, 0:1] - tgt[:, 0:1].T
    tdj = tgt[:, 1:2] - tgt[:, 1:2].T
    out_dist = np.hypot(tdi, tdj) * h
    iu, ju = np.triu_indices(n, k=1)
    d_in = in_dist[iu, ju]
    d_out = out_dist[iu, ju]
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(d_in > 0, d_out / d_in, 0.0)
    return ratio
