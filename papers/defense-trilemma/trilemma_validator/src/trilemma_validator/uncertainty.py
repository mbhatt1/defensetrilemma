"""Bootstrap confidence intervals for Lipschitz/gradient estimators.

We report bootstrap CIs on ``L``, ``K``, ``ell``, ``G`` by resampling the
per-pair (or per-cell) finite-difference populations with replacement and
recomputing the ``max`` on each resample. This gives an honest
uncertainty estimate on the point estimators that ``lipschitz.py``
produces. (The max is the relevant statistic because every Lipschitz
estimator is a supremum.)

Bootstrap setup:

* We draw ``B`` bootstrap resamples (default ``1000``).
* Each resample has size equal to the original sample size (with
  replacement).
* The reported CI is a **percentile interval**: the alpha/2 and 1 - alpha/2
  quantiles of the bootstrapped max distribution. (Not BCa; we want a
  simple, transparent CI.)
* We also report the **median** of the bootstrap distribution as a
  robust point estimate, alongside the original max.

Reference: Efron & Tibshirani, *An Introduction to the Bootstrap* (1993),
chapter 13 (bootstrap percentile interval).
"""

from __future__ import annotations

from typing import Tuple

import numpy as np


def bootstrap_ci(
    values: np.ndarray,
    B: int = 1000,
    alpha: float = 0.05,
    seed: int = 0,
    statistic: str = "max",
) -> Tuple[float, float, float]:
    """Percentile bootstrap CI on a summary statistic of ``values``.

    Args:
        values: 1-D array of per-pair or per-cell ratios.
        B: number of bootstrap resamples. Default 1000.
        alpha: two-sided CI level (``alpha=0.05`` -> 95% CI). Default 0.05.
        seed: PRNG seed for reproducibility. Default 0.
        statistic: one of ``"max"`` (default), ``"mean"``, or ``"median"``.

    Returns:
        ``(median_of_bootstrap, lo, hi)``: the bootstrap-resampled median
        of the chosen statistic, and the ``(alpha/2, 1 - alpha/2)``
        percentile endpoints.

    The returned **median** is the median over B resamples of the chosen
    statistic (not the median of the original data). This is robust
    against resamples that happen to draw pathological neighborhoods. If
    ``values`` is empty, returns ``(nan, nan, nan)``.
    """
    values = np.asarray(values, dtype=float)
    values = values[~np.isnan(values)]
    if values.size == 0:
        return (float("nan"), float("nan"), float("nan"))

    rng = np.random.default_rng(seed)
    n = values.size

    if statistic == "max":
        op = np.max
    elif statistic == "mean":
        op = np.mean
    elif statistic == "median":
        op = np.median
    else:
        raise ValueError(f"Unknown statistic: {statistic!r}")

    # Vectorized resample: (B, n) matrix of indices.
    # For modest n and B this is fine memory-wise; guard for extreme sizes.
    if n * B <= 10_000_000:
        idx = rng.integers(0, n, size=(B, n))
        samples = values[idx]
        stats = op(samples, axis=1)
    else:
        stats = np.empty(B, dtype=float)
        for b in range(B):
            resample = values[rng.integers(0, n, size=n)]
            stats[b] = float(op(resample))

    lo_q = alpha / 2.0
    hi_q = 1.0 - alpha / 2.0
    lo = float(np.quantile(stats, lo_q))
    hi = float(np.quantile(stats, hi_q))
    median = float(np.median(stats))
    return (median, lo, hi)


def bootstrap_estimator_cis(
    heatmap,
    defense,
    tau: float,
    B: int = 1000,
    alpha: float = 0.05,
    seed: int = 0,
) -> dict:
    """Return a dict ``{L, K, ell, G}`` of ``(median, lo, hi)`` bootstrap CIs.

    Each CI is computed on the per-pair or per-cell population for the
    corresponding estimator, with the ``max`` as the statistic (matching
    the estimator's definition).
    """
    from . import lipschitz as _lp

    L_pop = _lp.pairwise_L_ratios(heatmap)
    K_pop = _lp.per_pair_K_ratios(defense, heatmap)
    ell_pop = _lp.per_cell_ell_ratios(defense, heatmap)
    G_pop = _lp.pairwise_G_ratios(heatmap, tau)

    return {
        "B": B,
        "alpha": alpha,
        "L": {"population_size": int(L_pop.size),
              "ci": bootstrap_ci(L_pop, B=B, alpha=alpha, seed=seed)},
        "K": {"population_size": int(K_pop.size),
              "ci": bootstrap_ci(K_pop, B=B, alpha=alpha, seed=seed + 1)},
        "ell": {"population_size": int(ell_pop.size),
                "ci": bootstrap_ci(ell_pop, B=B, alpha=alpha, seed=seed + 2)},
        "G": {"population_size": int(G_pop.size),
              "ci": bootstrap_ci(G_pop, B=B, alpha=alpha, seed=seed + 3)},
    }
