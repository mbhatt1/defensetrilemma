"""Swappable positive-definite kernels for the GP-smooth defense validator.

Every kernel has signature ``kernel(X1, X2, sigma) -> K`` where ``X1`` has
shape ``(n, d)``, ``X2`` has shape ``(m, d)``, and ``K`` has shape ``(n, m)``.
``sigma`` is the length-scale parameter (the characteristic length over
which the kernel decays). All kernels are isotropic and normalized so that
``k(x, x) = 1`` for any ``x``.

Supported:

* ``rbf_kernel``       — Gaussian / squared-exponential.
* ``matern32_kernel``  — Matern with nu = 3/2.
* ``matern52_kernel``  — Matern with nu = 5/2.

These are the three most commonly used isotropic kernels in GP regression.
RBF is infinitely differentiable; Matern(3/2) once; Matern(5/2) twice.
That means the posterior mean's smoothness (and hence the effective
Lipschitz constant of the smoothed surface) decreases as we go from RBF
to Matern(3/2). The sensitivity sweep uses this to show that the
trilemma's predictions are robust across the family.
"""

from __future__ import annotations

import numpy as np


def _pairwise_dist(X1: np.ndarray, X2: np.ndarray) -> np.ndarray:
    """Euclidean distances between rows of X1 (n, d) and rows of X2 (m, d).

    Returns an (n, m) array. Avoids the sqrt of a tiny-negative floating-
    point residual when X1 == X2 by clipping to zero.
    """
    sq = ((X1[:, None, :] - X2[None, :, :]) ** 2).sum(axis=2)
    sq = np.maximum(sq, 0.0)
    return np.sqrt(sq)


def rbf_kernel(X1: np.ndarray, X2: np.ndarray, sigma: float) -> np.ndarray:
    """RBF (squared-exponential) kernel ``k(a, b) = exp(-||a-b||^2 / (2 sigma^2))``."""
    sq = ((X1[:, None, :] - X2[None, :, :]) ** 2).sum(axis=2)
    return np.exp(-sq / (2.0 * sigma * sigma))


def matern32_kernel(X1: np.ndarray, X2: np.ndarray, sigma: float) -> np.ndarray:
    """Matern kernel with nu = 3/2.

    ``k(a, b) = (1 + sqrt(3) r / sigma) * exp(-sqrt(3) r / sigma)``
    where ``r = ||a - b||``.
    """
    r = _pairwise_dist(X1, X2)
    s = np.sqrt(3.0) * r / sigma
    return (1.0 + s) * np.exp(-s)


def matern52_kernel(X1: np.ndarray, X2: np.ndarray, sigma: float) -> np.ndarray:
    """Matern kernel with nu = 5/2.

    ``k(a, b) = (1 + sqrt(5) r / sigma + 5 r^2 / (3 sigma^2)) * exp(-sqrt(5) r / sigma)``
    where ``r = ||a - b||``.
    """
    r = _pairwise_dist(X1, X2)
    s = np.sqrt(5.0) * r / sigma
    return (1.0 + s + (5.0 * r * r) / (3.0 * sigma * sigma)) * np.exp(-s)


# ----------------------------------------------------------------------
# Gradients of k(x, X_train) w.r.t. x, evaluated at a single point.
# Used for the gradient-step / oblique defenses: ∇_x μ(x) = Σ α_i ∇_x k(x, x_i).
# ----------------------------------------------------------------------


def rbf_kernel_grad_single(x: np.ndarray, X_train: np.ndarray, sigma: float) -> np.ndarray:
    """Gradient of k(x, X_train) w.r.t. x for the RBF kernel.

    Returns an array of shape ``(n, d)`` where row i is
    ``d/dx exp(-||x - x_i||^2 / (2 sigma^2)) = -(x - x_i) / sigma^2 * k(x, x_i)``.
    """
    diff = x[None, :] - X_train  # (n, d)
    sq = (diff * diff).sum(axis=1)
    k_vals = np.exp(-sq / (2.0 * sigma * sigma))
    return -(diff / (sigma * sigma)) * k_vals[:, None]


def matern32_kernel_grad_single(
    x: np.ndarray, X_train: np.ndarray, sigma: float
) -> np.ndarray:
    """Gradient of the Matern-3/2 kernel k(x, x_i) w.r.t. x.

    For ``k = (1 + s) e^{-s}`` with ``s = sqrt(3) r / sigma`` and
    ``r = ||x - x_i||``, ``dk/dr = -3 r / sigma^2 * e^{-s}``. The
    gradient w.r.t. x is then ``(dk/dr) * (x - x_i) / r``. Cleanly:

        grad_x k(x, x_i) = -3/sigma^2 * exp(-sqrt(3) r / sigma) * (x - x_i)

    (the ``r`` cancels with the ``1/r`` from ``dr/dx``). This form is
    well-defined even at ``r = 0`` (the gradient is zero there).
    """
    diff = x[None, :] - X_train  # (n, d)
    sq = (diff * diff).sum(axis=1)
    r = np.sqrt(np.maximum(sq, 0.0))
    s = np.sqrt(3.0) * r / sigma
    factor = -3.0 / (sigma * sigma) * np.exp(-s)  # (n,)
    return factor[:, None] * diff


def matern52_kernel_grad_single(
    x: np.ndarray, X_train: np.ndarray, sigma: float
) -> np.ndarray:
    """Gradient of the Matern-5/2 kernel k(x, x_i) w.r.t. x.

    For ``k = (1 + s + 5 r^2 / (3 sigma^2)) e^{-s}`` with
    ``s = sqrt(5) r / sigma``, a careful calculation yields

        grad_x k(x, x_i) = -(5/(3 sigma^2)) * (1 + sqrt(5) r / sigma)
                           * exp(-sqrt(5) r / sigma) * (x - x_i)

    which is also well-defined at ``r = 0``.
    """
    diff = x[None, :] - X_train  # (n, d)
    sq = (diff * diff).sum(axis=1)
    r = np.sqrt(np.maximum(sq, 0.0))
    s = np.sqrt(5.0) * r / sigma
    factor = -(5.0 / (3.0 * sigma * sigma)) * (1.0 + s) * np.exp(-s)  # (n,)
    return factor[:, None] * diff


# ----------------------------------------------------------------------
# Uniform dispatch so callers can pick a kernel by name.
# ----------------------------------------------------------------------


_KERNELS = {
    "rbf": (rbf_kernel, rbf_kernel_grad_single),
    "matern32": (matern32_kernel, matern32_kernel_grad_single),
    "matern52": (matern52_kernel, matern52_kernel_grad_single),
}


def get_kernel(name: str):
    """Look up a kernel pair (K(X1, X2, sigma), grad_k(x, X_train, sigma)) by name.

    Raises ValueError on unknown names. The return value is a 2-tuple
    ``(full_kernel, gradient_single)``. The first function computes the
    Gram matrix between two sets of points; the second computes the
    gradient of ``k(x, x_i)`` w.r.t. ``x`` at a single query point
    ``x``, evaluated at every training point ``x_i``.
    """
    try:
        return _KERNELS[name]
    except KeyError as e:
        raise ValueError(
            f"Unknown kernel: {name!r}. Choices: {sorted(_KERNELS)}."
        ) from e


def available_kernels() -> list[str]:
    """Return the list of registered kernel names."""
    return sorted(_KERNELS)
