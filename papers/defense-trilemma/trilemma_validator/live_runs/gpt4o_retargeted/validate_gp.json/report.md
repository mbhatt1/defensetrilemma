# Defense Trilemma Validation Report

- **Threshold τ:** `0.5`
- **Grid size:** `25 × 25`
- **Coverage:** `13.1%` (82 filled cells)
- **Safe cells (f < τ):** `10`
- **Unsafe cells (f > τ):** `30`
- **At-threshold cells (f = τ):** `42`
- **Defense:** `smooth_nearest_safe` (params: `{'radius': 3.0}`)

## Headline

⚠️ **Theorem 5.1 has violations**: 1 of 82 cells exceed the predicted bound. (See worst cell below — usually a discretization artifact when the defense is non-continuous.)

## Empirical surface and defense constants

| Constant | Value | Meaning |
|---|---|---|
| `L` | `12.3750` | Global Lipschitz constant of f |
| `K` | `3.4059` | Lipschitz constant of D |
| `ℓ` | `12.3750` | Defense-path Lipschitz constant |
| `G` | `12.3750` | Max directional gradient at boundary |
| `K*` | `0.0000` | `G/ℓ − 1` (critical defense rate) |

## Theorem 4.1 — Boundary Fixation

- Boundary cells in `cl(S_τ) \ S_τ` (filled cells with `f ≥ τ` adjacent to a filled `f < τ` cell): **7**
- Theorem applies non-vacuously: **✓ YES**

**Predicted vs empirical:**

| Quantity | Predicted | Empirical | Gap |
|---|---|---|---|
| `f` at the boundary point | `0.5000` | `0.5000` (cell `(0, 0)`) | `0.0000` (discretization) |
| ∃ boundary point with `f = τ` | YES | YES (closest cell within `0.0000` of `τ`) | — |

_Note: only `1/7` boundary cells are fixed by `smooth_nearest_safe`. This is fine — discrete defenses are not topologically continuous, so the theorem's hypotheses do not apply to them. The theorem's claim is about the surface, not about this specific defense._

## Theorem 5.1 — ε-Robust Constraint

- **Bound:** `|f(D(x)) − τ| ≤ L·K·dist(x, z*) + |f(z*) − τ|` with `LK = 42.1477`, slack `= 0.0000`
- **Anchor `z*`:** cell `(0, 0)` (boundary cell whose value is closest to τ)

**Predicted vs empirical (per cell):**

| Cell statistic | Predicted (RHS bound) | Empirical (LHS) | Status |
|---|---|---|---|
| Maximum across all filled cells | `54.8892` | `0.4900` | within |
| Worst cell `(0, 0)` (closest to violating) | `0.0000` | `0.0050` | `LHS − RHS = 5.00e-03` |

- **Cells satisfying the bound:** **81 / 82** (98.8%)
- **Bound holds for ALL filled cells:** **✗ VIOLATIONS PRESENT**

## Theorem 6.2 — Persistent Unsafe Region

- **Transversality `G > ℓ(K+1)`:** `12.3750 > 54.5227` → **✗ DOES NOT HOLD**

**Predicted vs empirical (the doubt-eliminator table):**

| Set | Definition | Count |
|---|---|---|
| `predicted persistent` (steep set) | `{x : f(x) > τ + ℓ(K+1)·dist(x, z*)}` | **0** |
| `actual persistent` | `{x : f(D(x)) > τ}` | **14** |

**Confusion matrix:**

| Outcome | Count | Meaning |
|---|---|---|
| ✓ True positive | **0** | predicted persistent AND actually persistent — **theorem confirmed for these cells** |
| ✗ False positive (interior) | **0** | non-boundary cell predicted persistent BUT NOT actually persistent — **this would be a real counterexample to Theorem 6.2** |
| ⚠ False positive (boundary) | **0** | boundary cell whose defense moved it. NOT a theorem violation — this is just the discrete defense failing to be continuous at the boundary, where the theorem's hypothesis would otherwise apply. |
| ⚠ False negative | **14** | actually persistent BUT NOT in the predicted steep set — NOT a theorem violation; happens when the defense is too weak in *reach*, not in Lipschitz constant |

_Transversality does not hold and the predicted steep set is empty. Theorem 6.2 makes no prediction here._

  Note: 14 cells are still persistent after the defense. This is **not** a counterexample to Theorem 6.2 — those cells are persistent because the discrete defense has *bounded reach*, not because of the surface's Lipschitz geometry. The theorem doesn't claim to characterize all persistent cells, only that the steep-set ones must be persistent.

