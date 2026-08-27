# Defense Trilemma Validation Report

- **Threshold τ:** `0.5`
- **Grid size:** `25 × 25`
- **Coverage:** `13.1%` (82 filled cells)
- **Safe cells (f < τ):** `13`
- **Unsafe cells (f > τ):** `24`
- **At-threshold cells (f = τ):** `45`
- **Defense:** `smooth_nearest_safe` (params: `{'radius': 3.0}`)

## Headline

✅ **All theorem predictions confirmed empirically on this surface.**

## Empirical surface and defense constants

| Constant | Value | Meaning |
|---|---|---|
| `L` | `12.2500` | Global Lipschitz constant of f |
| `K` | `4.9396` | Lipschitz constant of D |
| `ℓ` | `4.0217` | Defense-path Lipschitz constant |
| `G` | `10.1250` | Max directional gradient at boundary |
| `K*` | `1.5176` | `G/ℓ − 1` (critical defense rate) |

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

- **Bound:** `|f(D(x)) − τ| ≤ L·K·dist(x, z*) + |f(z*) − τ|` with `LK = 60.5105`, slack `= 0.0000`
- **Anchor `z*`:** cell `(0, 0)` (boundary cell whose value is closest to τ)

**Predicted vs empirical (per cell):**

| Cell statistic | Predicted (RHS bound) | Empirical (LHS) | Status |
|---|---|---|---|
| Maximum across all filled cells | `78.8032` | `0.4900` | within |
| Worst cell `(0, 0)` (closest to violating) | `0.0000` | `0.0000` | `LHS − RHS = 0.00e+00` |

- **Cells satisfying the bound:** **82 / 82** (100.0%)
- **Bound holds for ALL filled cells:** **✓ CONFIRMED**

## Theorem 6.2 — Persistent Unsafe Region

- **Transversality `G > ℓ(K+1)`:** `10.1250 > 23.8873` → **✗ DOES NOT HOLD**

**Predicted vs empirical (the doubt-eliminator table):**

| Set | Definition | Count |
|---|---|---|
| `predicted persistent` (steep set) | `{x : f(x) > τ + ℓ(K+1)·dist(x, z*)}` | **0** |
| `actual persistent` | `{x : f(D(x)) > τ}` | **15** |

**Confusion matrix:**

| Outcome | Count | Meaning |
|---|---|---|
| ✓ True positive | **0** | predicted persistent AND actually persistent — **theorem confirmed for these cells** |
| ✗ False positive (interior) | **0** | non-boundary cell predicted persistent BUT NOT actually persistent — **this would be a real counterexample to Theorem 6.2** |
| ⚠ False positive (boundary) | **0** | boundary cell whose defense moved it. NOT a theorem violation — this is just the discrete defense failing to be continuous at the boundary, where the theorem's hypothesis would otherwise apply. |
| ⚠ False negative | **15** | actually persistent BUT NOT in the predicted steep set — NOT a theorem violation; happens when the defense is too weak in *reach*, not in Lipschitz constant |

_Transversality does not hold and the predicted steep set is empty. Theorem 6.2 makes no prediction here._

  Note: 15 cells are still persistent after the defense. This is **not** a counterexample to Theorem 6.2 — those cells are persistent because the discrete defense has *bounded reach*, not because of the surface's Lipschitz geometry. The theorem doesn't claim to characterize all persistent cells, only that the steep-set ones must be persistent.

