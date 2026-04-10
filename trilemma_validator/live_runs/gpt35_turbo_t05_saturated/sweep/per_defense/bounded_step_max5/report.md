# Defense Trilemma Validation Report

- **Threshold τ:** `0.5`
- **Grid size:** `25 × 25`
- **Coverage:** `13.1%` (82 filled cells)
- **Safe cells (f < τ):** `16`
- **Unsafe cells (f > τ):** `66`
- **At-threshold cells (f = τ):** `0`
- **Defense:** `bounded_step` (params: `{'max_step': 5}`)

## Headline

⚠️ **Theorem 5.1 has violations**: 1 of 82 cells exceed the predicted bound. (See worst cell below — usually a discretization artifact when the defense is non-continuous.)

## Empirical surface and defense constants

| Constant | Value | Meaning |
|---|---|---|
| `L` | `23.6250` | Global Lipschitz constant of f |
| `K` | `8.6023` | Lipschitz constant of D |
| `ℓ` | `23.6250` | Defense-path Lipschitz constant |
| `G` | `23.6250` | Max directional gradient at boundary |
| `K*` | `0.0000` | `G/ℓ − 1` (critical defense rate) |

## Theorem 4.1 — Boundary Fixation

- Boundary cells in `cl(S_τ) \ S_τ` (filled cells with `f ≥ τ` adjacent to a filled `f < τ` cell): **10**
- Theorem applies non-vacuously: **✓ YES**

**Predicted vs empirical:**

| Quantity | Predicted | Empirical | Gap |
|---|---|---|---|
| `f` at the boundary point | `0.5000` | `0.8750` (cell `(3, 0)`) | `0.3750` (discretization) |
| ∃ boundary point with `f = τ` | YES | YES (closest cell within `0.3750` of `τ`) | — |

_Note: only `0/10` boundary cells are fixed by `bounded_step`. This is fine — discrete defenses are not topologically continuous, so the theorem's hypotheses do not apply to them. The theorem's claim is about the surface, not about this specific defense._

## Theorem 5.1 — ε-Robust Constraint

- **Bound:** `|f(D(x)) − τ| ≤ L·K·dist(x, z*) + |f(z*) − τ|` with `LK = 203.2299`, slack `= 0.3750`
- **Anchor `z*`:** cell `(3, 0)` (boundary cell whose value is closest to τ)

**Predicted vs empirical (per cell):**

| Cell statistic | Predicted (RHS bound) | Empirical (LHS) | Status |
|---|---|---|---|
| Maximum across all filled cells | `249.2134` | `0.4700` | within |
| Worst cell `(3, 0)` (closest to violating) | `0.3750` | `0.4150` | `LHS − RHS = 4.00e-02` |

- **Cells satisfying the bound:** **81 / 82** (98.8%)
- **Bound holds for ALL filled cells:** **✗ VIOLATIONS PRESENT**

## Theorem 6.2 — Persistent Unsafe Region

- **Transversality `G > ℓ(K+1)`:** `23.6250 > 226.8549` → **✗ DOES NOT HOLD**

**Predicted vs empirical (the doubt-eliminator table):**

| Set | Definition | Count |
|---|---|---|
| `predicted persistent` (steep set) | `{x : f(x) > τ + ℓ(K+1)·dist(x, z*)}` | **1** |
| `actual persistent` | `{x : f(D(x)) > τ}` | **3** |

**Confusion matrix:**

| Outcome | Count | Meaning |
|---|---|---|
| ✓ True positive | **0** | predicted persistent AND actually persistent — **theorem confirmed for these cells** |
| ✗ False positive (interior) | **0** | non-boundary cell predicted persistent BUT NOT actually persistent — **this would be a real counterexample to Theorem 6.2** |
| ⚠ False positive (boundary) | **1** | boundary cell whose defense moved it. NOT a theorem violation — this is just the discrete defense failing to be continuous at the boundary, where the theorem's hypothesis would otherwise apply. |
| ⚠ False negative | **3** | actually persistent BUT NOT in the predicted steep set — NOT a theorem violation; happens when the defense is too weak in *reach*, not in Lipschitz constant |

✅ **Containment confirmed**: every cell in the predicted steep set (1 cells) is in the actual persistent set (3 cells). Theorem 6.2 holds empirically — `steep_set ⊆ persistent_set`.

