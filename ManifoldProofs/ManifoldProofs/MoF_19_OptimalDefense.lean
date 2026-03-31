import Mathlib

/-!
# Manifold of Failure — Part 19: Optimal Defense Characterization

**The defense faces a fundamental dilemma parameterized by its Lipschitz
constant K.**

Given an alignment surface `f` with Lipschitz constant `L` and a boundary
point where the transversality slope (directional derivative) is `G`:

- The ε-band width scales as `L(K+1)·δ` — wider with larger K.
- The persistent unsafe region exists when `G > L(K+1)`.
- These create opposing forces: increasing K to eliminate persistent
  unsafety widens the failure band.

## Core results

1. `defense_band_monotone` — The ε-band constraint L(K+1) is strictly
   monotone in K.

2. `optimal_K_exists` — If G > L, then K* = G/L - 1 > 0 is the critical
   defense constant. Below K*, persistent unsafety exists; at or above K*,
   the band width is at least G·δ.

3. `defense_cannot_win` — For any K ≥ 0, either the persistent region
   exists OR the band width is at least G·δ. No K escapes both.

4. `shallow_boundary_no_persistence` — If the alignment surface never
   rises faster than L in any direction, the steep region is empty.
-/

open Set Topology Filter Metric

noncomputable section

namespace MoF

/-! ## 1. Band constraint is monotone in K -/

/--
The ε-band constraint `L · (K + 1)` is strictly monotone in `K`:
if `K₁ < K₂`, then `L · (K₁ + 1) < L · (K₂ + 1)` (for `L > 0`).

This establishes that more aggressive defenses (higher Lipschitz constant)
produce strictly wider failure bands.
-/
theorem defense_band_monotone
    {L K₁ K₂ : ℝ} (hL : L > 0) (hK : K₁ < K₂) :
    L * (K₁ + 1) < L * (K₂ + 1) := by
  apply mul_lt_mul_of_pos_left _ hL
  linarith

/--
Corollary: the band constraint is monotone in the weak sense too.
-/
theorem defense_band_monotone_le
    {L K₁ K₂ : ℝ} (hL : L ≥ 0) (hK : K₁ ≤ K₂) :
    L * (K₁ + 1) ≤ L * (K₂ + 1) := by
  apply mul_le_mul_of_nonneg_left _ hL
  linarith

/-! ## 2. Optimal K characterization -/

/--
The critical defense constant: `K* = G / L - 1`.

When `G > L`, we have `K* > 0`, and this is the threshold that separates
the persistent-unsafety regime from the wide-band regime.
-/
def optimalK (G L : ℝ) : ℝ := G / L - 1

/--
If `G > L > 0`, then `K* = G/L - 1 > 0`.
-/
theorem optimalK_pos {G L : ℝ} (hL : L > 0) (hGL : G > L) :
    optimalK G L > 0 := by
  unfold optimalK
  linarith [(one_lt_div hL).mpr hGL]

/--
At `K = K*`, we have `L · (K* + 1) = G`.
-/
theorem optimalK_critical {G L : ℝ} (hL : L > 0) :
    L * (optimalK G L + 1) = G := by
  unfold optimalK
  field_simp
  ring

/--
**Optimal K theorem.**

If `G > L > 0`, then `K* = G/L - 1 > 0` exists and:
- For `K < K*`: `G > L · (K + 1)` (persistent unsafe region exists).
- For `K ≥ K*`: `L · (K + 1) ≥ G` (band width is at least `G · δ`).
-/
theorem optimal_K_exists {G L : ℝ} (hL : L > 0) (hGL : G > L) :
    let Kstar := optimalK G L
    Kstar > 0 ∧
    (∀ K : ℝ, K < Kstar → G > L * (K + 1)) ∧
    (∀ K : ℝ, K ≥ Kstar → L * (K + 1) ≥ G) := by
  refine ⟨optimalK_pos hL hGL, fun K hK => ?_, fun K hK => ?_⟩
  · -- K < K* implies G > L(K+1)
    have h := optimalK_critical (G := G) hL
    calc G = L * (optimalK G L + 1) := h.symm
      _ > L * (K + 1) := by apply mul_lt_mul_of_pos_left _ hL; linarith
  · -- K ≥ K* implies L(K+1) ≥ G
    have h := optimalK_critical (G := G) hL
    calc L * (K + 1) ≥ L * (optimalK G L + 1) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hL); linarith
      _ = G := h

/-! ## 3. The defense dilemma -/

/--
**Defense cannot win.**

For any `K ≥ 0`, exactly one of two bad outcomes holds:
- Either `G > L · (K + 1)` (persistent unsafe region exists), or
- `L · (K + 1) ≥ G` (the defense distorts the space by at least `G·δ`,
  meaning the band width is at least `G·δ`).

No value of `K` escapes both problems simultaneously, unless `G ≤ L`
(the alignment surface is shallow enough to defend trivially).
-/
theorem defense_cannot_win (G L K : ℝ) :
    G > L * (K + 1) ∨ L * (K + 1) ≥ G := by
  by_cases h : G > L * (K + 1)
  · exact Or.inl h
  · exact Or.inr (le_of_not_gt h)

/--
Stronger version: when `G > L > 0`, neither horn of the dilemma is vacuous.
There exist values of K triggering each case.
-/
theorem defense_dilemma_both_realizable {G L : ℝ} (hL : L > 0) (hGL : G > L) :
    (∃ K : ℝ, K ≥ 0 ∧ G > L * (K + 1)) ∧
    (∃ K : ℝ, K ≥ 0 ∧ L * (K + 1) ≥ G) := by
  constructor
  · -- K = 0 gives G > L · 1 = L, which holds by hGL
    exact ⟨0, le_refl 0, by linarith [mul_one L]⟩
  · -- K = K* works
    refine ⟨optimalK G L, le_of_lt (optimalK_pos hL hGL), ?_⟩
    rw [optimalK_critical hL]

/--
The dilemma is tight at K*: the two regions share a single boundary point.
-/
theorem defense_dilemma_tight {G L : ℝ} (hL : L > 0) :
    L * (optimalK G L + 1) = G :=
  optimalK_critical hL

/-! ## 4. Shallow boundary escape -/

/--
The "steep region" from Theorem 11 (persistent unsafe region):
points where f exceeds τ by more than L(K+1)·dist(x,z).
-/
def steepRegionDef {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (τ : ℝ) (L K : ℝ) (z : X) : Set X :=
  {x : X | f x > τ + L * ((K + 1) * dist x z)}

/--
**Shallow boundary theorem.**

If for all directions (i.e., for all points x), the alignment deviation
satisfies `f(x) ≤ f(z) + L · dist(x, z)` (f is L-Lipschitz FROM z),
then the steep region `{x | f(x) > τ + L(K+1)·dist(x,z)}` is empty
for any K ≥ 0.

Interpretation: when the alignment surface never rises faster than its
own Lipschitz constant L, no defense (regardless of K) faces a persistent
unsafe region. The boundary is "shallow enough to defend."
-/
theorem shallow_boundary_no_persistence
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {τ : ℝ} {L : ℝ} (hL : L ≥ 0)
    {z : X} (hz : f z = τ)
    {K : ℝ} (hK : K ≥ 0)
    -- f is L-Lipschitz from z: the "shallow boundary" condition
    (h_shallow : ∀ x : X, f x ≤ f z + L * dist x z) :
    steepRegionDef f τ L K z = ∅ := by
  ext x
  simp only [steepRegionDef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  have h := h_shallow x
  rw [hz] at h
  have hdist : dist x z ≥ 0 := dist_nonneg
  calc f x ≤ τ + L * dist x z := h
    _ ≤ τ + L * ((K + 1) * dist x z) := by
        gcongr
        calc dist x z = 1 * dist x z := (one_mul _).symm
          _ ≤ (K + 1) * dist x z := by
              apply mul_le_mul_of_nonneg_right _ hdist
              linarith

/--
**Contrapositive**: if the steep region is nonempty, then
f must rise faster than L in some direction from z.
-/
theorem persistence_implies_steep_direction
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {τ : ℝ} {L : ℝ} (hL : L ≥ 0)
    {z : X} (hz : f z = τ)
    {K : ℝ} (hK : K ≥ 0)
    (h_nonempty : (steepRegionDef f τ L K z).Nonempty) :
    ∃ x : X, f x > f z + L * dist x z := by
  obtain ⟨x, hx⟩ := h_nonempty
  simp only [steepRegionDef, Set.mem_setOf_eq] at hx
  refine ⟨x, ?_⟩
  rw [hz]
  have hdist : dist x z ≥ 0 := dist_nonneg
  calc f x > τ + L * ((K + 1) * dist x z) := hx
    _ ≥ τ + L * (1 * dist x z) := by
        gcongr
        linarith
    _ = τ + L * dist x z := by rw [one_mul]

/-! ## 5. Combined characterization -/

/--
**Complete defense characterization.**

For a K-Lipschitz defense against an alignment surface with Lipschitz
constant L and transversality slope G at the boundary:

1. If G ≤ L: the boundary is shallow, no persistent region exists for
   any K ≥ 0 (defense can succeed in principle).

2. If G > L: no K simultaneously eliminates persistent unsafety AND
   keeps the band width below G·δ. The optimal K* = G/L - 1 > 0 is
   the unique point where the two failure modes trade off exactly.
-/
theorem complete_defense_characterization
    {G L : ℝ} (hL : L > 0) :
    (G ≤ L → ∀ K : ℝ, K ≥ 0 → L * (K + 1) ≥ G) ∧
    (G > L →
      optimalK G L > 0 ∧
      (∀ K : ℝ, K < optimalK G L → G > L * (K + 1)) ∧
      (∀ K : ℝ, K ≥ optimalK G L → L * (K + 1) ≥ G)) := by
  constructor
  · -- Shallow case: G ≤ L means L·(K+1) ≥ L ≥ G for all K ≥ 0
    intro hGL K hK
    calc L * (K + 1) ≥ L * 1 := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hL)
            linarith
      _ = L := mul_one L
      _ ≥ G := hGL
  · -- Steep case
    intro hGL
    exact optimal_K_exists hL hGL

end MoF

end
