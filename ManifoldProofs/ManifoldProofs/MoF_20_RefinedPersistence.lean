import Mathlib
import ManifoldProofs.MoF_11_EpsilonRobust

/-!
# Manifold of Failure — Part 20: Refined Persistence with Defense-Path Lipschitz

**The persistence theorem in MoF_11 uses the GLOBAL Lipschitz constant L
of f for both the input-relative bound and the steep region definition.
But if f is globally L-Lipschitz, then f(x) ≤ f(z) + L·dist(x,z), so the
steep region {x : f(x) > τ + L(K+1)·dist(x,z)} is EMPTY for K ≥ 0.
This makes the persistence theorem vacuously true.**

**This file introduces the DEFENSE-PATH Lipschitz constant ℓ ≤ L, which
bounds |f(D(x)) - f(x)| / dist(D(x), x). When f is anisotropic — steep
in the growth direction (gradient G) but smooth along defense displacement
paths — we can have ℓ < L, making G > ℓ(K+1) achievable even for K > 0.**

## Core results

1. `defense_from_input_bound_refined` — Input-relative bound using ℓ:
   f(D(x)) ≥ f(x) - ℓ(K+1)·dist(x,z).

2. `steepRegion_refined` — Steep region defined with ℓ instead of L.

3. `persistent_unsafe_refined` — If the ℓ-steep region is nonempty,
   defense leaves positive-measure volume unsafe.

4. `global_lipschitz_steep_empty` — When ℓ = L (isotropic), the steep
   region is always empty for K ≥ 0. (This is MoF_19's
   `shallow_boundary_no_persistence` restated.)
-/

open Set Topology Filter Metric MeasureTheory

open scoped NNReal

noncomputable section

namespace MoF.Refined

/-! ## 1. Input-relative bound with defense-path Lipschitz constant -/

/--
**Refined input-relative bound.**

Instead of using f's global Lipschitz constant L, this version takes
a defense-path Lipschitz constant ℓ as a hypothesis: the bound
|f(D(x)) - f(x)| ≤ ℓ · dist(D(x), x) holds for all relevant x.

This gives: f(D(x)) ≥ f(x) - ℓ · (K+1) · dist(x, z).

When f is anisotropic, ℓ < L is possible, making the bound tighter
and the steep region larger.
-/
theorem defense_from_input_bound_refined
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {D : X → X}
    {ℓ : ℝ} (hℓ : ℓ ≥ 0)
    {K : ℝ≥0} (hD : LipschitzWith K D)
    -- Defense-path Lipschitz: f changes by at most ℓ along defense displacements
    (h_local : ∀ x, |f (D x) - f x| ≤ ℓ * dist (D x) x)
    {z : X} (hz_fix : D z = z) (x : X) :
    f (D x) ≥ f x - ℓ * ((↑K + 1) * dist x z) := by
  have h_disp : dist (D x) x ≤ (↑K + 1) * dist x z :=
    defense_fixes_nearby hD hz_fix
  -- |f(D(x)) - f(x)| ≤ ℓ · dist(D(x), x) implies f(D(x)) ≥ f(x) - ℓ · dist(D(x), x)
  have h1 : f (D x) ≥ f x - ℓ * dist (D x) x := by
    linarith [neg_abs_le (f (D x) - f x), h_local x]
  -- ℓ · dist(D(x), x) ≤ ℓ · (K+1) · dist(x, z)
  have h2 : ℓ * dist (D x) x ≤ ℓ * ((↑K + 1) * dist x z) :=
    mul_le_mul_of_nonneg_left h_disp hℓ
  linarith

/-! ## 2. Steep region with defense-path Lipschitz -/

/--
The steep region defined with defense-path Lipschitz constant ℓ
(possibly smaller than f's global Lipschitz constant L).
-/
def steepRegionRefined {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (τ : ℝ) (ℓ : ℝ) (K : ℝ≥0) (z : X) : Set X :=
  {x : X | f x > τ + ℓ * ((↑K + 1) * dist x z)}

theorem steepRegionRefined_isOpen
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} (hf : Continuous f) (τ : ℝ) (ℓ : ℝ) (K : ℝ≥0) (z : X) :
    IsOpen (steepRegionRefined f τ ℓ K z) := by
  unfold steepRegionRefined
  apply isOpen_lt
  · exact continuous_const.add
      (continuous_const.mul (continuous_const.mul (continuous_id.dist continuous_const)))
  · exact hf

/-! ## 3. Persistence with defense-path Lipschitz -/

/--
**Points in the ℓ-steep region remain unsafe after defense.**
-/
theorem defense_preserves_unsafe_refined
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {D : X → X}
    {ℓ : ℝ} (hℓ : ℓ ≥ 0)
    {K : ℝ≥0} (hD : LipschitzWith K D)
    (h_local : ∀ x, |f (D x) - f x| ≤ ℓ * dist (D x) x)
    {z : X} (hz_fix : D z = z)
    {τ : ℝ} {x : X} (hx : x ∈ steepRegionRefined f τ ℓ K z) :
    f (D x) > τ := by
  have h := defense_from_input_bound_refined hℓ hD h_local hz_fix x
  have hx' : f x > τ + ℓ * ((↑K + 1) * dist x z) := hx
  linarith

/--
**Refined Persistent Unsafe Region.**

If the alignment surface has defense-path Lipschitz constant ℓ ≤ L,
and the ℓ-steep region is nonempty, then a positive-measure set remains
unsafe after defense.

This is non-vacuous when f is anisotropic: steep in the growth
direction (gradient G) but smooth along defense displacement paths
(defense-path constant ℓ < L). The condition G > ℓ(K+1) is then
achievable even for K > 0.
-/
theorem persistent_unsafe_refined
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
    {f : X → ℝ} {D : X → X}
    {ℓ : ℝ} (hℓ : ℓ ≥ 0)
    {K : ℝ≥0} (hD : LipschitzWith K D)
    (hf_cont : Continuous f)
    (h_local : ∀ x, |f (D x) - f x| ≤ ℓ * dist (D x) x)
    {z : X} (hz_fix : D z = z)
    {τ : ℝ}
    (h_steep : ∃ x₀ : X, f x₀ > τ + ℓ * ((↑K + 1) * dist x₀ z)) :
    0 < μ {x : X | f (D x) > τ} := by
  obtain ⟨x₀, hx₀⟩ := h_steep
  have h_open := steepRegionRefined_isOpen hf_cont τ ℓ K z
  have h_ne : (steepRegionRefined f τ ℓ K z).Nonempty := ⟨x₀, hx₀⟩
  have h_pos : 0 < μ (steepRegionRefined f τ ℓ K z) :=
    IsOpen.measure_pos μ h_open h_ne
  have h_sub : steepRegionRefined f τ ℓ K z ⊆ {x : X | f (D x) > τ} :=
    fun x hx => defense_preserves_unsafe_refined hℓ hD h_local hz_fix hx
  exact lt_of_lt_of_le h_pos (measure_mono h_sub)

/-! ## 4. Isotropic case: steep region is empty -/

/--
**When ℓ = L (isotropic), the steep region is always empty for K ≥ 0.**

If f is L-Lipschitz from z (i.e., f(x) ≤ f(z) + L·dist(x,z)),
and we use ℓ = L in the steep region definition, then:
  f(x) ≤ τ + L·dist(x,z) ≤ τ + L·(K+1)·dist(x,z)
so no x satisfies f(x) > τ + L·(K+1)·dist(x,z).

This shows the persistence theorem is non-trivial ONLY in the
anisotropic case (ℓ < L).
-/
theorem isotropic_steep_empty
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {τ : ℝ} {L : ℝ} (hL : L ≥ 0)
    {z : X} (hz : f z = τ)
    {K : ℝ≥0} (hK : (0 : ℝ) ≤ ↑K)
    -- f is L-Lipschitz from z (follows from global L-Lipschitz)
    (h_lip_from_z : ∀ x : X, f x ≤ f z + L * dist x z) :
    steepRegionRefined f τ L K z = ∅ := by
  ext x
  simp only [steepRegionRefined, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  have h := h_lip_from_z x
  rw [hz] at h
  have hdist : dist x z ≥ 0 := dist_nonneg
  calc f x ≤ τ + L * dist x z := h
    _ ≤ τ + L * ((↑K + 1) * dist x z) := by
        gcongr
        calc dist x z = 1 * dist x z := (one_mul _).symm
          _ ≤ (↑K + 1) * dist x z := by
              apply mul_le_mul_of_nonneg_right _ hdist
              linarith

end MoF.Refined
