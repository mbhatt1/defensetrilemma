import Mathlib

/-!
# Manifold of Failure — Part 18: Quantitative Cone Measure Bound

**Proves that the persistent unsafe region contains a measurable segment
(and hence has positive Lebesgue measure) when the alignment deviation
surface rises steeply at a boundary fixed point.**

## Setup

We work in `ℝ` (1-dimensional Euclidean space) to keep the
formalization clean. The key insight is purely 1D: if `f` increases
faster than `L(K+1)` along a direction near boundary point `z`, then
the "steep region" `S = {x : f(x) > τ + L(K+1)·|x - z|}` contains
an interval of positive length, hence has positive Lebesgue measure.

## Core results

1. `cone_segment_in_steep_region` — If f has directional growth rate
   c > L(K+1) near z (i.e., f(z + t) ≥ τ + c·t for small t > 0),
   then for all t ∈ (0, δ₀), the point z + t lies in the steep region.

2. `steep_region_contains_interval` — The steep region contains the
   interval (z, z + δ₀), which has positive Lebesgue measure.

3. `steep_region_volume_lower_bound` — Since (z, z + δ₀) ⊆ S, we get
   μ(S) ≥ μ((z, z + δ₀)) = δ₀ > 0.
-/

open Set Topology Filter Metric MeasureTheory

open scoped NNReal

noncomputable section

namespace MoF

/-! ## The steep region in ℝ -/

/--
The steep region in ℝ around a boundary point z: the set of points x
where f(x) exceeds the defense-compensable threshold τ + slope·|x - z|.
-/
def steepRegionR (f : ℝ → ℝ) (τ : ℝ) (slope : ℝ) (z : ℝ) : Set ℝ :=
  {x : ℝ | f x > τ + slope * |x - z|}

/-! ## 1. Cone segment membership -/

/--
**Cone segment in steep region.**

If `f` has directional growth rate `c > slope` at `z` from the right—meaning
`f(z + t) ≥ τ + c · t` for all `0 < t < δ₀`—then every point `z + t` with
`0 < t < δ₀` lies in the steep region `{x : f(x) > τ + slope · |x - z|}`.

This is the core computation: `f(z + t) ≥ τ + c·t > τ + slope·t = τ + slope·|z+t - z|`.
-/
theorem cone_segment_in_steep_region
    {f : ℝ → ℝ} {τ slope c : ℝ} {z : ℝ} {δ₀ : ℝ}
    (hc : c > slope) (_hδ : δ₀ > 0)
    (h_deriv : ∀ t : ℝ, 0 < t → t < δ₀ → f (z + t) ≥ τ + c * t)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < δ₀) :
    z + t ∈ steepRegionR f τ slope z := by
  simp only [steepRegionR, mem_setOf_eq]
  have h1 : f (z + t) ≥ τ + c * t := h_deriv t ht_pos ht_lt
  have h2 : |z + t - z| = t := by
    rw [add_sub_cancel_left]
    exact abs_of_pos ht_pos
  rw [h2]
  have h3 : slope * t < c * t := by
    exact mul_lt_mul_of_pos_right hc ht_pos
  linarith

/-! ## 2. The steep region contains an interval -/

/--
**Steep region contains an interval.**

Under the same hypotheses, the open interval `(z, z + δ₀)` is contained
in the steep region. This gives us a concrete measurable subset.
-/
theorem steep_region_contains_Ioo
    {f : ℝ → ℝ} {τ slope c : ℝ} {z : ℝ} {δ₀ : ℝ}
    (hc : c > slope) (hδ : δ₀ > 0)
    (h_deriv : ∀ t : ℝ, 0 < t → t < δ₀ → f (z + t) ≥ τ + c * t) :
    Ioo z (z + δ₀) ⊆ steepRegionR f τ slope z := by
  intro x hx
  rw [mem_Ioo] at hx
  -- Write x = z + t where t = x - z
  have ht_pos : 0 < x - z := by linarith [hx.1]
  have ht_lt : x - z < δ₀ := by linarith [hx.2]
  have hx_eq : z + (x - z) = x := by ring
  rw [← hx_eq]
  exact cone_segment_in_steep_region hc hδ h_deriv ht_pos ht_lt

/-! ## 3. Positive measure of the steep region -/

/--
**Steep region has positive Lebesgue measure.**

The interval `(z, z + δ₀)` has Lebesgue measure `δ₀ > 0`, and it is
contained in the steep region, so `μ(S) ≥ δ₀ > 0`.
-/
theorem steep_region_measure_pos
    {f : ℝ → ℝ} {τ slope c : ℝ} {z : ℝ} {δ₀ : ℝ}
    (hc : c > slope) (hδ : δ₀ > 0)
    (h_deriv : ∀ t : ℝ, 0 < t → t < δ₀ → f (z + t) ≥ τ + c * t) :
    0 < volume (steepRegionR f τ slope z) := by
  have h_sub := steep_region_contains_Ioo hc hδ h_deriv
  have h_Ioo_pos : 0 < volume (Ioo z (z + δ₀)) := by
    rw [Real.volume_Ioo]
    simp only [ENNReal.ofReal_pos]
    linarith [add_sub_cancel_left z δ₀]
  exact lt_of_lt_of_le h_Ioo_pos (measure_mono h_sub)

/-! ## 4. Full cone bound theorem -/

/--
**Input-relative defense bound (local copy).**

If `f` is `L`-Lipschitz, `D` is `K`-Lipschitz, and `D(z) = z`, then
`f(D(x)) ≥ f(x) - L(K+1)·dist(x, z)`.

This is the key Lipschitz chain: dist(D(x), x) ≤ (K+1)·dist(x,z),
hence |f(D(x)) - f(x)| ≤ L·(K+1)·dist(x,z).
-/
theorem defense_from_input_bound_R
    {f : ℝ → ℝ} {D : ℝ → ℝ}
    {L K : ℝ≥0} (hf : LipschitzWith L f) (hD : LipschitzWith K D)
    {z : ℝ} (hz_fix : D z = z) (x : ℝ) :
    f (D x) ≥ f x - ↑L * ((↑K + 1) * dist x z) := by
  -- Step 1: |f(D(x)) - f(x)| ≤ L · dist(D(x), x)
  have h_lip_f : |f (D x) - f x| ≤ ↑L * dist (D x) x := by
    have := hf.dist_le_mul (D x) x; rwa [Real.dist_eq] at this
  -- Step 2: dist(D(x), x) ≤ (K+1) · dist(x, z)
  have h_Dx_x : dist (D x) x ≤ (↑K + 1) * dist x z := by
    calc dist (D x) x
        ≤ dist (D x) (D z) + dist (D z) x := dist_triangle _ _ _
      _ ≤ ↑K * dist x z + dist z x := by
          gcongr
          · exact hD.dist_le_mul x z
          · rw [hz_fix]
      _ = ↑K * dist x z + dist x z := by rw [dist_comm z x]
      _ = (↑K + 1) * dist x z := by ring
  -- Combine
  have hL : (0 : ℝ) ≤ ↑L := L.coe_nonneg
  linarith [neg_abs_le (f (D x) - f x),
            mul_le_mul_of_nonneg_left h_Dx_x hL]

/--
**Quantitative Cone Measure Bound (Main Theorem).**

In ℝ, if:
- `f(z) = τ` (z is a boundary point),
- `D(z) = z` (z is fixed by the defense),
- `f` has directional growth rate `c > L(K+1)` from the right at `z`,

then:
1. The steep region contains the interval `(z, z + δ₀)`,
2. The steep region has positive Lebesgue measure,
3. Every point in the steep region stays unsafe after defense.
-/
theorem cone_measure_bound
    {f : ℝ → ℝ} {D : ℝ → ℝ}
    {L K : ℝ≥0} (hf : LipschitzWith L f) (hD : LipschitzWith K D)
    {z : ℝ} {τ : ℝ} (_hz_val : f z = τ) (hz_fix : D z = z)
    {c : ℝ} (hc : c > ↑L * (↑K + 1))
    {δ₀ : ℝ} (hδ : δ₀ > 0)
    (h_deriv : ∀ t : ℝ, 0 < t → t < δ₀ → f (z + t) ≥ τ + c * t) :
    -- 1. The steep region contains (z, z + δ₀)
    Ioo z (z + δ₀) ⊆ steepRegionR f τ (↑L * (↑K + 1)) z ∧
    -- 2. The steep region has positive measure
    0 < volume (steepRegionR f τ (↑L * (↑K + 1)) z) ∧
    -- 3. Every point in the steep region stays unsafe after defense
    (∀ x ∈ steepRegionR f τ (↑L * (↑K + 1)) z, f (D x) > τ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: interval contained in steep region
    exact steep_region_contains_Ioo hc hδ h_deriv
  · -- Part 2: positive measure
    exact steep_region_measure_pos hc hδ h_deriv
  · -- Part 3: defense preserves unsafety
    intro x hx
    simp only [steepRegionR, mem_setOf_eq] at hx
    -- f(x) > τ + L(K+1) · |x - z|
    -- f(D(x)) ≥ f(x) - L(K+1) · dist(x, z)
    have h_Dx_bound : f (D x) ≥ f x - ↑L * ((↑K + 1) * dist x z) :=
      defense_from_input_bound_R hf hD hz_fix x
    have h_dist_abs : dist x z = |x - z| := Real.dist_eq x z
    rw [h_dist_abs] at h_Dx_bound
    -- Now: f(D(x)) ≥ f(x) - L(K+1)|x-z| > τ + L(K+1)|x-z| - L(K+1)|x-z| = τ
    have h_rearrange : ↑L * ((↑K + 1) * |x - z|) = ↑L * (↑K + 1) * |x - z| := by ring
    rw [h_rearrange] at h_Dx_bound
    linarith

/-! ## 5. Explicit measure lower bound -/

/--
**Explicit volume lower bound.**

The Lebesgue measure of the steep region is at least `δ₀`.
-/
theorem steep_region_measure_lower_bound
    {f : ℝ → ℝ} {τ slope c : ℝ} {z : ℝ} {δ₀ : ℝ}
    (hc : c > slope) (hδ : δ₀ > 0)
    (h_deriv : ∀ t : ℝ, 0 < t → t < δ₀ → f (z + t) ≥ τ + c * t) :
    ENNReal.ofReal δ₀ ≤ volume (steepRegionR f τ slope z) := by
  have h_sub := steep_region_contains_Ioo hc hδ h_deriv
  have h_vol : volume (Ioo z (z + δ₀)) = ENNReal.ofReal (z + δ₀ - z) :=
    Real.volume_Ioo
  have h_simp : z + δ₀ - z = δ₀ := by ring
  calc ENNReal.ofReal δ₀
      = ENNReal.ofReal (z + δ₀ - z) := by rw [h_simp]
    _ = volume (Ioo z (z + δ₀)) := h_vol.symm
    _ ≤ volume (steepRegionR f τ slope z) := measure_mono h_sub

/-! ## 6. Connection to the MoF_11 persistent unsafe region -/

/--
**Corollary: directional derivative implies persistent unsafe region.**

This connects the quantitative cone bound back to the persistent unsafe
region framework of MoF_11, providing the explicit transversality witness
that `persistent_unsafe_region` requires.
-/
theorem cone_bound_implies_persistent_unsafe
    {z : ℝ} {f : ℝ → ℝ} {D : ℝ → ℝ}
    {L K : ℝ≥0} (_hf : LipschitzWith L f) (_hD : LipschitzWith K D)
    (_hf_cont : Continuous f)
    {τ : ℝ} (_hz_val : f z = τ) (_hz_fix : D z = z)
    {c : ℝ} (hc : c > ↑L * (↑K + 1))
    {δ₀ : ℝ} (hδ : δ₀ > 0)
    (h_deriv : ∀ t : ℝ, 0 < t → t < δ₀ → f (z + t) ≥ τ + c * t) :
    ∃ x₀ : ℝ, f x₀ > τ + ↑L * ((↑K + 1) * dist x₀ z) := by
  -- Use t = δ₀ / 2
  refine ⟨z + δ₀ / 2, ?_⟩
  have hδ2 : (0 : ℝ) < δ₀ / 2 := by linarith
  have hδ2_lt : δ₀ / 2 < δ₀ := by linarith
  have h1 := h_deriv (δ₀ / 2) hδ2 hδ2_lt
  have h_dist : dist (z + δ₀ / 2) z = δ₀ / 2 := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ2]
  rw [h_dist]
  have h3 : ↑L * (↑K + 1) * (δ₀ / 2) < c * (δ₀ / 2) :=
    mul_lt_mul_of_pos_right hc hδ2
  have h4 : ↑L * ((↑K + 1) * (δ₀ / 2)) = ↑L * (↑K + 1) * (δ₀ / 2) := by ring
  rw [h4]
  linarith

end MoF

end
