import Mathlib
import ManifoldProofs.MoF_10_GradientAttack
import ManifoldProofs.MoF_20_RefinedPersistence

/-!
# Manifold of Failure — Part 21: Gradient Chain

**Closes the formalization gap between ‖∇f(z)‖ > ℓ(K+1) and the
persistent unsafe region.**

The paper's argument chain is:

  1. f differentiable at z with ‖f'‖ = G > ℓ(K+1)
  2. ∃ unit vector v with f'(v) > ℓ(K+1)      [from operator norm]
  3. ∀ sufficiently small t > 0: f(z+tv) > τ + ℓ(K+1)·t  [from derivative]
  4. z + tv ∈ steep region S                    [from step 3]
  5. persistent_unsafe_refined applies           [from step 4]

Previously, step 2 was an informal mathematical fact and step 3
was assumed as a hypothesis (not derived from the derivative).
This file formalises both missing links.

## Core results

1. `near_optimal_direction` — If ‖f'‖ > c ≥ 0, ∃ unit vector v
   with f'(v) > c.
2. `deriv_implies_local_growth` — HasFDerivAt + f'(v) > c implies
   f(z + tv) ≥ f(z) + c·t for small t > 0.
3. `deriv_implies_strict_local_growth` — Strict version: f(z + tv) > τ + c·t.
4. `gradient_norm_implies_steep_nonempty` — The full chain:
   ‖f'‖ > ℓ(K+1) implies ∃ x₀ in the steep region.
5. `gradient_chain_persistent_unsafe` — Combined with
   persistent_unsafe_refined: positive-measure set stays unsafe.
-/

open Set Filter Topology Metric MeasureTheory Asymptotics

open scoped NNReal

noncomputable section

namespace MoF.GradientChain

/-! ## 1. Near-optimal direction from operator norm -/

/--
If `f' : E →L[ℝ] ℝ` has operator norm `‖f'‖ > c ≥ 0`, there exists a
unit vector `v` with `f' v > c`.

Proof: By `exists_lt_apply_of_lt_opNorm`, ∃ x with ‖x‖ < 1 and
|f' x| > c.  Since c ≥ 0, x ≠ 0. Normalise w = x/‖x‖; since ‖x‖ < 1,
|f' w| = |f' x|/‖x‖ ≥ |f' x| > c. Choose sign to make f' v > 0.
-/
theorem near_optimal_direction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f' : E →L[ℝ] ℝ) {c : ℝ} (hc : c ≥ 0) (hf' : c < ‖f'‖) :
    ∃ v : E, ‖v‖ = 1 ∧ f' v > c := by
  obtain ⟨x, hx_norm, hx_val⟩ := f'.exists_lt_apply_of_lt_opNorm hf'
  have hx_ne : x ≠ 0 := by
    intro heq; simp [heq] at hx_val; linarith
  set w := (‖x‖⁻¹) • x with hw_def
  have hw_norm : ‖w‖ = 1 := by
    rw [hw_def, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx_ne)]
  have hx_norm_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx_ne
  have h_inv_ge : 1 ≤ ‖x‖⁻¹ := by
    rw [one_le_inv₀ hx_norm_pos]; exact le_of_lt hx_norm
  have hw_val : |f' w| > c := by
    rw [hw_def, map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm]
    calc ‖x‖⁻¹ * |f' x| ≥ 1 * |f' x| :=
            mul_le_mul_of_nonneg_right h_inv_ge (abs_nonneg _)
      _ = |f' x| := one_mul _
      _ > c := hx_val
  by_cases hpos : 0 < f' w
  · exact ⟨w, hw_norm, by rwa [abs_of_pos hpos] at hw_val⟩
  · push_neg at hpos
    refine ⟨-w, by rw [norm_neg, hw_norm], ?_⟩
    rw [map_neg]; linarith [abs_of_nonpos hpos ▸ hw_val]

/-! ## 2. Derivative implies local linear growth -/

/--
**Derivative implies local growth bound (non-strict).**

If `f` has Fréchet derivative `f'` at `z`, `f(z) = τ`, and `f'(v) > c`
for a unit vector `v`, then ∃ δ > 0 such that for all t ∈ (0, δ):
  f(z + t•v) ≥ τ + c·t

Proof: Set ε = f'(v) − c > 0. By HasFDerivAt, ∃ δ > 0 with
|f(z+h) − f(z) − f'(h)| ≤ ε·‖h‖ for ‖h‖ < δ. For h = t•v, ‖h‖ = t,
so f(z+tv) ≥ f(z) + t·f'(v) − ε·t = τ + c·t.
-/
theorem deriv_implies_local_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {z : E}
    (hf : HasFDerivAt f f' z) {τ : ℝ} (hz : f z = τ)
    {v : E} (_hv : ‖v‖ = 1) {c : ℝ} (hc : f' v > c) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      f (z + t • v) ≥ τ + c * t := by
  -- Use the line-restriction and slope approach from MoF_10
  have h_line : HasDerivAt (fun t : ℝ => f (z + t • v)) (f' v) 0 :=
    hasFDerivAt_line_restrict hf
  -- Repackage: the function t ↦ f(z+tv) - τ - c*t has derivative f'v - c > 0 at 0
  -- and value 0 at t = 0. So it is eventually positive for t > 0.
  set g := fun t : ℝ => f (z + t • v) - τ - c * t with hg_def
  have hg0 : g 0 = 0 := by simp [hg_def, hz]
  have hg_deriv : HasDerivAt g (f' v - c) 0 := by
    have h_const : HasDerivAt (fun t : ℝ => τ + c * t) c 0 := by
      have := (hasDerivAt_id (0 : ℝ)).const_mul c |>.const_add τ
      simp only [mul_one] at this; exact this
    have h_sub := h_line.sub h_const
    show HasDerivAt (fun t => f (z + t • v) - τ - c * t) (f' v - c) 0
    have : (fun t => f (z + t • v) - τ - c * t) = (fun t => f (z + t • v) - (τ + c * t)) := by
      ext t; ring
    rw [this]; exact h_sub
  have hg_pos : f' v - c > 0 := by linarith
  -- g'(0) > 0 and g(0) = 0, so g(t) > 0 for small t > 0
  have h_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t > 0 := by
    have h_asc := discrete_ascent_improvement hg_deriv hg_pos
    filter_upwards [h_asc] with t ht
    simp only [zero_add] at ht; linarith [hg0]
  -- Extract δ
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset] at h_ev
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := h_ev
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have hmem := hδ_sub ⟨ht_pos, ht_lt⟩
  simp only [Set.mem_setOf_eq] at hmem
  -- hmem : f(z + t•v) - τ - c*t > 0
  linarith

/--
**Derivative implies strict local growth.**

If `f'(v) > c`, then for small t > 0, `f(z + tv) > τ + c·t` (strictly).
Uses midpoint `c' = (f'v + c)/2` as the bound parameter: since c' > c and
`deriv_implies_local_growth` gives `f(z+tv) ≥ τ + c'·t`, we get strict `>`.
-/
theorem deriv_implies_strict_local_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {z : E}
    (hf : HasFDerivAt f f' z) {τ : ℝ} (hz : f z = τ)
    {v : E} (hv : ‖v‖ = 1) {c : ℝ} (hc : f' v > c) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      f (z + t • v) > τ + c * t := by
  set c' := (f' v + c) / 2
  have hc'_gt_c : c' > c := by simp only [c']; linarith
  have hc'_lt_fv : f' v > c' := by simp only [c']; linarith
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    deriv_implies_local_growth hf hz hv hc'_lt_fv
  exact ⟨δ, hδ_pos, fun t ht_pos ht_lt => by
    have h := hδ_bound t ht_pos ht_lt
    linarith [mul_lt_mul_of_pos_right hc'_gt_c ht_pos]⟩

/-! ## 3. Gradient norm implies steep region is nonempty -/

/--
**The full gradient chain.**

If `f` has Fréchet derivative `f'` at boundary point `z` with
`‖f'‖ > ℓ(K+1)`, then the steep region `{x | f(x) > τ + ℓ(K+1)·dist(x, z)}`
is nonempty.

This closes the gap between "gradient norm exceeds threshold" and
the hypothesis of `persistent_unsafe_refined`.
-/
theorem gradient_norm_implies_steep_nonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {z : E}
    (hf : HasFDerivAt f f' z)
    {τ : ℝ} (hz : f z = τ)
    {ℓ : ℝ} (hℓ : ℓ ≥ 0)
    {K : ℝ≥0}
    (hG : ℓ * (↑K + 1) < ‖f'‖) :
    ∃ x₀ : E, f x₀ > τ + ℓ * ((↑K + 1) * dist x₀ z) := by
  have hc_nonneg : ℓ * (↑K + 1) ≥ 0 := by positivity
  obtain ⟨v, hv_norm, hv_val⟩ := near_optimal_direction f' hc_nonneg hG
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    deriv_implies_strict_local_growth hf hz hv_norm hv_val
  have ht_pos : (0 : ℝ) < δ / 2 := by linarith
  have ht_lt : δ / 2 < δ := by linarith
  have h_growth := hδ_bound (δ / 2) ht_pos ht_lt
  have h_dist : dist (z + (δ / 2) • v) z = δ / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv_norm, mul_one,
        Real.norm_of_nonneg (le_of_lt ht_pos)]
  exact ⟨z + (δ / 2) • v, by rw [h_dist]; linarith⟩

/-! ## 4. The complete chain: gradient → persistence -/

/--
**Gradient Chain → Persistent Unsafe Region.**

The complete formalized chain:

  ‖f'(z)‖ > ℓ(K+1)
  → ∃ unit v with f'(v) > ℓ(K+1)       [near_optimal_direction]
  → ∃ δ, f(z+tv) > τ + ℓ(K+1)·t        [deriv_implies_strict_local_growth]
  → steep region nonempty                 [gradient_norm_implies_steep_nonempty]
  → positive-measure set stays unsafe     [persistent_unsafe_refined]

This closes Gaps 1 and 4 from the paper–code audit: the derivative-to-growth
link and the end-to-end chain from gradient norm to persistent unsafe region.
-/
theorem gradient_chain_persistent_unsafe
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : MeasureTheory.Measure E} [μ.IsOpenPosMeasure]
    {f : E → ℝ} {D : E → E}
    {z : E} {f' : E →L[ℝ] ℝ}
    (hf_deriv : HasFDerivAt f f' z)
    (hf_cont : Continuous f)
    {K : ℝ≥0} (hD : LipschitzWith K D)
    {τ : ℝ} (hz : f z = τ) (hz_fix : D z = z)
    {ℓ : ℝ} (hℓ : ℓ ≥ 0)
    (h_local : ∀ x, |f (D x) - f x| ≤ ℓ * dist (D x) x)
    (hG : ℓ * (↑K + 1) < ‖f'‖) :
    0 < μ {x : E | f (D x) > τ} := by
  obtain ⟨x₀, hx₀⟩ := gradient_norm_implies_steep_nonempty hf_deriv hz hℓ hG
  exact Refined.persistent_unsafe_refined hℓ hD hf_cont h_local hz_fix ⟨x₀, hx₀⟩

end MoF.GradientChain

end
