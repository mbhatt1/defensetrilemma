import Mathlib
import HallucinationProofs.HoF_14_QuantitativeGeometry

/-!
# Hallucination Trilemma — Part 15: Nonlinear Boundaries

A first-order theory of nonlinear probe boundaries. The linear results
of Part 14 say a nonzero linear probe's boundary is a codimension-one
affine hyperplane. Here the probe is any function differentiable at a
boundary point with nonzero derivative (a regular point), and three
results transfer the picture to first order.

1. `regular_point_is_crossing` — every neighborhood of a regular
   boundary point contains strictly true and strictly false points, so
   regular points generate local coverage and the boundary is locally
   thin.
2. `nonlinear_boundary_tangent` — boundary points near a regular point
   deviate from the tangent hyperplane sublinearly: for every `ε > 0`
   there is `δ > 0` with `|L (x - x₀)| ≤ ε * ‖x - x₀‖` for boundary
   `x` within `δ`.
3. `tangent_hyperplane_dim` — the tangent kernel has dimension `d - 1`,
   by Part 14's rank-nullity result.

All proofs are sorry-free.
-/

open Filter Asymptotics

noncomputable section

namespace HoF

/-- Derivative of the affine line `t ↦ x₀ + t • v` at `0`. -/
private theorem hasDerivAt_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ v : E) : HasDerivAt (fun t : ℝ => x₀ + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x₀

/-- Sign behavior of a function along a direction of strictly positive
directional derivative, through a zero. -/
private theorem sign_along_direction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x₀ : E) (L : E →L[ℝ] ℝ)
    (hf : HasFDerivAt f L x₀) (h0 : f x₀ = 0)
    (v : E) (hv : 0 < L v) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → t ≠ 0 →
      (0 < t → 0 < f (x₀ + t • v)) ∧ (t < 0 → f (x₀ + t • v) < 0) := by
  have hg : HasDerivAt (fun t : ℝ => f (x₀ + t • v)) (L v) 0 := by
    have h1 := hasDerivAt_line x₀ v
    have h2 : HasFDerivAt f L ((fun t : ℝ => x₀ + t • v) 0) := by
      simpa using hf
    simpa using h2.comp_hasDerivAt 0 h1
  have hlo := hasDerivAt_iff_isLittleO.mp hg
  have hbound := hlo.bound (half_pos hv)
  rw [Metric.eventually_nhds_iff] at hbound
  obtain ⟨δ, hδ, hb⟩ := hbound
  refine ⟨δ, hδ, fun t ht _htne => ?_⟩
  have hdist : dist t 0 < δ := by simpa [Real.dist_eq] using ht
  have hthis := hb hdist
  simp only [zero_smul, add_zero, h0, sub_zero, smul_eq_mul,
    Real.norm_eq_abs] at hthis
  have habs := abs_le.mp hthis
  constructor
  · intro htpos
    rw [abs_of_pos htpos] at habs
    nlinarith [habs.1, mul_pos htpos hv]
  · intro htneg
    rw [abs_of_neg htneg] at habs
    nlinarith [habs.2, mul_pos (neg_pos.mpr htneg) hv]

/--
**Regular boundary points are genuine crossings.**

If `f` is differentiable at `x₀` with nonzero derivative and
`f x₀ = 0`, then every metric neighborhood of `x₀` contains a point
where `f` is strictly positive and a point where `f` is strictly
negative. Regular points of the truth boundary therefore generate
local coverage, and the boundary is locally thin.
-/
theorem regular_point_is_crossing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x₀ : E) (L : E →L[ℝ] ℝ)
    (hf : HasFDerivAt f L x₀) (h0 : f x₀ = 0) (hL : L ≠ 0) :
    ∀ ε > 0, (∃ x, ‖x - x₀‖ < ε ∧ 0 < f x) ∧
             (∃ x, ‖x - x₀‖ < ε ∧ f x < 0) := by
  obtain ⟨u, hu⟩ : ∃ u, L u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hL (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ : ∃ v, 0 < L v := by
    rcases lt_or_gt_of_ne hu with h | h
    · exact ⟨-u, by simp only [map_neg]; exact neg_pos.mpr h⟩
    · exact ⟨u, h⟩
  obtain ⟨δ, hδ, hsign⟩ := sign_along_direction f x₀ L hf h0 v hv
  intro ε hε
  set t : ℝ := min (δ / 2) (ε / (2 * (‖v‖ + 1))) with htdef
  have hvpos : (0 : ℝ) < ‖v‖ + 1 := by positivity
  have htpos : 0 < t := by
    apply lt_min (half_pos hδ)
    positivity
  have htδ : |t| < δ := by
    rw [abs_of_pos htpos]
    calc t ≤ δ / 2 := min_le_left _ _
    _ < δ := half_lt_self hδ
  have htε : t * ‖v‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖v‖ + 1)) := min_le_right _ _
    have h2 : t * ‖v‖ ≤ ε / (2 * (‖v‖ + 1)) * ‖v‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
    have h3 : ε / (2 * (‖v‖ + 1)) * ‖v‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    linarith
  have hnorm : ∀ s : ℝ, ‖(x₀ + s • v) - x₀‖ = |s| * ‖v‖ := by
    intro s
    simp [norm_smul]
  constructor
  · refine ⟨x₀ + t • v, ?_, ?_⟩
    · rw [hnorm, abs_of_pos htpos]; exact htε
    · exact (hsign t htδ (ne_of_gt htpos)).1 htpos
  · refine ⟨x₀ + (-t) • v, ?_, ?_⟩
    · rw [hnorm, abs_neg, abs_of_pos htpos]; exact htε
    · exact (hsign (-t) (by rwa [abs_neg]) (by simpa using ne_of_gt htpos)).2
        (neg_lt_zero.mpr htpos)

/--
**Boundary points hug the tangent hyperplane.**

If `f` is differentiable at a boundary point `x₀` with derivative `L`,
then boundary points near `x₀` satisfy the tangent constraint to first
order: for every `ε > 0` there is `δ > 0` such that any boundary point
`x` within `δ` of `x₀` has `|L (x - x₀)| ≤ ε * ‖x - x₀‖`. The nonlinear
truth boundary deviates from the affine tangent hyperplane
`x₀ + ker L` sublinearly.
-/
theorem nonlinear_boundary_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x₀ : E) (L : E →L[ℝ] ℝ)
    (hf : HasFDerivAt f L x₀) (h0 : f x₀ = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x - x₀‖ < δ → f x = 0 →
      |L (x - x₀)| ≤ ε * ‖x - x₀‖ := by
  intro ε hε
  have hlo := hf.isLittleO
  have hbound := hlo.bound hε
  rw [Metric.eventually_nhds_iff] at hbound
  obtain ⟨δ, hδ, hb⟩ := hbound
  refine ⟨δ, hδ, fun x hx hfx => ?_⟩
  have hdist : dist x x₀ < δ := by
    simpa [dist_eq_norm] using hx
  have hthis := hb hdist
  simp only [hfx, h0, sub_zero, zero_sub, norm_neg,
    Real.norm_eq_abs] at hthis
  exact hthis

/--
**The tangent hyperplane has codimension one.**

A nonzero derivative's kernel has dimension `d - 1`, by the
rank-nullity result of Part 14. Together with the two theorems above,
the truth boundary of a differentiable probe is, at every regular
point, a genuine sign crossing pressed against a codimension-one
affine hyperplane.
-/
theorem tangent_hyperplane_dim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (L : E →ₗ[ℝ] ℝ)) =
      Module.finrank ℝ E - 1 := by
  apply linear_probe_boundary_dim
  intro h
  apply hL
  ext x
  exact congrFun (congrArg DFunLike.coe h) x

/-! ## Axiom audit -/

#print axioms regular_point_is_crossing
#print axioms nonlinear_boundary_tangent
#print axioms tangent_hyperplane_dim

end HoF

end
