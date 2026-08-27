import Mathlib

/-!
# Hallucination Trilemma — Part 14: Quantitative Geometry

Quantitative and structural geometry of the truth boundary.

1. `confidence_gap_width` — a Lipschitz confidence field cannot jump.
   The high-confidence region and the low-confidence region are at
   distance at least `2γ/L` from each other. The ambiguity corridor
   between them has a minimum width fixed by the Lipschitz constant.
2. `truth_margin_tube` — near a boundary point, a Lipschitz realized
   truth field has small margin. Within radius `r` of the forced
   point, the truth margin is at most `L_δ · r`.
3. `ambiguity_tube` — the two combined. Around the coupled point,
   every query within the corridor radius has truth margin bounded by
   the ratio of the two Lipschitz data.
4. `linear_probe_boundary_coset` — for a linear probe, the truth
   boundary is an affine translate of the probe's kernel.
5. `linear_probe_boundary_dim` — that kernel has dimension `d - 1`.
   For linear probes the truth boundary is literally a
   codimension-one affine hyperplane.

All proofs are sorry-free.
-/

open Set

noncomputable section

namespace HoF

/-! ## 1. Width of the ambiguity corridor -/

/--
**Confidence gap width.**

If confidence is `L`-Lipschitz, then any query with confidence at
least `τ + γ` and any query with confidence at most `τ - γ` are at
distance at least `2γ/L`. Decisive-above and decisive-below regions
cannot touch. The corridor between them has width at least `2γ/L`.
-/
theorem confidence_gap_width
    {Q : Type*} [PseudoMetricSpace Q]
    (conf : Q → ℝ) (L γ τ : ℝ) (hL : 0 < L)
    (hlip : ∀ x y, |conf x - conf y| ≤ L * dist x y)
    (x y : Q) (hx : conf x ≥ τ + γ) (hy : conf y ≤ τ - γ) :
    2 * γ / L ≤ dist x y := by
  have h1 : 2 * γ ≤ conf x - conf y := by linarith
  have h2 : conf x - conf y ≤ |conf x - conf y| := le_abs_self _
  have h3 : 2 * γ ≤ L * dist x y := le_trans (le_trans h1 h2) (hlip x y)
  rw [div_le_iff₀ hL]
  linarith [h3, mul_comm L (dist x y)]

/--
**Truth margin tube.**

If the realized truth field is `L_δ`-Lipschitz and vanishes at `x₀`,
then every query within distance `r` of `x₀` has truth margin at most
`L_δ · r`.
-/
theorem truth_margin_tube
    {Q : Type*} [PseudoMetricSpace Q]
    (dF : Q → ℝ) (Lδ : ℝ)
    (hlip : ∀ x y, |dF x - dF y| ≤ Lδ * dist x y)
    (x₀ : Q) (h0 : dF x₀ = 0) (x : Q) :
    |dF x| ≤ Lδ * dist x x₀ := by
  have h := hlip x x₀
  rw [h0, sub_zero] at h
  exact h

/--
**Ambiguity tube.**

Combine the two. Around a coupled point `x₀` (confidence `τ`, truth
margin `0`), every query within radius `r` has truth margin at most
`L_δ · r` and confidence within `L_c · r` of the threshold. The
forced ambiguity is not one pathological point. It is a tube whose
profile is controlled by the Lipschitz data.
-/
theorem ambiguity_tube
    {Q : Type*} [PseudoMetricSpace Q]
    (conf dF : Q → ℝ) (Lc Lδ τ r : ℝ)
    (hlipc : ∀ x y, |conf x - conf y| ≤ Lc * dist x y)
    (hlipd : ∀ x y, |dF x - dF y| ≤ Lδ * dist x y)
    (x₀ : Q) (hc0 : conf x₀ = τ) (hd0 : dF x₀ = 0)
    (x : Q) (hx : dist x x₀ ≤ r) (hLc : 0 ≤ Lc) (hLδ : 0 ≤ Lδ) :
    |dF x| ≤ Lδ * r ∧ |conf x - τ| ≤ Lc * r := by
  constructor
  · have h := truth_margin_tube dF Lδ hlipd x₀ hd0 x
    have : Lδ * dist x x₀ ≤ Lδ * r := mul_le_mul_of_nonneg_left hx hLδ
    linarith
  · have h := hlipc x x₀
    rw [hc0] at h
    have : Lc * dist x x₀ ≤ Lc * r := mul_le_mul_of_nonneg_left hx hLc
    linarith [h]

/-! ## 2. Linear probes have hyperplane boundaries -/

/--
**Linear probe boundary is an affine coset.**

For a linear probe `f` with offset `b`, a point lies on the probe's
truth boundary exactly when its displacement from any fixed boundary
point lies in the kernel of `f`. The boundary is an affine translate
of the kernel.
-/
theorem linear_probe_boundary_coset
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (x₀ : E) (hx₀ : f x₀ = b) (y : E) :
    f y = b ↔ y - x₀ ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker, map_sub, hx₀, sub_eq_zero]

/--
**Linear probe boundary has codimension one.**

A nonzero linear probe on a `d`-dimensional space has a kernel of
dimension `d - 1`. Together with the coset description, the truth
boundary of a linear probe is a codimension-one affine hyperplane.
This is the rank–nullity theorem.
-/
theorem linear_probe_boundary_dim
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ E - 1 := by
  have hrange : LinearMap.range f = ⊤ := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf (LinearMap.ext h)
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(y / f x) • x, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hrk : Module.finrank ℝ (LinearMap.range f) = 1 := by
    rw [hrange, finrank_top]
    exact Module.finrank_self ℝ
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  omega

/-! ## 3. Axiom audit -/

#print axioms confidence_gap_width
#print axioms truth_margin_tube
#print axioms ambiguity_tube
#print axioms linear_probe_boundary_coset
#print axioms linear_probe_boundary_dim

end HoF

end
