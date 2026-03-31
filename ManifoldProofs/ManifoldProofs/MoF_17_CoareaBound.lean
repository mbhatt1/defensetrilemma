import Mathlib

/-!
# Manifold of Failure — Part 17: Coarea-Style Volume Lower Bound

**Quantitative lower bound on the ε-band volume via Lipschitz
ball containment.**

## Strategy

The full coarea formula may not be available in Mathlib, so we use a
self-contained Lipschitz ball-containment argument:

1. If `f` is `L`-Lipschitz and `f(c) = τ - ε/2`, then
   `ball(c, ε/(4L)) ⊆ {x | τ - ε ≤ f(x) ≤ τ}` (the ε-band).
2. Therefore `μ(ε-band) ≥ μ(ball(c, ε/(4L)))`.
3. In ℝ^n the ball has positive and computable volume.

## Main results

- `lipschitz_ball_subset_band` — ball containment in the ε-band
- `epsilon_band_volume_lower_bound` — μ(ε-band) ≥ μ(ball(c, ε/(4L)))
- `epsilon_band_volume_lower_bound_euclidean` — specialised to ℝ^n with
  Lebesgue measure, giving a concrete positive lower bound
- `epsilon_band_volume_lower_bound_real` — explicit formula in ℝ:
  μ(ε-band) ≥ ε/(2L)
-/

open Set Topology Filter Metric MeasureTheory

open scoped NNReal

noncomputable section

namespace MoF

/-! ## 1. The ε-band (re-stated for self-containedness) -/

/-- The ε-band around the decision boundary: `{x | τ - ε ≤ f(x) ≤ τ}`. -/
def coareaBand {X : Type*} (f : X → ℝ) (τ ε : ℝ) : Set X :=
  {x : X | τ - ε ≤ f x ∧ f x ≤ τ}

/-! ## 2. Lipschitz ball containment -/

/--
If `f` is `L`-Lipschitz with `L > 0`, and `f(c) = τ - ε/2`, then every
point in `ball(c, ε/(4L))` has `f`-value in `[τ - 3ε/4, τ - ε/4]`,
which is contained in `[τ - ε, τ]`.

Proof sketch: For `x ∈ ball(c, r)` with `r = ε/(4L)`,
  `|f(x) - f(c)| ≤ L · dist(x, c) < L · ε/(4L) = ε/4`.
So `f(x) ∈ (τ - ε/2 - ε/4, τ - ε/2 + ε/4) = (τ - 3ε/4, τ - ε/4)`.
Both endpoints lie strictly within `[τ - ε, τ]`.
-/
theorem lipschitz_ball_subset_band
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : X} (hc : f c = τ - ε / 2) :
    Metric.ball c (ε / (4 * ↑L)) ⊆ coareaBand f τ ε := by
  intro x hx
  rw [Metric.mem_ball] at hx
  have h_dist : |f x - f c| ≤ ↑L * dist x c := by
    have := hfL.dist_le_mul x c; rwa [Real.dist_eq] at this
  have hLdist : ↑L * dist x c < ↑L * (ε / (4 * ↑L)) :=
    mul_lt_mul_of_pos_left hx hL
  have hLdist2 : ↑L * (ε / (4 * ↑L)) = ε / 4 := by field_simp
  have h_bound : |f x - f c| < ε / 4 := by
    calc |f x - f c| ≤ ↑L * dist x c := h_dist
      _ < ↑L * (ε / (4 * ↑L)) := hLdist
      _ = ε / 4 := hLdist2
  rw [hc] at h_bound
  constructor
  · -- f x ≥ τ - ε
    linarith [neg_abs_le (f x - (τ - ε / 2))]
  · -- f x ≤ τ
    linarith [le_abs_self (f x - (τ - ε / 2))]

/-! ## 3. Volume lower bound: general metric measure space -/

/--
**ε-band volume lower bound (general).**

If `f` is `L`-Lipschitz with `L > 0`, `ε > 0`, and there exists a
centre point `c` with `f(c) = τ - ε/2`, then

  `μ(coareaBand f τ ε) ≥ μ(ball(c, ε/(4L)))`.

This is a quantitative upgrade of `epsilonBand_measure_pos` from MoF_11:
instead of just *positive* measure, we get a *computable* lower bound
in terms of the ball volume.
-/
theorem epsilon_band_volume_lower_bound
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} {L : ℝ≥0} (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : X} (hc : f c = τ - ε / 2) :
    μ (Metric.ball c (ε / (4 * ↑L))) ≤ μ (coareaBand f τ ε) :=
  measure_mono (lipschitz_ball_subset_band hfL hL hε hc)

/--
**Positive measure corollary.**

Under the same hypotheses, the ε-band has strictly positive measure
in any measure that gives positive measure to open balls.
-/
theorem epsilon_band_volume_pos
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℝ} {L : ℝ≥0} (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : X} (hc : f c = τ - ε / 2) :
    0 < μ (coareaBand f τ ε) := by
  have h_ball_pos : 0 < μ (Metric.ball c (ε / (4 * ↑L))) :=
    Metric.isOpen_ball.measure_pos μ ⟨c, Metric.mem_ball_self (by positivity)⟩
  exact lt_of_lt_of_le h_ball_pos (epsilon_band_volume_lower_bound μ hfL hL hε hc)

/-! ## 4. Euclidean space specialisation -/

/--
**ε-band volume lower bound in Euclidean space.**

In `EuclideanSpace ℝ (Fin n)` with Lebesgue measure, the ε-band
has measure at least `volume(ball(c, ε/(4L)))`, which is a positive
quantity depending on the dimension `n`, `ε`, and `L`.
-/
theorem epsilon_band_volume_lower_bound_euclidean
    {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : EuclideanSpace ℝ (Fin n)} (hc : f c = τ - ε / 2) :
    volume (Metric.ball c (ε / (4 * ↑L))) ≤ volume (coareaBand f τ ε) :=
  epsilon_band_volume_lower_bound volume hfL hL hε hc

/--
In Euclidean space, the ε-band has strictly positive Lebesgue measure.
-/
theorem epsilon_band_volume_pos_euclidean
    {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : EuclideanSpace ℝ (Fin n)} (hc : f c = τ - ε / 2) :
    0 < volume (coareaBand f τ ε) :=
  epsilon_band_volume_pos volume hfL hL hε hc

/-! ## 5. Explicit formula in ℝ -/

/--
**ε-band volume lower bound in ℝ.**

For a Lipschitz function `f : ℝ → ℝ` with Lipschitz constant `L > 0`,
the ε-band has Lebesgue measure at least `ε / (2L)`.

Proof: `ball(c, ε/(4L))` has measure `2 · ε/(4L) = ε/(2L)`.
-/
theorem epsilon_band_volume_lower_bound_real
    {f : ℝ → ℝ} {L : ℝ≥0}
    (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : ℝ} (hc : f c = τ - ε / 2) :
    ENNReal.ofReal (ε / (2 * ↑L)) ≤ volume (coareaBand f τ ε) := by
  have h_band := epsilon_band_volume_lower_bound volume hfL hL hε hc
  have h_ball_vol : volume (Metric.ball c (ε / (4 * ↑L))) =
      ENNReal.ofReal (2 * (ε / (4 * ↑L))) := Real.volume_ball c (ε / (4 * ↑L))
  have h_simplify : 2 * (ε / (4 * ↑L)) = ε / (2 * ↑L) := by
    field_simp; ring
  rw [h_ball_vol, h_simplify] at h_band
  exact h_band

/-! ## 6. Midpoint existence via IVT -/

/--
In a connected space, if `f` is continuous and takes values both below
`τ - ε` and above `τ`, then there exists a midpoint `c` with
`f(c) = τ - ε/2`. Combined with the ball-containment bound, this
gives an unconditional volume lower bound.
-/
theorem exists_midpoint_for_band
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f)
    {τ ε : ℝ} (hε : ε > 0)
    (h_low : ∃ a : X, f a < τ - ε)
    (h_high : ∃ b : X, f b > τ) :
    ∃ c : X, f c = τ - ε / 2 := by
  obtain ⟨a, ha⟩ := h_low
  obtain ⟨b, hb⟩ := h_high
  have h_conn : IsPreconnected (Set.univ : Set X) := isPreconnected_univ
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂
    (Set.mem_univ a) (Set.mem_univ b)
    hf.continuousOn continuous_const.continuousOn
    (by linarith : f a ≤ τ - ε / 2) (by linarith : τ - ε / 2 ≤ f b)
  exact ⟨c, hc⟩

/--
**Unconditional ε-band volume bound.**

In a connected space with a Lipschitz continuous function that takes
values both well below `τ - ε` and above `τ`, the ε-band has strictly
positive measure. Moreover, there exists a centre point `c` witnessing
the ball-containment lower bound.
-/
theorem epsilon_band_volume_pos_unconditional
    {X : Type*} [PseudoMetricSpace X] [ConnectedSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf : Continuous f) {L : ℝ≥0} (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    (h_low : ∃ a : X, f a < τ - ε)
    (h_high : ∃ b : X, f b > τ) :
    ∃ c : X, f c = τ - ε / 2 ∧
      μ (Metric.ball c (ε / (4 * ↑L))) ≤ μ (coareaBand f τ ε) ∧
      0 < μ (coareaBand f τ ε) := by
  obtain ⟨c, hc⟩ := exists_midpoint_for_band hf hε h_low h_high
  exact ⟨c, hc,
    epsilon_band_volume_lower_bound μ hfL hL hε hc,
    epsilon_band_volume_pos μ hfL hL hε hc⟩

/-! ## 7. Band radius scaling -/

/--
The ball radius `ε/(4L)` is positive when `ε > 0` and `L > 0`.
This is a helper for downstream results that need the radius positivity.
-/
theorem band_radius_pos {L : ℝ≥0} (hL : (0 : ℝ) < L) {ε : ℝ} (hε : ε > 0) :
    (0 : ℝ) < ε / (4 * ↑L) := by positivity

/--
The ball radius scales linearly with `ε` and inversely with `L`.
Doubling `ε` doubles the guaranteed ball radius; doubling the Lipschitz
constant halves it.
-/
theorem band_radius_scaling {L : ℝ≥0} (hL : (0 : ℝ) < L) {ε₁ ε₂ : ℝ}
    (_hε₁ : ε₁ > 0) (h : ε₁ ≤ ε₂) :
    ε₁ / (4 * ↑L) ≤ ε₂ / (4 * ↑L) := by
  apply div_le_div_of_nonneg_right h
  positivity

/--
**Monotonicity**: a wider ε-band has at least as much measure.
-/
theorem coareaBand_mono
    {X : Type*} {f : X → ℝ} {τ : ℝ} {ε₁ ε₂ : ℝ}
    (h : ε₁ ≤ ε₂) :
    coareaBand f τ ε₁ ⊆ coareaBand f τ ε₂ := by
  intro x ⟨hlo, hhi⟩
  exact ⟨by linarith, hhi⟩

theorem coareaBand_measure_mono
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} {τ : ℝ} {ε₁ ε₂ : ℝ}
    (h : ε₁ ≤ ε₂) :
    μ (coareaBand f τ ε₁) ≤ μ (coareaBand f τ ε₂) :=
  measure_mono (coareaBand_mono h)

end MoF

end
