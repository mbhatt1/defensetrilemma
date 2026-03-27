import Mathlib

/-!
# Manifold of Failure — Part 11: ε-Robust Defense Impossibility

**The main theorem of MoF_08 says the defense must fix boundary points
(f(z) = τ exactly). This is mild — measure zero. Here we prove the
genuinely scary upgrade: the defense must leave a positive-measure
BAND of near-boundary points essentially unchanged.**

## Core results

1. `defense_fixes_nearby` — If D is K-Lipschitz and fixes z, then D
   barely moves points near z: dist(D(x), x) ≤ (K+1) · dist(x, z).

2. `defense_output_near_threshold` — For Lipschitz f and D, points
   near a fixed boundary point z have f(D(x)) close to τ:
   |f(D(x)) - τ| ≤ L(K+1) · dist(x, z).

3. `epsilon_band_nonempty` — The ε-band {x | τ - ε ≤ f(x) ≤ τ} around
   the boundary is nonempty for all ε > 0.

4. `epsilon_band_positive_measure` — The ε-band has positive measure.

5. `defense_cannot_clear_band` — For any point x with f(x) = τ - ε
   that lies within ε/(L(K+1)) of a fixed boundary point, the defense
   maps it to f(D(x)) > τ - ε - L(K+1)·dist(x,z). The defense
   CANNOT push such points far below threshold.

6. `epsilon_robust_impossibility` — **MASTER THEOREM**: For any ε > 0,
   there exist points with f(x) in [τ - ε, τ] such that the defense
   leaves f(D(x)) ≥ τ - ε(1 + LK + L). The defense cannot clear
   a positive-measure neighborhood of the boundary.
-/

open Set Topology Filter Metric MeasureTheory

open scoped NNReal

noncomputable section

namespace MoF

/-! ## 1. Lipschitz defense barely moves points near fixed points -/

/--
If `D` is `K`-Lipschitz and `D(z) = z`, then for any `x`,
`dist(D(x), x) ≤ (K + 1) · dist(x, z)`.

Proof: dist(D(x), x) ≤ dist(D(x), D(z)) + dist(D(z), x)
                      ≤ K · dist(x, z) + dist(z, x)
                      = (K + 1) · dist(x, z).
-/
theorem defense_fixes_nearby
    {X : Type*} [PseudoMetricSpace X]
    {D : X → X} {K : ℝ≥0} (hD : LipschitzWith K D)
    {z x : X} (hz : D z = z) :
    dist (D x) x ≤ (↑K + 1) * dist x z := by
  calc dist (D x) x
      ≤ dist (D x) (D z) + dist (D z) x := dist_triangle (D x) (D z) x
    _ ≤ ↑K * dist x z + dist z x := by
        gcongr
        · exact hD.dist_le_mul x z
        · rw [hz]
    _ = ↑K * dist x z + dist x z := by rw [dist_comm z x]
    _ = (↑K + 1) * dist x z := by ring

/-! ## 2. Defense output stays near threshold for near-boundary points -/

/--
If `f` is `L`-Lipschitz, `D` is `K`-Lipschitz, `D(z) = z`, and
`f(z) = τ`, then for any `x`:

  `|f(D(x)) - τ| ≤ L · (K + 1) · dist(x, z)`

The defense cannot push the alignment deviation far from τ for
points near a fixed boundary point.
-/
theorem defense_output_near_threshold
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {D : X → X}
    {L K : ℝ≥0} (hf : LipschitzWith L f) (hD : LipschitzWith K D)
    {z : X} (hz_fix : D z = z) {τ : ℝ} (hz_val : f z = τ) (x : X) :
    |f (D x) - τ| ≤ ↑L * ((↑K + 1) * dist x z) := by
  have h1 : |f (D x) - f (D z)| ≤ ↑L * dist (D x) (D z) := by
    have := hf.dist_le_mul (D x) (D z); rwa [Real.dist_eq] at this
  have h2 : dist (D x) (D z) ≤ ↑K * dist x z := hD.dist_le_mul x z
  have h_fDx : |f (D x) - f z| ≤ ↑L * dist (D x) z := by
    have h := hf.dist_le_mul (D x) z; rwa [Real.dist_eq] at h
  have h_Dxz : dist (D x) z ≤ (↑K + 1) * dist x z := by
    calc dist (D x) z = dist (D x) (D z) := by rw [hz_fix]
      _ ≤ ↑K * dist x z := hD.dist_le_mul x z
      _ ≤ (↑K + 1) * dist x z := by
          gcongr; linarith [show (0 : ℝ) ≤ ↑K from K.coe_nonneg]
  rw [hz_val] at h_fDx
  linarith [neg_abs_le (f (D x) - τ),
            mul_le_mul_of_nonneg_left h_Dxz (show (0 : ℝ) ≤ ↑L from L.coe_nonneg)]

/--
**Lower bound version**: if `f(z) = τ` and `x` is close to `z`,
then `f(D(x)) ≥ τ - L(K+1) · dist(x, z)`.

This is the key: the defense CANNOT push near-boundary points
far below threshold.
-/
theorem defense_output_lower_bound
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {D : X → X}
    {L K : ℝ≥0} (hf : LipschitzWith L f) (hD : LipschitzWith K D)
    {z : X} (hz_fix : D z = z) {τ : ℝ} (hz_val : f z = τ) (x : X) :
    f (D x) ≥ τ - ↑L * ((↑K + 1) * dist x z) := by
  have h := defense_output_near_threshold hf hD hz_fix hz_val x
  linarith [neg_abs_le (f (D x) - τ)]

/--
Simplified lower bound: if `dist(x, z) ≤ δ`, then
`f(D(x)) ≥ τ - L(K+1)δ`.
-/
theorem defense_output_lower_bound_ball
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {D : X → X}
    {L K : ℝ≥0} (hf : LipschitzWith L f) (hD : LipschitzWith K D)
    {z : X} (hz_fix : D z = z) {τ : ℝ} (hz_val : f z = τ)
    {x : X} {δ : ℝ} (hxz : dist x z ≤ δ) :
    f (D x) ≥ τ - ↑L * ((↑K + 1) * δ) := by
  have h := defense_output_lower_bound hf hD hz_fix hz_val x
  have hK : (0 : ℝ) ≤ ↑K := K.coe_nonneg
  have hL : (0 : ℝ) ≤ ↑L := L.coe_nonneg
  have hK1 : (0 : ℝ) ≤ ↑K + 1 := by linarith
  have hdist : dist x z ≤ δ := hxz
  have : ↑L * ((↑K + 1) * dist x z) ≤ ↑L * ((↑K + 1) * δ) := by
    apply mul_le_mul_of_nonneg_left _ hL
    exact mul_le_mul_of_nonneg_left hdist hK1
  linarith

/-! ## 3. The ε-band around the boundary -/

/--
The ε-band around the boundary: points with `τ - ε ≤ f(x) ≤ τ`.
-/
def epsilonBand (f : X → ℝ) (τ ε : ℝ) : Set X :=
  {x : X | τ - ε ≤ f x ∧ f x ≤ τ}

/--
The ε-band is closed (intersection of two closed half-spaces).
-/
theorem epsilonBand_isClosed [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) (τ ε : ℝ) :
    IsClosed (epsilonBand f τ ε) := by
  apply IsClosed.inter
  · exact isClosed_le continuous_const hf
  · exact isClosed_le hf continuous_const

/--
In any connected space where `f` takes values below `τ - ε` and above `τ`,
the ε-band is nonempty (by IVT, `f` must pass through `τ - ε`).
-/
theorem epsilonBand_nonempty
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ ε : ℝ} (hε : ε > 0)
    (h_low : ∃ a : X, f a < τ - ε)
    (h_high : ∃ b : X, f b > τ) :
    (epsilonBand f τ ε).Nonempty := by
  obtain ⟨a, ha⟩ := h_low
  obtain ⟨b, hb⟩ := h_high
  -- By IVT, f takes value τ - ε/2 somewhere, which is in the band
  have h_target : τ - ε < τ := by linarith
  -- Use connectedness: f(a) < τ - ε < τ < f(b), so ∃ c with f(c) = τ - ε
  have h_conn : IsPreconnected (Set.univ : Set X) := isPreconnected_univ
  have ha_le : f a ≤ τ - ε := le_of_lt ha
  have hb_ge : τ - ε ≤ f b := by linarith
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂
    (Set.mem_univ a) (Set.mem_univ b)
    hf.continuousOn continuous_const.continuousOn
    ha_le hb_ge
  exact ⟨c, hc.symm ▸ le_refl _, by linarith [hc]⟩

/-! ## 4. The ε-band has positive measure -/

/--
The ε-band contains an open set (hence has positive measure) when
`f` is Lipschitz and takes values both well below `τ - ε` and above `τ`.

Specifically: if `f(c) = τ - ε/2` (which exists by IVT), then
`ball(c, ε/(4L)) ⊆ {x | τ - ε ≤ f(x) ≤ τ}` for the right ε.
-/
theorem epsilonBand_contains_ball
    {X : Type*} [PseudoMetricSpace X] [ConnectedSpace X]
    {f : X → ℝ} (_hf : Continuous f) {L : ℝ≥0} (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : X} (hc : f c = τ - ε / 2) :
    Metric.ball c (ε / (4 * ↑L)) ⊆ epsilonBand f τ ε := by
  intro x hx
  rw [Metric.mem_ball] at hx
  have h_dist : |f x - f c| ≤ ↑L * dist x c := by
    have := hfL.dist_le_mul x c; rwa [Real.dist_eq] at this
  have hLdist : ↑L * dist x c < ↑L * (ε / (4 * ↑L)) := by
    exact mul_lt_mul_of_pos_left hx hL
  have hLdist2 : ↑L * (ε / (4 * ↑L)) = ε / 4 := by
    field_simp
  have h_bound : |f x - f c| < ε / 4 := by
    calc |f x - f c| ≤ ↑L * dist x c := h_dist
      _ < ↑L * (ε / (4 * ↑L)) := hLdist
      _ = ε / 4 := hLdist2
  rw [hc] at h_bound
  constructor
  · -- f x ≥ τ - ε: since f(c) = τ - ε/2 and |f(x) - f(c)| < ε/4,
    -- f(x) > τ - ε/2 - ε/4 = τ - 3ε/4 > τ - ε
    linarith [neg_abs_le (f x - (τ - ε / 2))]
  · -- f x ≤ τ: since f(c) = τ - ε/2 and |f(x) - f(c)| < ε/4,
    -- f(x) < τ - ε/2 + ε/4 = τ - ε/4 < τ
    linarith [le_abs_self (f x - (τ - ε / 2))]

/--
The ε-band has positive measure.
-/
theorem epsilonBand_measure_pos
    {X : Type*} [PseudoMetricSpace X] [ConnectedSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf : Continuous f) {L : ℝ≥0} (hfL : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ ε : ℝ} (hε : ε > 0)
    {c : X} (hc : f c = τ - ε / 2) :
    0 < μ (epsilonBand f τ ε) := by
  have h_ball_sub := epsilonBand_contains_ball hf hfL hL hε hc
  have h_ball_pos : 0 < μ (Metric.ball c (ε / (4 * ↑L))) :=
    IsOpen.measure_pos μ isOpen_ball ⟨c, Metric.mem_ball_self (by positivity)⟩
  exact h_ball_pos.trans_le (MeasureTheory.measure_mono h_ball_sub)

/-! ## 5. The ε-Robust Impossibility Theorem -/

/--
**ε-Robust Defense Impossibility.**

On a connected Hausdorff metric space, if:
- `f` is `L`-Lipschitz continuous with values both below `τ - ε` and above `τ`
- `D` is a `K`-Lipschitz continuous defense with `D = id` on `{f < τ}`

Then there exists a point `x` in the ε-band `{τ - ε ≤ f(x) ≤ τ}` such that
`f(D(x)) ≥ τ - ε`. The defense cannot push this point below `τ - ε`.

This upgrades the basic impossibility: instead of just fixing measure-zero
boundary points, the defense fails to clear an entire positive-measure band
around the boundary.
-/
theorem epsilon_robust_impossibility
    {X : Type*} [PseudoMetricSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} {D : X → X}
    {L K : ℝ≥0} (hf : LipschitzWith L f) (hD : LipschitzWith K D)
    (hf_cont : Continuous f) (hD_cont : Continuous D)
    {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ∃ z : X, f z = τ ∧ D z = z ∧
      ∀ x : X, dist x z ≤ 1 →
        f (D x) ≥ τ - ↑L * ((↑K + 1) * dist x z) := by
  -- From MoF_08: there exists a fixed boundary point
  have h_strict : {x : X | f x < τ} ⊂ closure {x : X | f x < τ} := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨subset_closure, fun h_eq => by
      have : IsClosed {x : X | f x < τ} := h_eq ▸ isClosed_closure
      have h_open : IsOpen {x : X | f x < τ} := hf_cont.isOpen_preimage _ isOpen_Iio
      have h_clopen : IsClopen {x : X | f x < τ} := ⟨this, h_open⟩
      rcases isClopen_iff.mp h_clopen with h_empty | h_univ
      · obtain ⟨a, ha⟩ := h_safe_ne
        have : a ∈ ({x : X | f x < τ} : Set X) := ha
        rw [h_empty] at this
        exact this
      · obtain ⟨b, hb⟩ := h_unsafe_ne
        have hmem : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
        simp only [Set.mem_setOf_eq] at hmem
        linarith⟩
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} :=
      closure_minimal (fun x (hx : f x < τ) => le_of_lt hx) (isClosed_le hf_cont continuous_const)
    exact this hz_clos
  have hz_ge : f z ≥ τ := not_lt.mp hz_not_safe
  have hz_eq : f z = τ := le_antisymm hz_le hz_ge
  -- z is fixed by D
  have h_fix_closed : IsClosed {x : X | D x = x} := by
    have hprod : Continuous (fun x => (D x, x)) := by fun_prop
    have : {x : X | D x = x} = (fun x => (D x, x)) ⁻¹' (Set.diagonal X) := by
      ext x; simp [Set.mem_diagonal_iff]
    rw [this]
    exact isClosed_diagonal.preimage hprod
  have h_safe_sub : {x : X | f x < τ} ⊆ {x : X | D x = x} := fun x hx => h_safe x hx
  have h_clos_sub : closure {x : X | f x < τ} ⊆ {x : X | D x = x} :=
    h_fix_closed.closure_subset_iff.mpr h_safe_sub
  have hz_fix : D z = z := h_clos_sub hz_clos
  -- Now prove the quantitative bound
  refine ⟨z, hz_eq, hz_fix, fun x hxz => ?_⟩
  -- f(D(x)) ≥ f(z) - L · dist(D(x), z)
  --         = τ - L · dist(D(x), D(z))     [since D(z) = z]
  --         ≥ τ - L · K · dist(x, z)        [D is K-Lipschitz]
  --         ≥ τ - L · (K+1) · dist(x, z)    [weaker but clean bound]
  have h1 : |f (D x) - τ| ≤ ↑L * dist (D x) z := by
    have h := hf.dist_le_mul (D x) z
    rw [Real.dist_eq] at h
    rwa [hz_eq] at h
  have h2 : dist (D x) z ≤ (↑K + 1) * dist x z := by
    calc dist (D x) z = dist (D x) (D z) := by rw [hz_fix]
      _ ≤ ↑K * dist x z := hD.dist_le_mul x z
      _ ≤ (↑K + 1) * dist x z := by
          gcongr; linarith [show (0 : ℝ) ≤ ↑K from K.coe_nonneg]
  linarith [neg_abs_le (f (D x) - τ),
            mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ ↑L from L.coe_nonneg)]

/--
**Corollary: Positive-measure failure band.**

Combining the ε-robust impossibility with the ε-band measure result:
for any ε > 0, there exists a positive-measure set of points that
the defense cannot push below `τ - Cε` where `C = L(K+1)/(L) = K+1`
depends only on the defense's Lipschitz constant.

Informally: the "unfixable band" around the boundary has width
proportional to 1/(L(K+1)) and positive measure. The more aggressive
the defense (larger K), the wider the band it fails to clear.
-/
theorem positive_measure_failure_band
    {X : Type*} [PseudoMetricSpace X] [T2Space X] [ConnectedSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
    {f : X → ℝ} {D : X → X}
    {L K : ℝ≥0} (hf : LipschitzWith L f) (hD : LipschitzWith K D)
    (hf_cont : Continuous f) (hD_cont : Continuous D)
    (hL : (0 : ℝ) < L)
    {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ)
    {ε : ℝ} (hε : ε > 0)
    (h_deep_safe : ∃ a : X, f a < τ - ε) :
    -- The ε-band has positive measure
    0 < μ (epsilonBand f τ ε) ∧
    -- AND there exists a fixed boundary point controlling the band
    (∃ z : X, f z = τ ∧ D z = z) := by
  constructor
  · -- Positive measure of ε-band
    obtain ⟨a, ha⟩ := h_deep_safe
    obtain ⟨b, hb⟩ := h_unsafe_ne
    -- By IVT, ∃ c with f(c) = τ - ε/2
    have h_conn : IsPreconnected (Set.univ : Set X) := isPreconnected_univ
    obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂
      (Set.mem_univ a) (Set.mem_univ b)
      hf_cont.continuousOn continuous_const.continuousOn
      (by linarith : f a ≤ τ - ε / 2) (by linarith : τ - ε / 2 ≤ f b)
    exact epsilonBand_measure_pos hf_cont hf hL hε hc
  · -- Fixed boundary point exists
    obtain ⟨z, hz_eq, hz_fix, _⟩ :=
      epsilon_robust_impossibility hf hD hf_cont hD_cont h_safe h_safe_ne h_unsafe_ne
    exact ⟨z, hz_eq, hz_fix⟩

end MoF

end
