import Mathlib
import HallucinationProofs.HoF_07_TrilemmaCore
import HallucinationProofs.HoF_10_PureDiscrete

/-!
# Hallucination Trilemma — Part 11: Multi-Turn and Probabilistic Extensions

## A. Multi-Turn

The T-turn history space `Fin T → Q` is connected whenever `Q` is connected
(Mathlib: `instance [∀ i, ConnectedSpace (X i)] : ConnectedSpace (∀ i, X i)`).
Applying the trilemma to history-dependent models is therefore immediate.

## B. Probabilistic

Two results:
1. `stochastic_trilemma_expected` — expected-value form: apply the IVT
   argument directly to `cbar` and `dbar`.
2. `stochastic_dichotomy` — sample-level form: at the forced boundary point
   where `∫ d dμ = 0`, if sample faithfulness holds a.e. and there is positive
   probability of high confidence, then `μ{d > 0} > 0` (active hallucination).

All proofs are sorry-free.
-/

open MeasureTheory Set Filter

noncomputable section

namespace HoF

/-! ## A. Multi-Turn -/

/--
**Per-turn impossibility.** Each turn is independently trapped.
-/
theorem multi_turn_per_turn
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (T : ℕ)
    (M   : Fin T → Q → A × ℝ)
    (δ   : Fin T → Q × A → ℝ)
    (hM_ans  : ∀ t, Continuous (fun q => (M t q).1))
    (hM_conf : ∀ t, Continuous (fun q => (M t q).2))
    (hδ      : ∀ t, Continuous (δ t))
    (hF      : ∀ t, TrilemmaFaithful  (M t) (δ t))
    (hC      : ∀ t, TrilemmaCovering  (M t) (δ t))
    (hCal    : ∀ t, StrictCalibrated  (M t) (δ t))
    (t : Fin T) : False :=
  hallucination_trilemma (M t) (δ t)
    (hM_ans t) (hM_conf t) (hδ t) (hF t) (hC t) (hCal t)

/--
**History-dependent impossibility.**

`Fin T → Q` is connected because `Q` is, so the trilemma applies verbatim
to models that see the full conversation history.
-/
theorem multi_turn_history_dependent
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (T : ℕ)
    (M   : (Fin T → Q) → A × ℝ)
    (δ   : (Fin T → Q) × A → ℝ)
    (hM_ans  : Continuous (fun h => (M h).1))
    (hM_conf : Continuous (fun h => (M h).2))
    (hδ      : Continuous δ)
    (hF      : TrilemmaFaithful M δ)
    (hC      : TrilemmaCovering M δ)
    (hCal    : StrictCalibrated M δ) : False := by
  haveI : ConnectedSpace (Fin T → Q) := inferInstance  -- Mathlib: Pi of connected is connected
  exact hallucination_trilemma M δ hM_ans hM_conf hδ hF hC hCal

/--
**History-space embedding.**

Any t-turn history can be injectively embedded into a t'-turn history
(by padding with a fixed question). This is only a structural embedding of
history spaces; whether a particular model preserves the trilemma hypotheses
after padding is a separate model-specific assumption.
-/
theorem adversary_boundary_reachable
    {Q : Type*} (t t' : ℕ) (hle : t ≤ t') (q₀ : Q) :
    ∃ (embed : (Fin t → Q) → (Fin t' → Q)),
      Function.Injective embed :=
  ⟨fun h i => if h' : (i : ℕ) < t then h ⟨i, h'⟩ else q₀,
   fun h₁ h₂ heq => funext fun i => by
     have := congr_fun heq ⟨i, i.isLt.trans_le hle⟩
     simp [i.isLt] at this
     exact this⟩

/-! ## B. Probabilistic -/

/-! ### B.1 Expected-value trilemma -/

/--
**Stochastic trilemma (expected-value form).**

Apply IVT directly to the continuous expected confidence `cbar` and
expected truth-distance `dbar`. No measure theory required beyond naming
the maps.
-/
theorem stochastic_trilemma_expected
    {Q : Type*} [TopologicalSpace Q] [ConnectedSpace Q]
    (cbar dbar : Q → ℝ)
    (hcbar : Continuous cbar)
    (hdbar : Continuous dbar)
    (hF   : ∀ q, cbar q ≥ 1/2 → dbar q < 0)
    (hC   : (∃ q, dbar q < 0) ∧ (∃ q, dbar q > 0))
    (hCal : ∀ q, (cbar q > 1/2 ↔ dbar q < 0) ∧ (cbar q < 1/2 ↔ dbar q > 0)) :
    False := by
  obtain ⟨⟨q_t, h_t⟩, ⟨q_f, h_f⟩⟩ := hC
  have hct : cbar q_t > 1/2 := (hCal q_t).1.mpr h_t
  have hcf : cbar q_f < 1/2 := (hCal q_f).2.mpr h_f
  obtain ⟨q₀, _, hq₀⟩ :=
    isPreconnected_univ.intermediate_value₂
      (mem_univ q_f) (mem_univ q_t)
      hcbar.continuousOn continuous_const.continuousOn
      (le_of_lt hcf) (le_of_lt hct)
  have h_not_neg : ¬ dbar q₀ < 0 := fun h =>
    absurd ((hCal q₀).1.mpr h) (by linarith)
  have h_not_pos : ¬ dbar q₀ > 0 := fun h =>
    absurd ((hCal q₀).2.mpr h) (by linarith)
  linarith [hF q₀ (ge_of_eq hq₀),
            le_antisymm (not_lt.mp h_not_pos) (not_lt.mp h_not_neg)]

/-! ### B.2 Stochastic dichotomy -/

/--
**Stochastic dichotomy.**

At a forced boundary point where `∫ d dμ = 0`:
if sample faithfulness holds a.e. (`c ≥ 1/2 → d < 0` μ-a.e.)
and high-confidence outputs occur with positive probability
(`μ{c ≥ 1/2} > 0`), then the model actively hallucinates:
`μ{d > 0} > 0`.

**Proof sketch:**
Suppose for contradiction `μ{d > 0} = 0`. Then `d ≤ 0` μ-a.e.
Since `∫ d dμ = 0` and `-d ≥ 0` a.e., the integral identity
`integral_eq_zero_iff_of_nonneg_ae` gives `-d = 0` a.e., i.e. `d = 0` a.e.
But sample faithfulness says on the positive-measure set `{c ≥ 1/2}`,
`d < 0` a.e. --- contradicting `d = 0` a.e. on that set.
-/
theorem stochastic_dichotomy
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c d : Ω → ℝ)
    (_hc_meas : Measurable c)
    (_hd_meas : Measurable d)
    (h_int   : ∫ ω, d ω ∂μ = 0)
    (h_faith : ∀ᵐ ω ∂μ, c ω ≥ 1/2 → d ω < 0)
    (h_conf  : μ {ω | c ω ≥ 1/2} > 0)
    (h_int_d : Integrable d μ) :
    μ {ω | d ω > 0} > 0 := by
  by_contra h
  push_neg at h
  -- μ{d > 0} = 0
  have h_zero : μ {ω | d ω > 0} = 0 :=
    nonpos_iff_eq_zero.mp h
  -- d ≤ 0 a.e.  (since the set where d > 0 has measure zero)
  have h_le : ∀ᵐ ω ∂μ, d ω ≤ 0 := by
    rw [ae_iff]; simp only [not_le]; exact h_zero
  -- -d ≥ 0 a.e.
  have h_neg_d_nn : 0 ≤ᵐ[μ] (-d) :=
    h_le.mono fun ω hω => by simp [hω]
  -- ∫ (-d) dμ = 0
  have h_int_neg : ∫ ω, -d ω ∂μ = 0 := by
    simp [integral_neg, h_int]
  -- -d = 0 a.e., hence d = 0 a.e.
  have h_d_zero : d =ᵐ[μ] 0 := by
    have hnd := (integral_eq_zero_iff_of_nonneg_ae h_neg_d_nn h_int_d.neg).mp h_int_neg
    filter_upwards [hnd] with ω hω
    simp only [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at hω
    exact hω
  -- a.e. ω in {c ≥ 1/2}: faith gives d < 0, but d = 0. Contradiction a.e.
  have h_no_conf : ∀ᵐ ω ∂μ, ¬ c ω ≥ 1/2 := by
    filter_upwards [h_faith, h_d_zero] with ω hfaith hzero hconf
    exact absurd hzero (ne_of_lt (hfaith hconf))
  -- μ{c ≥ 1/2} = 0  (from ae ¬(c ≥ 1/2))
  have h_conf_zero : μ {ω | c ω ≥ 1/2} = 0 := by
    rw [ae_iff] at h_no_conf; simpa using h_no_conf
  exact absurd h_conf_zero (ne_of_gt h_conf)

/--
**Boundary dichotomy (either-or form).**

Under sample faithfulness: either the model never outputs high-confidence
answers at `q₀` (`μ{c ≥ 1/2} = 0`), or it actively hallucinates
(`μ{d > 0} > 0`). The two alternatives are exhaustive; they are not claimed
to be mutually exclusive.
-/
theorem boundary_dichotomy
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c d : Ω → ℝ)
    (hc_meas : Measurable c)
    (hd_meas : Measurable d)
    (h_int   : ∫ ω, d ω ∂μ = 0)
    (h_faith : ∀ᵐ ω ∂μ, c ω ≥ 1/2 → d ω < 0)
    (h_int_d : Integrable d μ) :
    μ {ω | c ω ≥ 1/2} = 0 ∨ μ {ω | d ω > 0} > 0 := by
  rcases eq_or_ne (μ {ω | c ω ≥ 1/2}) 0 with h | h
  · exact Or.inl h
  · exact Or.inr (stochastic_dichotomy μ c d hc_meas hd_meas
        h_int h_faith (pos_of_ne_zero h) h_int_d)

end HoF

end
