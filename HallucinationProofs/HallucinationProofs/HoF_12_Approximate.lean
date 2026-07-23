import Mathlib
import HallucinationProofs.HoF_07_TrilemmaCore

/-!
# Hallucination Trilemma — Part 12: Approximate and Discrete Bridge

This file bridges the exact trilemma to approximate calibration.

## The gap in the main theorem

The exact trilemma requires strict biconditional calibration:
`conf > c ↔ δ < 0` and `conf < c ↔ δ > 0`.

No deployed model satisfies this exactly. This file proves:

1. **Approximate continuous trilemma** (`approx_trilemma`): Under ε-calibration
   (calibration holds strictly outside an ε-band), ε-coverage, and c-faithfulness
   on a connected space, there exists `q₀` with `conf(q₀) = c` and
   `δ(q₀) ∈ [-ε, 0)`. At `ε = 0` this gives the exact contradiction
   `0 ≤ δ(q₀) < 0`.

2. **Discrete band constraint** (`discrete_approx_bridge`): On any sets (no
   topology), for any question `q*` in the upper confidence band with
   `c ≤ conf(q*) ≤ c + ε`, the same arithmetic gives `δ(q*) ∈ [-ε, 0)`.

## Calibration condition

We use **two-sided ε-calibration**:
- `δ(q) < -ε → conf(q) > c + ε`   (very correct → conf clearly above c)
- `δ(q) > ε  → conf(q) < c - ε`   (very wrong   → conf clearly below c)

Contrapositives:
- `conf(q) ≤ c + ε → δ(q) ≥ -ε`
- `conf(q) ≥ c - ε → δ(q) ≤ ε`

These are the two lines needed for the discrete bridge.
-/

open Set

noncomputable section

namespace HoF

/-- Two-sided ε-calibration: truth-distance values outside the `±ε` truth band
    force confidence to the corresponding side of the `c ± ε` confidence band.

This is intentionally one-way. At `ε = 0` it is the part of strict calibration
needed by the IVT argument: `δ < 0 → conf > c` and `δ > 0 → conf < c`. -/
def EpsCalibrated {Q A : Type*} (M : Q → A × ℝ) (δ : Q × A → ℝ) (c ε : ℝ) : Prop :=
  (∀ q, δ (q, (M q).1) < -ε → (M q).2 > c + ε) ∧
  (∀ q, δ (q, (M q).1) > ε  → (M q).2 < c - ε)

/-- ε-coverage: witnesses strictly outside the ε-band around the boundary. -/
def EpsCovering {Q A : Type*} (M : Q → A × ℝ) (δ : Q × A → ℝ) (ε : ℝ) : Prop :=
  (∃ q, δ (q, (M q).1) < -ε) ∧ (∃ q, δ (q, (M q).1) > ε)

/-! ## 1. Continuous approximate trilemma -/

/--
**Approximate Hallucination Trilemma (continuous).**

Under ε-coverage, two-sided ε-calibration, c-faithfulness, and continuity
on a connected space:

∃ q₀ with conf(q₀) = c and δ(q₀) ∈ [-ε, 0).

**Proof.** Two-sided ε-calibration converts ε-coverage witnesses into
confidence witnesses: `conf(q_t) > c + ε ≥ c` and `conf(q_f) < c - ε ≤ c`.
IVT gives `q₀` with `conf(q₀) = c`.

At `q₀`:
- **Lower bound** (`δ ≥ -ε`): if `δ(q₀) < -ε` then by ε-calibration
  `conf(q₀) > c + ε`, contradicting `conf(q₀) = c`.
- **Upper bound** (`δ < 0`): from c-faithfulness since `conf(q₀) = c ≥ c`.
-/
theorem approx_trilemma
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c ε : ℝ) (hε : 0 ≤ ε)
    (hconf   : Continuous (fun q => (M q).2))
    (hcov    : EpsCovering M δ ε)
    (hcal    : EpsCalibrated M δ c ε)
    (hfaith  : ∀ q, (M q).2 ≥ c → δ (q, (M q).1) < 0) :
    ∃ q₀, (M q₀).2 = c ∧ -ε ≤ δ (q₀, (M q₀).1) ∧ δ (q₀, (M q₀).1) < 0 := by
  obtain ⟨⟨q_t, ht⟩, ⟨q_f, hf⟩⟩ := hcov
  -- ε-calibration gives confidence witnesses
  have hct : (M q_t).2 > c + ε := hcal.1 q_t ht
  have hcf : (M q_f).2 < c - ε := hcal.2 q_f hf
  -- IVT: confidence crosses c
  have hct' : (M q_t).2 > c := by linarith
  have hcf' : (M q_f).2 < c := by linarith
  obtain ⟨q₀, _, hq₀⟩ :=
    isPreconnected_univ.intermediate_value₂
      (mem_univ q_f) (mem_univ q_t)
      hconf.continuousOn continuous_const.continuousOn
      (le_of_lt hcf') (le_of_lt hct')
  refine ⟨q₀, hq₀, ?_, hfaith q₀ (ge_of_eq hq₀)⟩
  -- Lower bound: if δ(q₀) < -ε then ε-calibration gives conf(q₀) > c+ε, but conf(q₀) = c
  by_contra h
  push_neg at h
  have := hcal.1 q₀ h
  linarith

/-! ## 2. ε = 0 recovers an exact contradiction -/

/--
**Exact contradiction as the ε = 0 case.**

At `ε = 0`, `EpsCalibrated` is the one-sided part of strict calibration needed
for the IVT argument. `approx_trilemma` gives `q₀` with `conf(q₀) = c` and
`0 ≤ δ(q₀) < 0`, hence `False`.
-/
theorem exact_from_approx
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c : ℝ)
    (hconf  : Continuous (fun q => (M q).2))
    (hcov   : EpsCovering M δ 0)
    (hcal   : EpsCalibrated M δ c 0)
    (hfaith : ∀ q, (M q).2 ≥ c → δ (q, (M q).1) < 0) :
    False := by
  obtain ⟨q₀, _, hle, hlt⟩ :=
    approx_trilemma M δ c 0 le_rfl hconf hcov hcal hfaith
  linarith

/--
Strict calibration at the paper's `1/2` threshold implies zero-slack
ε-calibration at the same threshold.
-/
theorem strictCalibrated_to_epsCalibrated_zero_half
    {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (hcal : StrictCalibrated M δ) :
    EpsCalibrated M δ (1/2) 0 := by
  constructor
  · intro q hδ
    have hδ0 : δ (q, (M q).1) < 0 := by
      simpa using hδ
    have hconf : (M q).2 > 1 / 2 := ((hcal q).1).mpr hδ0
    simpa using hconf
  · intro q hδ
    have hδ0 : δ (q, (M q).1) > 0 := by
      simpa using hδ
    have hconf : (M q).2 < 1 / 2 := ((hcal q).2).mpr hδ0
    simpa using hconf

/-- Ordinary trilemma coverage is zero-slack ε-coverage. -/
theorem trilemmaCovering_to_epsCovering_zero
    {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (hcov : TrilemmaCovering M δ) :
    EpsCovering M δ 0 := by
  simpa [EpsCovering, TrilemmaCovering] using hcov

/--
The exact strict-calibration trilemma follows from the approximate bridge at
zero slack. This variant needs only confidence continuity, because the IVT step
is applied only to the confidence map.
-/
theorem exact_from_strictCalibrated_via_approx
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (hconf : Continuous (fun q => (M q).2))
    (hfaith : TrilemmaFaithful M δ)
    (hcov : TrilemmaCovering M δ)
    (hcal : StrictCalibrated M δ) :
    False := by
  exact exact_from_approx M δ (1/2) hconf
    (trilemmaCovering_to_epsCovering_zero M δ hcov)
    (strictCalibrated_to_epsCalibrated_zero_half M δ hcal) hfaith

/-! ## 3. Discrete band constraint -/

/--
**Discrete approximate bridge.**

On any sets `Q`, `A` (no topology, no finiteness):

For any question `q*` with `c ≤ conf(q*) ≤ c + ε`, two-sided ε-calibration
and c-faithfulness force `δ(q*) ∈ [-ε, 0)`.

**Proof.**
- `δ(q*) < 0`: from c-faithfulness since `conf(q*) ≥ c`.
- `δ(q*) ≥ -ε`: if `δ(q*) < -ε`, ε-calibration gives `conf(q*) > c + ε`,
  contradicting `conf(q*) ≤ c + ε`.

**Significance.** On a connected continuous space, IVT forces a question with
`conf = c` to exist (from ε-coverage). On a discrete space, the same arithmetic
applies to any question in the upper confidence band whenever it exists.
-/
theorem discrete_approx_bridge
    {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c ε : ℝ) (_hε : 0 ≤ ε)
    (hcal   : EpsCalibrated M δ c ε)
    (hfaith : ∀ q, (M q).2 ≥ c → δ (q, (M q).1) < 0)
    (q  : Q)
    (hge : (M q).2 ≥ c)        -- in the upper half of the confidence band
    (hle : (M q).2 ≤ c + ε) :  -- not above the band
    -ε ≤ δ (q, (M q).1) ∧ δ (q, (M q).1) < 0 := by
  constructor
  · -- Lower bound: contrapositive of ε-calibration first clause
    -- If δ < -ε then conf > c+ε, contradicting conf ≤ c+ε
    by_contra h
    push_neg at h
    have := hcal.1 q h
    linarith
  · exact hfaith q hge

/-! ## 4. Corollary: no question escapes both constraints simultaneously -/

/--
**Impossibility in the band.**

Under two-sided ε-calibration and c-faithfulness, no question can satisfy
BOTH:
- `conf(q) ≥ c` (high enough confidence for faithfulness to apply), and
- `δ(q) = 0` (exactly on the truth boundary).

The upper-band conclusion `δ ∈ [-ε, 0)` excludes `δ = 0`.
-/
theorem no_boundary_in_upper_band
    {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c ε : ℝ) (hε : 0 ≤ ε)
    (hcal   : EpsCalibrated M δ c ε)
    (hfaith : ∀ q, (M q).2 ≥ c → δ (q, (M q).1) < 0)
    (q  : Q)
    (hge : (M q).2 ≥ c)
    (hle : (M q).2 ≤ c + ε)
    (hbdy : δ (q, (M q).1) = 0) :
    False := by
  have ⟨_, hlt⟩ := discrete_approx_bridge M δ c ε hε hcal hfaith q hge hle
  linarith

end HoF

end
