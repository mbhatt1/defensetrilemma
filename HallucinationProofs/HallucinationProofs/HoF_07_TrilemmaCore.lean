import Mathlib

/-!
# Hallucination Trilemma — Part 7: The Core Impossibility Theorem

This file states and proves the **core impossibility theorem** of the
Hallucination Trilemma. A continuous model on a connected question space
cannot simultaneously be **Faithful**, **Covering**, and **(strictly)
Calibrated** when the truth-set has a non-trivial boundary.

## Setup

* `Q` — connected topological space (questions)
* `A` — topological space (answers)
* `M : Q → A × ℝ` — model: `(M q).1` answer, `(M q).2` confidence
* `δ : Q × A → ℝ` — continuous truth-distance, `T = {δ ≤ 0}`,
  `∂T = {δ = 0}`

## The three conditions

* **Faithful** (strong form): `(M q).2 ≥ 1/2 → δ (q, (M q).1) < 0`.
* **Covering**: there exist `q_t` with `δ < 0` and `q_f` with `δ > 0`.
* **StrictCalibrated**: `(M q).2 > 1/2 ↔ δ < 0` and
  `(M q).2 < 1/2 ↔ δ > 0`.

## Main results

* `hallucination_trilemma_strict` — under continuity, Covering, and
  StrictCalibrated, there exists a question `q` with confidence
  exactly `1/2` and `δ` exactly `0`. This is the geometric obstruction.
* `hallucination_trilemma` — adding StrongFaithful makes the system
  inconsistent: `False` follows.

The proof is a direct application of the IVT on the connected question
space, combined with the strict-iff form of calibration.

All proofs are sorry-free.
-/

open Set Topology Filter

noncomputable section

namespace HoF

/-! ## 1. The three conditions, packaged for legibility -/

/--
**Strong Faithful.** Every confidence `≥ 1/2` answer lies *strictly*
inside the truth-set: `δ < 0`. This is the form used in the trilemma
contradiction; the (weaker) `≤ 0` form admits the boundary case
`δ = 0`, which the IVT-extracted point would otherwise satisfy.
-/
def TrilemmaFaithful {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ q, (M q).2 ≥ 1/2 → δ (q, (M q).1) < 0

/--
**Covering.** The model exhibits both true-side answers (`δ < 0`) and
false-side answers (`δ > 0`) across its question domain.
-/
def TrilemmaCovering {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0)

/--
**Strict calibration.** The confidence is on one side of `1/2` if and
only if the truth-distance is on the corresponding side of `0`.
-/
def StrictCalibrated {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ q,
    ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
    ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0)

/-! ## 2. The core IVT-driven obstruction -/

/--
**Boundary-confidence ambiguity.** Under continuity, Covering, and
StrictCalibrated, there exists a question `q₀` at which the confidence
is *exactly* `1/2` and the truth-distance is *exactly* `0`.

Geometrically: the model graph cannot avoid a point sitting on `∂T`
with the calibrator's "ambiguity" confidence `1/2`. This is the
obstruction that prevents a *Strong Faithful* model from coexisting
with the other two conditions.

The proof uses the intermediate value theorem on the continuous
confidence map over the connected question space, picking up a
crossing point of `1/2`. Strict calibration then forces `δ = 0` at
that crossing.
-/
theorem hallucination_trilemma_strict
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (_hM_ans : Continuous (fun q => (M q).1))
    (hM_conf : Continuous (fun q => (M q).2))
    (_hδ : Continuous δ)
    (hC : TrilemmaCovering M δ)
    (hCal : StrictCalibrated M δ) :
    ∃ q, (M q).2 = 1/2 ∧ δ (q, (M q).1) = 0 := by
  -- Extract two-sided coverage witnesses.
  obtain ⟨⟨q_t, h_t⟩, ⟨q_f, h_f⟩⟩ := hC
  -- Strict calibration converts δ-witnesses into confidence-witnesses.
  have hconf_t : (M q_t).2 > 1/2 := ((hCal q_t).1).mpr h_t
  have hconf_f : (M q_f).2 < 1/2 := ((hCal q_f).2).mpr h_f
  -- Apply IVT on the connected universe to the continuous confidence map,
  -- picking up a question where confidence equals `1/2`.
  have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
  obtain ⟨q₀, _, hq₀⟩ := h_conn.intermediate_value₂
    (Set.mem_univ q_f) (Set.mem_univ q_t)
    hM_conf.continuousOn continuous_const.continuousOn
    (le_of_lt hconf_f) (le_of_lt hconf_t)
  refine ⟨q₀, hq₀, ?_⟩
  -- Now use strict calibration at `q₀` to pin `δ (q₀, ans q₀) = 0`.
  -- (M q₀).2 = 1/2, so neither `> 1/2` nor `< 1/2` holds; the iffs
  -- then exclude `δ < 0` and `δ > 0`, forcing equality.
  have h_not_lt : ¬ δ (q₀, (M q₀).1) < 0 := by
    intro h
    have hgt : (M q₀).2 > 1/2 := ((hCal q₀).1).mpr h
    linarith
  have h_not_gt : ¬ δ (q₀, (M q₀).1) > 0 := by
    intro h
    have hlt : (M q₀).2 < 1/2 := ((hCal q₀).2).mpr h
    linarith
  exact le_antisymm (not_lt.mp h_not_gt) (not_lt.mp h_not_lt)

/-! ## 3. The trilemma proper: incompatibility of all three conditions -/

/--
**Hallucination Trilemma (core impossibility).** A continuous model on
a connected question space cannot simultaneously be Strong-Faithful,
Covering, and StrictCalibrated. The three conditions are mutually
inconsistent.

The proof composes `hallucination_trilemma_strict` (which produces a
question `q₀` with confidence `1/2` and `δ = 0`) with Strong
Faithfulness (which says confidence `≥ 1/2` forces `δ < 0`). The
boundary case `δ = 0` violates the strict inequality.
-/
theorem hallucination_trilemma
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (hM_conf : Continuous (fun q => (M q).2))
    (hδ : Continuous δ)
    (hF : TrilemmaFaithful M δ)
    (hC : TrilemmaCovering M δ)
    (hCal : StrictCalibrated M δ) :
    False := by
  obtain ⟨q₀, hconf, hd⟩ :=
    hallucination_trilemma_strict M δ hM_ans hM_conf hδ hC hCal
  -- Strong Faithfulness at `q₀`: conf ≥ 1/2 ⇒ δ < 0.
  have hge : (M q₀).2 ≥ 1/2 := ge_of_eq hconf
  have hlt : δ (q₀, (M q₀).1) < 0 := hF q₀ hge
  -- But we just showed `δ (q₀, ans q₀) = 0`.
  linarith

/-! ## 4. A symmetric restatement using the unfolded existential form -/

/--
**Trilemma in raw existential form.** The same theorem, stated
directly in terms of the unfolded predicates (without the wrapped
`TrilemmaFaithful`/`TrilemmaCovering`/`StrictCalibrated` definitions).

This is convenient when the surrounding context already has
existential coverage and pointwise-iff calibration, but has not yet
introduced the named definitions of this file.
-/
theorem hallucination_trilemma_unfolded
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (hM_conf : Continuous (fun q => (M q).2))
    (hδ : Continuous δ)
    (hF : ∀ q, (M q).2 ≥ 1/2 → δ (q, (M q).1) < 0)
    (hC : (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0))
    (hCal : ∀ q,
      ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
      ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0)) :
    False :=
  hallucination_trilemma M δ hM_ans hM_conf hδ hF hC hCal

/-! ## 5. Boundary-confidence existence in unfolded form -/

/--
**Boundary-confidence existence in raw form.** Same as
`hallucination_trilemma_strict`, but stated without wrapping
`TrilemmaCovering` and `StrictCalibrated`.
-/
theorem hallucination_trilemma_strict_unfolded
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (hM_conf : Continuous (fun q => (M q).2))
    (hδ : Continuous δ)
    (hC : (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0))
    (hCal : ∀ q,
      ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
      ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0)) :
    ∃ q, (M q).2 = 1/2 ∧ δ (q, (M q).1) = 0 :=
  hallucination_trilemma_strict M δ hM_ans hM_conf hδ hC hCal

/-! ## 6. Summary

| # | Statement | Status |
|---|-----------|--------|
| 1 | `TrilemmaFaithful` — `conf ≥ 1/2 ⇒ δ < 0` | Defined |
| 2 | `TrilemmaCovering` — two-sided witnesses | Defined |
| 3 | `StrictCalibrated` — bi-conditional confidence/δ alignment | Defined |
| 4 | `hallucination_trilemma_strict` — IVT obstruction | Proved |
| 5 | `hallucination_trilemma` — the impossibility theorem | Proved |
| 6 | `hallucination_trilemma_unfolded` — raw-form impossibility | Proved |
| 7 | `hallucination_trilemma_strict_unfolded` — raw IVT obstruction | Proved |

All proofs are sorry-free.

**The geometric content.** Connectedness of `Q` plus continuity of
the confidence map forces `(M ·).2` to take the value `1/2` somewhere
between a `> 1/2` witness and a `< 1/2` witness (intermediate value
theorem). Strict calibration then traps the truth-distance at exactly
`0` at that crossing point. Strong Faithfulness, however, demands a
strict inequality `δ < 0` for *every* `conf ≥ 1/2` point — including
the crossing point itself. The strict inequality contradicts the
forced equality, so the three conditions cannot coexist.
-/

end HoF

end
