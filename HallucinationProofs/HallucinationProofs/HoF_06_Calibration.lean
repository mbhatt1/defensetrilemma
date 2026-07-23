import Mathlib

/-!
# Hallucination Trilemma — Part 6: Calibration

This file formalizes the **Calibration** condition of the Hallucination
Trilemma: the model's confidence tracks truth-distance — specifically,
`confidence = 1/2` exactly on the preimage of the truth-set boundary
`∂T = {δ = 0}`.

## Setup

- `Q` is a (typically connected) topological space of questions.
- `A` is a topological space of answers.
- `M : Q → A × ℝ` — `(M q).1` is the answer, `(M q).2` is the
  confidence (intended to lie in `[0,1]`).
- `δ : Q × A → ℝ` is the truth-distance, with truth-set `T = {δ ≤ 0}`
  and boundary `∂T = {δ = 0}`.

**Calibration.** `(M q).2 = 1/2  ↔  δ (q, (M q).1) = 0`,
together with continuity of `q ↦ (M q).2`.

## Main results

1. `Calibrated` / `MonotoneCalibrated` — calibration predicates.
2. `calibrated_levelSet_eq` — the confidence half-level set coincides
   with the model truth-boundary.
3. `confHalf_isClosed` — calibration ⇒ the confidence half-level set is
   closed (preimage of a point under the continuous confidence map).
4. `monotoneCalibrated_half_on_boundary` — the monotone form implies
   the equivalence at `1/2` on the boundary.
5. `calibrated_confHalf_nonempty` — on a connected space, calibration
   plus values straddling `1/2` forces the half-level set to be
   non-empty (IVT).
6. `confHalf_implies_truthBoundary` — direct extraction of the forward
   direction.
7. `off_boundary_conf_not_half` — the contrapositive: off the boundary,
   confidence cannot equal `1/2`.
-/

open Set Topology Filter

noncomputable section

namespace HoF

/-! ## 1. Calibration predicates -/

/-- **Calibration.** Confidence equals `1/2` exactly on the preimage of
the truth boundary, and is continuous. This is the rigorous topological
formalization of "confidence tracks truth-distance" at the boundary. -/
structure Calibrated {Q A : Type*} [TopologicalSpace Q]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop where
  conf_continuous : Continuous (fun q => (M q).2)
  half_on_boundary : ∀ q, (M q).2 = 1/2 ↔ δ (q, (M q).1) = 0

/-- **Weaker monotone calibration.** Confidence is `> 1/2` iff the
answer is strictly inside the truth-set, and `< 1/2` iff strictly
outside. By trichotomy, this implies the boundary equivalence. -/
def MonotoneCalibrated {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ q, ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
       ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0)

/-! ## 2. Level-set equality -/

/-- **Calibration ⇒ confidence-half level set equals model truth
boundary.** Direct unfolding of `half_on_boundary`. -/
theorem calibrated_levelSet_eq
    {Q A : Type*} [TopologicalSpace Q]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hCal : Calibrated M δ) :
    {q | (M q).2 = 1/2} = {q | δ (q, (M q).1) = 0} := by
  ext q
  exact hCal.half_on_boundary q

/-! ## 3. Closedness of the confidence half-level set -/

/-- **Calibration ⇒ the confidence half level set is closed.**
The preimage of the singleton `{1/2}` under the continuous confidence
map is closed. -/
theorem confHalf_isClosed
    {Q A : Type*} [TopologicalSpace Q]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hCal : Calibrated M δ) :
    IsClosed {q | (M q).2 = 1/2} :=
  isClosed_eq hCal.conf_continuous continuous_const

/-! ## 4. Monotone calibration ⇒ boundary equivalence -/

/-- **Trichotomy lemma.** If `MonotoneCalibrated` holds, then for each
`q`, the confidence is `1/2` iff the truth-distance at the model's
answer is zero. The proof is by trichotomy on `(M q).2` versus `1/2`,
using the two strict equivalences provided by `MonotoneCalibrated`. -/
theorem monotoneCalibrated_half_on_boundary
    {Q A : Type*}
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hMC : MonotoneCalibrated M δ) :
    ∀ q, (M q).2 = 1/2 ↔ δ (q, (M q).1) = 0 := by
  intro q
  obtain ⟨hgt, hlt⟩ := hMC q
  constructor
  · -- (M q).2 = 1/2 → δ = 0
    intro hEq
    rcases lt_trichotomy (δ (q, (M q).1)) 0 with hδ | hδ | hδ
    · -- δ < 0 ⇒ confidence > 1/2, contradiction with hEq
      have hconf : (M q).2 > 1/2 := hgt.mpr hδ
      exact absurd hEq (ne_of_gt hconf)
    · exact hδ
    · -- δ > 0 ⇒ confidence < 1/2, contradiction with hEq
      have hconf : (M q).2 < 1/2 := hlt.mpr hδ
      exact absurd hEq (ne_of_lt hconf)
  · -- δ = 0 → (M q).2 = 1/2
    intro hδ
    rcases lt_trichotomy ((M q).2) (1/2 : ℝ) with hc | hc | hc
    · -- conf < 1/2 ⇒ δ > 0, contradiction with hδ = 0
      have : δ (q, (M q).1) > 0 := hlt.mp hc
      exact absurd hδ (ne_of_gt this)
    · exact hc
    · -- conf > 1/2 ⇒ δ < 0, contradiction
      have : δ (q, (M q).1) < 0 := hgt.mp hc
      exact absurd hδ (ne_of_lt this)

/-! ## 5. IVT on the connected question space -/

/-- **Calibration on a connected space + straddling values ⇒ confidence
half level set non-empty.** Direct IVT on the continuous confidence
function: if some `q₁` has confidence `< 1/2` and some `q₂` has
confidence `> 1/2`, then there is a `q` with confidence exactly
`1/2`. -/
theorem calibrated_confHalf_nonempty
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hCal : Calibrated M δ)
    (q₁ q₂ : Q)
    (h₁ : (M q₁).2 < 1/2) (h₂ : (M q₂).2 > 1/2) :
    ∃ q, (M q).2 = 1/2 := by
  have hcont : Continuous (fun q => (M q).2) := hCal.conf_continuous
  have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
  have hq₁_mem : q₁ ∈ (Set.univ : Set Q) := Set.mem_univ _
  have hq₂_mem : q₂ ∈ (Set.univ : Set Q) := Set.mem_univ _
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂ hq₁_mem hq₂_mem
    hcont.continuousOn continuous_const.continuousOn
    (le_of_lt h₁) (le_of_lt h₂)
  exact ⟨c, hc⟩

/-! ## 6. Confidence half ⇒ truth boundary -/

/-- **Forward direction:** at any point with confidence exactly `1/2`,
the model's answer lies on `∂T` (i.e. `δ = 0`). -/
theorem confHalf_implies_truthBoundary
    {Q A : Type*} [TopologicalSpace Q]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hCal : Calibrated M δ)
    {q : Q} (hq : (M q).2 = 1/2) :
    δ (q, (M q).1) = 0 :=
  (hCal.half_on_boundary q).mp hq

/-! ## 7. Contrapositive: off-boundary forces non-half confidence -/

/-- **Crucial contrapositive.** If the model's answer at `q` is *not*
on the truth boundary (i.e. `δ ≠ 0`), then the confidence at `q` is
*not* `1/2`. This is the form of calibration used by the trilemma to
push `q` into either the high- or low-confidence region. -/
theorem off_boundary_conf_not_half
    {Q A : Type*} [TopologicalSpace Q]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hCal : Calibrated M δ)
    {q : Q} (hq : δ (q, (M q).1) ≠ 0) :
    (M q).2 ≠ 1/2 := by
  intro hConf
  exact hq ((hCal.half_on_boundary q).mp hConf)

/-! ## 8. Summary

**Calibration** is the second pillar of the Hallucination Trilemma. It
says: the model's confidence is exactly `1/2` precisely on the truth
boundary, and is continuous.

* `Calibrated M δ`            — the structure: continuity of confidence
                                 plus the boundary equivalence.
* `MonotoneCalibrated M δ`    — the strict-inequality form; implies
                                 the boundary equivalence by trichotomy
                                 (`monotoneCalibrated_half_on_boundary`).
* `calibrated_levelSet_eq`    — `{conf = 1/2} = {δ = 0}`.
* `confHalf_isClosed`         — that level set is closed (preimage of a
                                 point under a continuous map).
* `calibrated_confHalf_nonempty` — IVT on a connected `Q`: straddling
                                 values force the half-level set to be
                                 non-empty.
* `confHalf_implies_truthBoundary` / `off_boundary_conf_not_half` —
                                 the two directions, the latter being
                                 the contrapositive form invoked in the
                                 trilemma argument.

Combined with **Faithfulness** (Part 4) and **Coverage** (forthcoming),
calibration provides the rigid topological link between the level
structure of confidence and the truth-distance — the link that
ultimately yields the trilemma's contradiction.
-/

end HoF
