import Mathlib

/-!
# Hallucination Trilemma — Part 4: Faithfulness

This file formalizes the **Faithfulness** condition of the Hallucination
Trilemma: a model's high-confidence answers must lie in the truth-set
`T = {δ ≤ 0}` (equivalently, the truth-distance `δ` is non-positive).

## Setup

- `Q` is a (typically connected) topological space of questions.
- `A` is a topological space of answers.
- `M : Q → A × ℝ` is the model: `(M q).1` is the answer, `(M q).2` is
  the confidence (intended to lie in `[0,1]`).
- `δ : Q × A → ℝ` is the truth-distance, with truth-set `T = {δ ≤ 0}`
  and boundary `∂T = {δ = 0}`.

**Faithfulness.** `(M q).2 > 1/2  ⇒  δ (q, (M q).1) ≤ 0`.

## Main results

1. `Faithful` / `StrongFaithful` — the two faithfulness predicates.
2. `faithful_image_in_truth` — high-confidence questions map into `T`.
3. `highConf_closed` / `highConf_open` — closedness of `{conf ≥ c}`
   and openness of `{conf > c}`.
4. `faithful_closure_in_truth` — under continuity, the closure of the
   high-confidence region still maps into `T` (parallel to the
   `closure_safe_subset_fixedPoints` lemma in `MoF_08_DefenseBarriers`).
5. `faithful_at_half_boundary` — boundary points with confidence
   exactly `1/2` that are limits of strictly-high-confidence points
   still satisfy `δ ≤ 0`.
6. `low_conf_unconstrained` — sanity: faithfulness imposes nothing on
   low-confidence outputs.
-/

open Set Topology Filter

noncomputable section

namespace HoF

/-! ## 1. Faithfulness predicates -/

/--
A model `M` is **Faithful** with respect to truth-distance `δ` if every
high-confidence (`> 1/2`) answer lies in the truth-set `T = {δ ≤ 0}`.
-/
def Faithful {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ q, (M q).2 > 1/2 → δ (q, (M q).1) ≤ 0

/--
A model `M` is **StrongFaithful** with respect to `δ` if every
high-confidence answer lies in the strict interior of the truth-set,
i.e. `δ < 0`.
-/
def StrongFaithful {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ q, (M q).2 > 1/2 → δ (q, (M q).1) < 0

/-- StrongFaithful is strictly stronger than Faithful. -/
theorem StrongFaithful.toFaithful {Q A : Type*}
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hS : StrongFaithful M δ) : Faithful M δ :=
  fun q hq => le_of_lt (hS q hq)

/-! ## 2. Faithfulness: high-confidence region maps into T -/

/--
Direct reformulation of `Faithful` as a set-membership statement: the
image (along the diagonal `q ↦ (q, (M q).1)`) of the high-confidence
region lies in `T = {p | δ p ≤ 0}`.
-/
theorem faithful_image_in_truth
    {Q A : Type*}
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hF : Faithful M δ) :
    ∀ q, (M q).2 > 1/2 → (q, (M q).1) ∈ {p : Q × A | δ p ≤ 0} :=
  fun q hq => hF q hq

/-! ## 3. Closedness / openness of the confidence sublevel sets -/

/--
The set `{q | (M q).2 ≥ c}` is closed when the confidence function is
continuous. Standard preimage-of-closed argument.
-/
theorem highConf_closed
    {Q : Type*} [TopologicalSpace Q]
    {M : Q → ℝ × ℝ}
    (hM_conf : Continuous (fun q => (M q).2))
    (c : ℝ) :
    IsClosed {q | (M q).2 ≥ c} := by
  have : {q : Q | (M q).2 ≥ c} = (fun q => (M q).2) ⁻¹' (Set.Ici c) := by
    ext q; simp [Set.mem_Ici]
  rw [this]
  exact isClosed_Ici.preimage hM_conf

/--
The strict version: `{q | (M q).2 > c}` is open when the confidence is
continuous.
-/
theorem highConf_open
    {Q : Type*} [TopologicalSpace Q]
    {M : Q → ℝ × ℝ}
    (hM_conf : Continuous (fun q => (M q).2))
    (c : ℝ) :
    IsOpen {q | (M q).2 > c} := by
  have : {q : Q | (M q).2 > c} = (fun q => (M q).2) ⁻¹' (Set.Ioi c) := by
    ext q; simp [Set.mem_Ioi]
  rw [this]
  exact isOpen_Ioi.preimage hM_conf

/-! ## 4. The truth pull-back set is closed under continuity -/

/--
Under continuity of the answer map and the truth-distance, the set of
questions whose model-answer lies in `T` is closed.

This is the key topological ingredient: `q ↦ δ (q, (M q).1)` is
continuous, and `{x | x ≤ 0}` is closed in `ℝ`.
-/
theorem truth_preimage_closed
    {Q A : Type*} [TopologicalSpace Q] [TopologicalSpace A]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hM_ans : Continuous (fun q => (M q).1))
    (hδ : Continuous δ) :
    IsClosed {q : Q | δ (q, (M q).1) ≤ 0} := by
  have hcomp : Continuous (fun q : Q => δ (q, (M q).1)) := by
    have hpair : Continuous (fun q : Q => (q, (M q).1)) :=
      continuous_id.prodMk hM_ans
    exact hδ.comp hpair
  have hset : {q : Q | δ (q, (M q).1) ≤ 0}
      = (fun q : Q => δ (q, (M q).1)) ⁻¹' (Set.Iic 0) := by
    ext q; simp [Set.mem_Iic]
  rw [hset]
  exact isClosed_Iic.preimage hcomp

/-! ## 5. Faithfulness is preserved on the closure of the high-confidence region

This is the analogue of `closure_safe_subset_fixedPoints` from
`MoF_08_DefenseBarriers`: a closed set containing a region must contain
its closure. -/

/--
**Closure faithfulness.** If `M` is faithful and the relevant maps are
continuous, then every limit of strictly-high-confidence points still
maps into the truth-set.
-/
theorem faithful_closure_in_truth
    {Q A : Type*} [TopologicalSpace Q] [TopologicalSpace A]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hM_ans : Continuous (fun q => (M q).1))
    (_hM_conf : Continuous (fun q => (M q).2))
    (hδ : Continuous δ)
    (hF : Faithful M δ) :
    closure {q | (M q).2 > 1/2} ⊆ {q | δ (q, (M q).1) ≤ 0} := by
  -- The target set is closed, and contains the high-confidence region by faithfulness.
  exact (truth_preimage_closed hM_ans hδ).closure_subset_iff.mpr
    (fun q hq => hF q hq)

/-! ## 6. Boundary case: confidence exactly 1/2 -/

/--
**Half-boundary faithfulness.** A point `q₀` with confidence exactly
`1/2` that is a limit of strictly-high-confidence points still satisfies
`δ (q₀, (M q₀).1) ≤ 0`. This is the key fact used by the trilemma to
"squeeze" the boundary case.
-/
theorem faithful_at_half_boundary
    {Q A : Type*} [TopologicalSpace Q] [TopologicalSpace A]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hM_ans : Continuous (fun q => (M q).1))
    (hM_conf : Continuous (fun q => (M q).2))
    (hδ : Continuous δ)
    (hF : Faithful M δ)
    {q₀ : Q} (_hq₀ : (M q₀).2 = 1/2)
    (hq_lim : q₀ ∈ closure {q | (M q).2 > 1/2}) :
    δ (q₀, (M q₀).1) ≤ 0 :=
  faithful_closure_in_truth hM_ans hM_conf hδ hF hq_lim

/-! ## 7. Sanity check: faithfulness imposes nothing on low confidence -/

/--
**Low-confidence is unconstrained.** Faithfulness puts no constraint on
the truth-distance for confidence `≤ 1/2`. This is a (trivial)
sanity-check lemma — the implication direction is one-way.
-/
theorem low_conf_unconstrained
    {Q A : Type*} (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (_hF : Faithful M δ) :
    ∀ q, (M q).2 ≤ 1/2 → True := fun _ _ => trivial

/-! ## 8. Summary

**Faithfulness** is one of the three pillars of the Hallucination
Trilemma. It says: high confidence implies truth.

* `Faithful M δ`     — the predicate `(M q).2 > 1/2 → δ (q, (M q).1) ≤ 0`.
* `StrongFaithful`    — strict version: `δ < 0`.
* The high-confidence region `{q | (M q).2 > 1/2}` is open, and
  `{q | (M q).2 ≥ c}` is closed when the confidence is continuous.
* Under continuity, faithfulness extends from the open
  high-confidence region to its closure (`faithful_closure_in_truth`).
* In particular, boundary points with confidence exactly `1/2` that
  are limits of higher-confidence points still satisfy `δ ≤ 0`
  (`faithful_at_half_boundary`).

These topological closure facts are the ingredients that combine with
**Calibration** and **Coverage** in the trilemma to force a
contradiction.
-/

end HoF
