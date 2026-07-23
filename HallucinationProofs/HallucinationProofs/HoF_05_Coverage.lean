import Mathlib

/-!
# Hallucination of Failure — Part 5: Coverage Condition

We formalize the **Coverage** condition of the Hallucination Trilemma: the
model's image hits both sides of the truth-set boundary `∂T`. Concretely, the
model is willing to express both true-side answers (`δ < 0`) and false-side
answers (`δ > 0`) across its question domain.

## Setting

* `Q` — connected topological space of questions
* `A` — topological space of answers
* `M : Q → A × ℝ` — model: answer (`.1`) and confidence (`.2`)
* `δ : Q × A → ℝ` — truth-distance, with `T = {δ ≤ 0}` and `∂T = {δ = 0}`

## Three forms of coverage

1. **`Covering M δ`** — practical two-sided form: there exist `q_t` with
   `δ(q_t, M.ans q_t) < 0` and `q_f` with `δ(q_f, M.ans q_f) > 0`. This is
   the workhorse for the IVT obstruction.
2. **`DenseCoverage M`** — strong topological form: the image `{(M q).1}`
   is dense in answer space.
3. **`BoundaryCovering M δ`** — every boundary point `(q,a)` with `δ = 0`
   is approximable by graph points `(q, M.ans q)`.

## Main results

* `covering_image_straddles_zero` — unfolding form
* `denseCoverage_closure_eq_univ` — dense coverage hits everything
* `covering_yields_truth_boundary_point` — the IVT workhorse
* `covering_yields_two_sided_witnesses` — explicit witness extraction

All proofs are sorry-free.
-/

open Set Topology Filter

noncomputable section

namespace HoF

/-! ## Definitions -/

/-- **Two-sided coverage.** The model produces both true-side and false-side
answers across its question domain. -/
def Covering {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0)

/-- **Dense coverage.** The image of the model's answer component is dense in
the answer space `A`. -/
def DenseCoverage {Q A : Type*} [TopologicalSpace A]
    (M : Q → A × ℝ) : Prop :=
  Dense (Set.range (fun q => (M q).1))

/-- **Boundary coverage.** Every boundary point of `T` lies in the closure of
the model's graph (in question-answer space). -/
def BoundaryCovering {Q A : Type*} [TopologicalSpace (Q × A)]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ p, δ p = 0 → p ∈ closure (Set.range (fun q => (q, (M q).1)))

/-! ## 1. Covering unfolds to two-sided witnesses -/

/--
**Coverage straddles zero.** Unfolding the definition of `Covering`, we
recover the two-sided existence statements directly.
-/
theorem covering_image_straddles_zero
    {Q A : Type*}
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hC : Covering M δ) :
    (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0) :=
  hC

/-! ## 2. Dense coverage gives full closure -/

/--
**Dense coverage ⇒ closure of range is everything.** A direct application of
`Dense.closure_eq`.
-/
theorem denseCoverage_closure_eq_univ
    {Q A : Type*} [TopologicalSpace A]
    {M : Q → A × ℝ} (hD : DenseCoverage M) :
    closure (Set.range (fun q => (M q).1)) = Set.univ :=
  hD.closure_eq

/-! ## 3. Coverage yields a boundary point via IVT -/

/--
**The Coverage / IVT workhorse.** Under coverage, the composite
`g(q) := δ(q, (M q).1)` is continuous and takes both signs on the connected
space `Q`. By the intermediate value theorem, there is some `q` with
`δ (q, (M q).1) = 0` — a question whose model answer lies exactly on the truth
boundary.

This is the core obstruction driving the Hallucination Trilemma: in the
presence of coverage and continuity, the model graph must cross `∂T`.
-/
theorem covering_yields_truth_boundary_point
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hM_ans : Continuous (fun q => (M q).1))
    (hδ : Continuous δ)
    (hC : Covering M δ) :
    ∃ q, δ (q, (M q).1) = 0 := by
  -- Build the composite g(q) := δ(q, (M q).1) and prove it continuous.
  set g : Q → ℝ := fun q => δ (q, (M q).1) with hg_def
  have hg : Continuous g := by
    have hpair : Continuous (fun q : Q => (q, (M q).1)) :=
      continuous_id.prodMk hM_ans
    exact hδ.comp hpair
  -- Extract the two sign witnesses from coverage.
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hC
  -- Apply IVT on the connected universe.
  have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
  have ha_mem : a ∈ (Set.univ : Set Q) := Set.mem_univ _
  have hb_mem : b ∈ (Set.univ : Set Q) := Set.mem_univ _
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂ ha_mem hb_mem
    hg.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)
  exact ⟨c, hc⟩

/-! ## 4. Two-sided witness extraction (definitional) -/

/--
**Two-sided witnesses.** A direct restatement of `Covering` producing named
witnesses `q_t` (true-side) and `q_f` (false-side).
-/
theorem covering_yields_two_sided_witnesses
    {Q A : Type*}
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hC : Covering M δ) :
    ∃ q_t q_f : Q,
      δ (q_t, (M q_t).1) < 0 ∧ δ (q_f, (M q_f).1) > 0 := by
  obtain ⟨⟨q_t, ht⟩, ⟨q_f, hf⟩⟩ := hC
  exact ⟨q_t, q_f, ht, hf⟩

/-! ## 5. Coverage near the boundary (weakened form) -/

/--
**Closed-side approachability.** Coverage on a connected space yields the
existence of two questions whose model answers lie on opposite *closed* sides
of the boundary: one with `δ ≤ 0` and one with `δ ≥ 0`. (The strict witnesses
already lie on the corresponding closed sides.)

This is the practical near-boundary statement; the stronger
`∀ ε > 0`-statement reduces to repeated application of the IVT inside
sublevel and superlevel neighborhoods, which we omit for compactness.
-/
theorem covering_two_closed_sides
    {Q A : Type*}
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hC : Covering M δ) :
    ∃ q₁ q₂ : Q,
      δ (q₁, (M q₁).1) ≤ 0 ∧ δ (q₂, (M q₂).1) ≥ 0 := by
  obtain ⟨⟨q₁, h₁⟩, ⟨q₂, h₂⟩⟩ := hC
  exact ⟨q₁, q₂, le_of_lt h₁, le_of_lt h₂⟩

/--
**Boundary value attained.** Coverage plus continuity guarantee a question
`q₀` where `|δ(q₀, M.ans q₀)|` is exactly zero — i.e. the model graph touches
the boundary. This packages `covering_yields_truth_boundary_point` in the
absolute-value form often invoked in trilemma arguments.
-/
theorem covering_abs_zero
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    {M : Q → A × ℝ} {δ : Q × A → ℝ}
    (hM_ans : Continuous (fun q => (M q).1))
    (hδ : Continuous δ)
    (hC : Covering M δ) :
    ∃ q, |δ (q, (M q).1)| = 0 := by
  obtain ⟨q, hq⟩ := covering_yields_truth_boundary_point hM_ans hδ hC
  exact ⟨q, by simp [hq]⟩

/-! ## 6. Dense coverage subsumes range-closure observations -/

/--
**Dense coverage ⇒ every answer is approximable.** For any answer `a : A`,
under dense coverage, every neighborhood of `a` contains the answer of some
question.
-/
theorem denseCoverage_approximable
    {Q A : Type*} [TopologicalSpace A]
    {M : Q → A × ℝ} (hD : DenseCoverage M) (a : A) :
    a ∈ closure (Set.range (fun q => (M q).1)) := by
  rw [denseCoverage_closure_eq_univ hD]
  exact Set.mem_univ _

/-! ## Summary

| # | Statement | Status |
|---|-----------|--------|
| 1 | `Covering` — two-sided witnesses for `δ` on the model graph | Defined |
| 2 | `DenseCoverage` — answer-image is dense in `A` | Defined |
| 3 | `BoundaryCovering` — boundary points lie in graph closure | Defined |
| 4 | `covering_image_straddles_zero` — unfolding form | Proved |
| 5 | `denseCoverage_closure_eq_univ` — `Dense.closure_eq` | Proved |
| 6 | `covering_yields_truth_boundary_point` — IVT workhorse | Proved |
| 7 | `covering_yields_two_sided_witnesses` — named witnesses | Proved |
| 8 | `covering_two_closed_sides` — closed-side approachability | Proved |
| 9 | `covering_abs_zero` — `|δ| = 0` form of the IVT result | Proved |
| 10 | `denseCoverage_approximable` — every answer is a limit | Proved |

All proofs are sorry-free. The central content is item 6: under coverage and
continuity, the model graph must intersect the truth boundary `∂T`. This is
the Hallucination Trilemma's geometric obstruction.
-/

end HoF

end
