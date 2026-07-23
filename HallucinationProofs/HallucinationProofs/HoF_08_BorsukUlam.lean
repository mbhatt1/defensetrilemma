import Mathlib

/-!
# Hallucination Trilemma — Part 8: Borsuk–Ulam-Style Antipodal Obstruction

This file develops a **Borsuk–Ulam-style obstruction** for the Hallucination
Trilemma. By considering an *antipodal action* on the question space `Q`
(think: negation, reframing, swapping a yes/no), any continuous calibrated
faithful coverage map must identify antipodal questions in a way that
violates one of the three properties.

## The 1D Borsuk–Ulam analog

For Mathlib v4.28, the full Borsuk–Ulam machinery for general spheres is
heavy. Instead, we prove the **1-dimensional analog**, which is essentially
the IVT applied to an *antipodally-odd* continuous function. Concretely:

> A continuous antipodally-odd `g : Q → ℝ` on a connected nonempty space `Q`
> with an antipodal involution `σ` (continuous, self-inverse, fixed-point
> free) must hit `0`.

This perfectly captures the antipodal-obstruction idea: if reframing
(antipodal action) flips the sign of the truth-distance, then by
connectedness the truth-distance must vanish at some intermediate
question — i.e. the model lies *exactly* on the truth boundary.

## Setup

- `Q` is a topological space of questions, equipped with an
  `AntipodalAction`.
- `A` is a topological space of answers.
- `M : Q → A × ℝ` — `(M q).1` is the answer, `(M q).2` is the confidence.
- `δ : Q × A → ℝ` is the truth-distance.

## Main results

1. `AntipodalAction Q` — structure: continuous, self-inverse, fixed-point-free
   involution `σ : Q → Q`.
2. `AntipodalOdd act g` — `g (σ q) = - g q` for all `q`.
3. `antipodal_odd_has_zero` — the 1D Borsuk–Ulam analog: an antipodally-odd
   continuous map on a connected `Q` has a zero.
4. `antipodal_yields_truth_boundary` — applied to the truth-distance
   composite, this gives a question on the model's truth boundary.
5. `antipodal_hallucination_trilemma` — combined with monotone calibration,
   forces the existence of a question with confidence exactly `1/2` and
   truth-distance exactly `0`.
-/

open Set Topology

noncomputable section

namespace HoF

/-! ## 1. Antipodal action -/

/-- An **antipodal involution** on a topological space `Q`: a continuous,
self-inverse, fixed-point-free map `σ : Q → Q`. This is the abstract
analog of the antipodal map `x ↦ -x` on a sphere. -/
structure AntipodalAction (Q : Type*) [TopologicalSpace Q] where
  /-- The involution. -/
  σ : Q → Q
  /-- `σ` is continuous. -/
  continuous : Continuous σ
  /-- `σ` is self-inverse. -/
  involution : ∀ q, σ (σ q) = q
  /-- `σ` has no fixed points. -/
  fixed_point_free : ∀ q, σ q ≠ q

/-! ## 2. Antipodally-odd functions -/

/-- A real-valued function `g : Q → ℝ` is **antipodally-odd** with respect
to an antipodal action `act` if `g (σ q) = - g q` for every `q`. This is
the abstract analog of an odd function `f : ℝ → ℝ` (i.e. `f (-x) = - f x`). -/
def AntipodalOdd {Q : Type*} [TopologicalSpace Q]
    (act : AntipodalAction Q) (g : Q → ℝ) : Prop :=
  ∀ q, g (act.σ q) = - g q

/-! ## 3. The 1D Borsuk–Ulam analog -/

/-- **1D Borsuk–Ulam analog.** Let `Q` be a connected topological space and
`act` an antipodal involution on `Q`. Any continuous antipodally-odd
function `g : Q → ℝ` has a zero.

The proof picks any `q₀ ∈ Q`. If `g q₀ = 0` we are done. Otherwise, by
antipodal-oddness, `g q₀` and `g (σ q₀)` have opposite signs, and the
intermediate value theorem on the connected space `Q` produces a zero. -/
theorem antipodal_odd_has_zero
    {Q : Type*} [TopologicalSpace Q] [ConnectedSpace Q]
    (act : AntipodalAction Q)
    (g : Q → ℝ) (hg : Continuous g)
    (hodd : AntipodalOdd act g)
    (q₀ : Q) :
    ∃ q, g q = 0 := by
  by_cases h : g q₀ = 0
  · exact ⟨q₀, h⟩
  · rcases lt_or_gt_of_ne h with hneg | hpos
    · -- g q₀ < 0; then g (σ q₀) = - g q₀ > 0, so by IVT on Q
      have hσ : g (act.σ q₀) > 0 := by
        rw [hodd q₀]; linarith
      have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
      obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂
        (Set.mem_univ q₀) (Set.mem_univ (act.σ q₀))
        hg.continuousOn continuous_const.continuousOn
        (le_of_lt hneg) (le_of_lt hσ)
      exact ⟨c, hc⟩
    · -- g q₀ > 0; symmetric: g (σ q₀) < 0
      have hσ : g (act.σ q₀) < 0 := by
        rw [hodd q₀]; linarith
      have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
      obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂
        (Set.mem_univ (act.σ q₀)) (Set.mem_univ q₀)
        hg.continuousOn continuous_const.continuousOn
        (le_of_lt hσ) (le_of_lt hpos)
      exact ⟨c, hc⟩

/-! ## 4. Application to the truth-distance composite -/

/-- **Antipodal obstruction for hallucination.** If the truth-distance
composite `q ↦ δ (q, (M q).1)` is antipodally-odd and continuous, then on
a connected question space there exists a question on the model's truth
boundary (`δ = 0` at the model's answer).

Continuity of the composite follows from continuity of the answer map
`q ↦ (M q).1`, of the projection `q ↦ (q, (M q).1)`, and of `δ`. -/
theorem antipodal_yields_truth_boundary
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (act : AntipodalAction Q)
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (hδ : Continuous δ)
    (hodd : AntipodalOdd act (fun q => δ (q, (M q).1)))
    (q₀ : Q) :
    ∃ q, δ (q, (M q).1) = 0 := by
  -- The composite g(q) = δ(q, (M q).1) is continuous as a composition of
  -- continuous maps: q ↦ (q, (M q).1) is continuous, and δ is continuous.
  have hpair : Continuous (fun q : Q => (q, (M q).1)) :=
    continuous_id.prodMk hM_ans
  have hg : Continuous (fun q : Q => δ (q, (M q).1)) :=
    hδ.comp hpair
  exact antipodal_odd_has_zero act _ hg hodd q₀

/-! ## 5. The antipodal hallucination trilemma -/

/-- **Antipodal Hallucination Trilemma.** Suppose:

* `Q` is a connected topological space, `A` is a topological space.
* `M : Q → A × ℝ` has continuous answer-map and continuous confidence-map.
* `δ : Q × A → ℝ` is continuous.
* The truth-distance composite is *antipodally-odd*: there is an antipodal
  involution `σ` on `Q` such that `δ (σ q, (M (σ q)).1) = - δ (q, (M q).1)`.
* `M` is *monotonely calibrated*: `(M q).2 > 1/2 ↔ δ < 0` and
  `(M q).2 < 1/2 ↔ δ > 0`.

Then there is a question `q` with `(M q).2 = 1/2` *and* the model's answer
lies exactly on the truth boundary `δ = 0`.

This is the antipodal analog of `HoF_07`'s trilemma: any *non-trivial*
calibrated faithful answer-map on a connected, antipodally-symmetric
question space is forced onto the boundary at some point. The hypothesis
`q₀` (an arbitrary base question) suffices to invoke the IVT inside
`antipodal_odd_has_zero`. -/
theorem antipodal_hallucination_trilemma
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (act : AntipodalAction Q)
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (_hM_conf : Continuous (fun q => (M q).2))
    (hδ : Continuous δ)
    (hodd : AntipodalOdd act (fun q => δ (q, (M q).1)))
    (hCal : ∀ q,
      ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
      ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0))
    (q₀ : Q) :
    ∃ q, (M q).2 = 1/2 ∧ δ (q, (M q).1) = 0 := by
  -- Step 1: extract a zero of the truth-distance composite.
  obtain ⟨q, hq⟩ :=
    antipodal_yields_truth_boundary act M δ hM_ans hδ hodd q₀
  refine ⟨q, ?_, hq⟩
  -- Step 2: from δ(q, M.ans q) = 0 and monotone calibration, deduce
  -- (M q).2 = 1/2 by trichotomy.
  obtain ⟨hgt, hlt⟩ := hCal q
  rcases lt_trichotomy ((M q).2) (1/2 : ℝ) with hc | hc | hc
  · -- conf < 1/2 ⇒ δ > 0, contradicts hq : δ = 0
    have hδpos : δ (q, (M q).1) > 0 := hlt.mp hc
    exact absurd hq (ne_of_gt hδpos)
  · exact hc
  · -- conf > 1/2 ⇒ δ < 0, contradicts hq : δ = 0
    have hδneg : δ (q, (M q).1) < 0 := hgt.mp hc
    exact absurd hq (ne_of_lt hδneg)

/-! ## 6. Summary

| # | Statement | Status |
|---|-----------|--------|
| 1 | `AntipodalAction Q` (structure) | Defined |
| 2 | `AntipodalOdd act g` (predicate) | Defined |
| 3 | `antipodal_odd_has_zero` (1D Borsuk–Ulam analog via IVT) | Proved |
| 4 | `antipodal_yields_truth_boundary` (truth-distance has a zero) | Proved |
| 5 | `antipodal_hallucination_trilemma` (forced boundary point) | Proved |

The 1D Borsuk–Ulam analog says: an antipodally-odd continuous function on
a connected space with a free involution must vanish somewhere. Pulled
back to the truth-distance composite, this forces the model onto the
truth boundary at some question; combined with monotone calibration, it
pins the confidence there to exactly `1/2`. This is the
**antipodal obstruction** form of the Hallucination Trilemma — symmetric,
sphere-flavoured, and entirely sorry-free.
-/

end HoF
