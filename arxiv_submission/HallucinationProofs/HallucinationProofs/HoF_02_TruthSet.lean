import Mathlib

/-!
# Hallucination of Failure — Part 2: Truth Set Topology

We develop the topology of the **truth set** `T = {δ ≤ 0}` for a continuous
truth-distance function `δ : QA → ℝ` defined on a question-answer space `QA`.

The picture mirrors `MoF_02_BasinStructure.lean` and
`MoF_03_ThresholdCrossing.lean` but is specialized to the threshold `τ = 0`:

* `TruthSet δ = {p | δ p ≤ 0}` — closed truth set
* `FalseSet δ = {p | δ p > 0}` — open false set
* `TruthBoundary δ = {p | δ p = 0}` — closed boundary (level set)
* `StrictTruth δ = {p | δ p < 0}` — open interior of truth

## Main results

1. `truthSet_isClosed` — truth set is closed for continuous `δ`
2. `falseSet_isOpen` — false set is open
3. `strictTruth_isOpen` — strict truth interior is open
4. `truthBoundary_isClosed` — boundary level set is closed
5. `truthBoundary_nonempty` — on connected `QA`, witnesses on either side
   force a boundary point (IVT)
6. `strictTruth_falseSet_separated` — closures meet only on the boundary
7. `strictTruth_not_closed` — strict truth cannot be clopen on a connected
   space when both regions are inhabited
8. `boundary_point_in_closure_of_strictTruth` — boundary points are limits
   of strict-truth points
9. `strictTruth_falseSet_no_intersect` — the strict and false sets are
   disjoint (definitional)

All proofs are sorry-free.
-/

open Set Topology Filter

noncomputable section

namespace HoF

variable {QA : Type*}

/-! ## Definitions (self-contained for this file) -/

/-- The **truth set** `{p | δ p ≤ 0}`: points whose truth-distance is
nonpositive. -/
def TruthSet (δ : QA → ℝ) : Set QA := {p | δ p ≤ 0}

/-- The **false set** `{p | δ p > 0}`: points strictly off the truth set. -/
def FalseSet (δ : QA → ℝ) : Set QA := {p | δ p > 0}

/-- The **truth boundary** `{p | δ p = 0}`: the level set where truth-distance
vanishes. -/
def TruthBoundary (δ : QA → ℝ) : Set QA := {p | δ p = 0}

/-- The **strict truth set** `{p | δ p < 0}`: the open interior of the truth
set. -/
def StrictTruth (δ : QA → ℝ) : Set QA := {p | δ p < 0}

/-! ## 1–4. Basic topology of the truth/false/boundary sets -/

/-- The truth set `{δ ≤ 0}` is closed for continuous `δ`. -/
theorem truthSet_isClosed [TopologicalSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ) :
    IsClosed (TruthSet δ) :=
  isClosed_le hδ continuous_const

/-- The false set `{δ > 0}` is open for continuous `δ`. -/
theorem falseSet_isOpen [TopologicalSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ) :
    IsOpen (FalseSet δ) :=
  isOpen_lt continuous_const hδ

/-- The strict truth set `{δ < 0}` is open for continuous `δ`. -/
theorem strictTruth_isOpen [TopologicalSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ) :
    IsOpen (StrictTruth δ) :=
  isOpen_lt hδ continuous_const

/-- The truth boundary `{δ = 0}` is closed for continuous `δ`. -/
theorem truthBoundary_isClosed [TopologicalSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ) :
    IsClosed (TruthBoundary δ) := by
  have : TruthBoundary δ = δ ⁻¹' {0} := by
    ext x; simp [TruthBoundary]
  rw [this]
  exact isClosed_singleton.preimage hδ

/-! ## 5. Boundary nonemptiness on connected spaces (IVT) -/

/--
**Truth boundary is nonempty.** On a connected topological space `QA`, if a
continuous truth-distance `δ` takes both a strictly-negative value (a true
point) and a strictly-positive value (a false point), then the boundary
`{δ = 0}` is nonempty.

Parallel to `threshold_level_set_nonempty` from `MoF_03_ThresholdCrossing`.
-/
theorem truthBoundary_nonempty
    [TopologicalSpace QA] [ConnectedSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ)
    (htrue : ∃ p, δ p < 0) (hfalse : ∃ p, δ p > 0) :
    (TruthBoundary δ).Nonempty := by
  obtain ⟨a, ha⟩ := htrue
  obtain ⟨b, hb⟩ := hfalse
  have h_conn : IsPreconnected (Set.univ : Set QA) := isPreconnected_univ
  have ha_mem : a ∈ (Set.univ : Set QA) := Set.mem_univ _
  have hb_mem : b ∈ (Set.univ : Set QA) := Set.mem_univ _
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂ ha_mem hb_mem
    hδ.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)
  exact ⟨c, hc⟩

/-! ## 6. Closure separation -/

/--
**Closure separation.** The closures of the strict truth set and the false
set meet only on the boundary level set:
  `closure (StrictTruth δ) ∩ closure (FalseSet δ) ⊆ TruthBoundary δ`.

Parallel to `safe_unsafe_separated` from `MoF_03`.
-/
theorem strictTruth_falseSet_separated
    [TopologicalSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ) :
    closure (StrictTruth δ) ∩ closure (FalseSet δ) ⊆ TruthBoundary δ := by
  intro x ⟨hx_true, hx_false⟩
  -- x ∈ closure {δ < 0} forces δ x ≤ 0
  have h_le : δ x ≤ 0 := by
    by_contra h
    push_neg at h
    have hopen : IsOpen (FalseSet δ) := falseSet_isOpen δ hδ
    have hx_in : x ∈ FalseSet δ := h
    rw [mem_closure_iff] at hx_true
    obtain ⟨y, hy_false, hy_true⟩ := hx_true _ hopen hx_in
    simp only [StrictTruth, FalseSet, Set.mem_setOf_eq] at hy_true hy_false
    linarith
  -- x ∈ closure {δ > 0} forces δ x ≥ 0
  have h_ge : δ x ≥ 0 := by
    by_contra h
    push_neg at h
    have hopen : IsOpen (StrictTruth δ) := strictTruth_isOpen δ hδ
    have hx_in : x ∈ StrictTruth δ := h
    rw [mem_closure_iff] at hx_false
    obtain ⟨y, hy_true, hy_false⟩ := hx_false _ hopen hx_in
    simp only [StrictTruth, FalseSet, Set.mem_setOf_eq] at hy_true hy_false
    linarith
  exact le_antisymm h_le h_ge

/-! ## 7. Strict truth is not closed on a connected space -/

/--
**Strict truth cannot be clopen.** On a connected space `QA`, if both a true
point and a false point exist, then `StrictTruth δ` is not closed: it is open
but not closed, so its closure must strictly contain it (and actually picks
up boundary points).

This is the standard clopen / connectedness argument.
-/
theorem strictTruth_not_closed
    [TopologicalSpace QA] [ConnectedSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ)
    (htrue : ∃ p, δ p < 0) (hfalse : ∃ p, δ p > 0) :
    ¬ IsClosed (StrictTruth δ) := by
  intro hclosed
  -- StrictTruth is also open, hence clopen
  have hopen : IsOpen (StrictTruth δ) := strictTruth_isOpen δ hδ
  have hclopen : IsClopen (StrictTruth δ) := ⟨hclosed, hopen⟩
  -- A clopen set in a connected space is ∅ or all of QA
  rcases isClopen_iff.mp hclopen with h_empty | h_univ
  · -- StrictTruth = ∅ contradicts existence of a true point
    obtain ⟨a, ha⟩ := htrue
    have : a ∈ (StrictTruth δ : Set QA) := ha
    rw [h_empty] at this
    exact this
  · -- StrictTruth = univ contradicts existence of a false point
    obtain ⟨b, hb⟩ := hfalse
    have : b ∈ (StrictTruth δ : Set QA) := h_univ ▸ mem_univ b
    simp only [StrictTruth, Set.mem_setOf_eq] at this
    linarith

/-! ## 8. Boundary point is in the closure of strict truth -/

/--
**Boundary point in closure of strict truth.** On a connected space with both
a true point and a false point, there exists a boundary point `z` (i.e.
`δ z = 0`) which is also a limit point of the strict truth set.

Proof: the strict truth set is open but not closed (item 7), hence its
closure strictly contains it. The closure of `{δ < 0}` is contained in
`{δ ≤ 0}` by continuity, so any point in `closure(StrictTruth) \ StrictTruth`
must lie on the boundary `{δ = 0}`.
-/
theorem boundary_point_in_closure_of_strictTruth
    [TopologicalSpace QA] [ConnectedSpace QA]
    (δ : QA → ℝ) (hδ : Continuous δ)
    (htrue : ∃ p, δ p < 0) (hfalse : ∃ p, δ p > 0) :
    ∃ z, δ z = 0 ∧ z ∈ closure (StrictTruth δ) := by
  -- Strict truth is open but not closed, so closure strictly contains it.
  have hssub : StrictTruth δ ⊂ closure (StrictTruth δ) := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨subset_closure, fun h_eq => ?_⟩
    have : IsClosed (StrictTruth δ) := h_eq ▸ isClosed_closure
    exact strictTruth_not_closed δ hδ htrue hfalse this
  obtain ⟨z, hz_cl, hz_not⟩ := Set.exists_of_ssubset hssub
  refine ⟨z, ?_, hz_cl⟩
  -- closure of {δ < 0} sits inside the closed set {δ ≤ 0}
  have hcl_subset : closure (StrictTruth δ) ⊆ TruthSet δ :=
    closure_minimal (fun _ (hx : δ _ < 0) => le_of_lt hx) (truthSet_isClosed δ hδ)
  have hz_le : δ z ≤ 0 := hcl_subset hz_cl
  -- z ∉ StrictTruth means δ z ≥ 0
  have hz_ge : (0 : ℝ) ≤ δ z := by
    by_contra hlt
    push_neg at hlt
    exact hz_not hlt
  linarith

/-! ## 9. Strict truth and false set are disjoint -/

/--
**Strict truth and false set are disjoint.** This is essentially definitional:
`δ p < 0` and `δ p > 0` cannot hold simultaneously.

This is the topological skeleton of the "two-component complement" picture:
once the truth boundary is removed, what remains splits cleanly between
strict-truth points (`δ < 0`) and false points (`δ > 0`).
-/
theorem strictTruth_falseSet_no_intersect
    (δ : QA → ℝ) :
    Disjoint (StrictTruth δ) (FalseSet δ) := by
  rw [Set.disjoint_iff]
  intro x ⟨hx_true, hx_false⟩
  simp only [StrictTruth, FalseSet, Set.mem_setOf_eq] at hx_true hx_false
  linarith

/-! ## Summary

| # | Statement | Status |
|---|-----------|--------|
| 1 | `truthSet_isClosed` — `{δ ≤ 0}` closed for continuous `δ` | Proved |
| 2 | `falseSet_isOpen` — `{δ > 0}` open for continuous `δ` | Proved |
| 3 | `strictTruth_isOpen` — `{δ < 0}` open for continuous `δ` | Proved |
| 4 | `truthBoundary_isClosed` — `{δ = 0}` closed | Proved |
| 5 | `truthBoundary_nonempty` — IVT on connected `QA` | Proved |
| 6 | `strictTruth_falseSet_separated` — closures meet on boundary | Proved |
| 7 | `strictTruth_not_closed` — clopen argument on connected `QA` | Proved |
| 8 | `boundary_point_in_closure_of_strictTruth` — boundary as limit | Proved |
| 9 | `strictTruth_falseSet_no_intersect` — disjointness | Proved |

All results are sorry-free and parameterized over an arbitrary topological
space `QA`, with connectedness assumed only where needed.
-/

end HoF

end
