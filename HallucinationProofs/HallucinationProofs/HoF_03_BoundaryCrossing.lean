import Mathlib

/-
  HoF_03_BoundaryCrossing.lean

  Part 3 of the "Hallucination Trilemma" formalization.

  **Core result: The model truth boundary cannot be avoided.**

  Setup:
    * `Q` — question space (a topological space; connected when needed)
    * `A` — answer space
    * `M : Q → A × ℝ` — a model returning an answer and a confidence
    * `δ : Q × A → ℝ` — truth-distance; truth set `T = {δ ≤ 0}`,
      boundary `∂T = {δ = 0}`
    * `q ↦ δ(q, (M q).1)` — the *model truth-distance composite*

  This file develops the IVT-style boundary-crossing arguments which
  underlie the topological obstruction in the Hallucination Trilemma.
  Each result mirrors the corresponding lemma in
  `MoF_03_ThresholdCrossing.lean`, restated for the model composite.

  Contents:

    1. `confidence_path_crosses_half` — IVT on ℝ at the threshold 1/2.
    2. `path_crosses_truth_boundary` — IVT along a path for the
       model truth-distance composite.
    3. `model_truth_boundary_nonempty` — connected-space crossing for
       the model: if δ takes both signs along `q ↦ (M q).1`, then
       there exists a question on the truth boundary.
    4. `model_confidence_half_set_nonempty` — parallel statement for
       the confidence component crossing 1/2.
    5. `confidence_half_nonempty` — generalized version: any continuous
       `c : Q → ℝ` on a connected space straddling 1/2 hits 1/2.
    6. `model_truth_boundary_isClosed` — the model truth boundary is
       a closed subset of `Q`.
-/

noncomputable section

open Set Topology

namespace HoF

/-! ## 1. Confidence Path Crosses 1/2 (IVT on ℝ) -/

/--
**IVT on ℝ at threshold 1/2.** If `c : ℝ → ℝ` is continuous,
`c a < 1/2`, `c b > 1/2`, and `a ≤ b`, then there exists
`t ∈ [a, b]` with `c t = 1/2`.

This is the one-dimensional intermediate value theorem applied at the
canonical confidence threshold of 1/2.
-/
theorem confidence_path_crosses_half
    (c : ℝ → ℝ) (hc : Continuous c) (a b : ℝ)
    (hab : a ≤ b) (ha : c a < 1/2) (hb : c b > 1/2) :
    ∃ t ∈ Set.Icc a b, c t = 1/2 := by
  have h_conn : IsPreconnected (Set.Icc a b) := isPreconnected_Icc
  have ha_mem : a ∈ Set.Icc a b := left_mem_Icc.mpr hab
  have hb_mem : b ∈ Set.Icc a b := right_mem_Icc.mpr hab
  obtain ⟨t, ht_mem, ht_eq⟩ := h_conn.intermediate_value₂ ha_mem hb_mem
    hc.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)
  exact ⟨t, ht_mem, ht_eq⟩

/-! ## 2. IVT Along a Path for the Model Truth-Distance Composite -/

/--
**Generic IVT for the model truth-distance composite.**

Let `Q`, `A` be topological spaces, `δ : Q × A → ℝ` the truth-distance,
`M : Q → A × ℝ` a model with continuous answer-component, and
`γ : ℝ → Q` a continuous path. If

  * `δ(γ(a), M(γ(a)).1) < 0` (answer is *inside* the truth set), and
  * `δ(γ(b), M(γ(b)).1) > 0` (answer is *outside* the truth set),

then there exists `t ∈ [a, b]` for which the model's answer lies
*exactly* on the truth boundary, i.e. `δ(γ(t), (M(γ(t))).1) = 0`.

Proof: apply the one-dimensional IVT to the continuous composite
`t ↦ δ(γ(t), (M(γ(t))).1)`.
-/
theorem path_crosses_truth_boundary
    {Q A : Type*} [TopologicalSpace Q] [TopologicalSpace A]
    (δ : Q × A → ℝ) (hδ : Continuous δ)
    (M : Q → A × ℝ) (hM : Continuous (fun q => (M q).1))
    (γ : ℝ → Q) (hγ : Continuous γ)
    (a b : ℝ) (hab : a ≤ b)
    (ha : δ (γ a, (M (γ a)).1) < 0) (hb : δ (γ b, (M (γ b)).1) > 0) :
    ∃ t ∈ Set.Icc a b, δ (γ t, (M (γ t)).1) = 0 := by
  -- The composite map t ↦ δ(γ t, (M (γ t)).1)
  set f : ℝ → ℝ := fun t => δ (γ t, (M (γ t)).1) with hf_def
  -- Continuity of t ↦ γ t is hγ; continuity of q ↦ (M q).1 is hM.
  -- Their composition gives continuity of t ↦ (M (γ t)).1.
  have hM_circ_γ : Continuous (fun t : ℝ => (M (γ t)).1) := hM.comp hγ
  -- Pair continuity: t ↦ (γ t, (M (γ t)).1)
  have h_pair : Continuous (fun t : ℝ => (γ t, (M (γ t)).1)) :=
    hγ.prodMk hM_circ_γ
  -- Then composing with δ gives continuity of f.
  have hf : Continuous f := hδ.comp h_pair
  -- Apply IVT on ℝ at threshold 0.
  have h_conn : IsPreconnected (Set.Icc a b) := isPreconnected_Icc
  have ha_mem : a ∈ Set.Icc a b := left_mem_Icc.mpr hab
  have hb_mem : b ∈ Set.Icc a b := right_mem_Icc.mpr hab
  obtain ⟨t, ht_mem, ht_eq⟩ := h_conn.intermediate_value₂ ha_mem hb_mem
    hf.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)
  exact ⟨t, ht_mem, ht_eq⟩

/-! ## 3. Model Truth Boundary is Nonempty on a Connected Space -/

/--
**Connected-space crossing for the model.**

If `Q` is a *connected* topological space, `δ : Q × A → ℝ` is
continuous, and the model's answer-component `q ↦ (M q).1` is
continuous, then whenever there exist `q₁, q₂ ∈ Q` with

  * `δ(q₁, (M q₁).1) < 0`, and
  * `δ(q₂, (M q₂).1) > 0`,

there must exist `q ∈ Q` with `δ(q, (M q).1) = 0`.

Equivalently: if the model is ever *truthful* and ever *false*, then
its truth-boundary level set is nonempty. This is the workhorse
result powering the topological obstruction.
-/
theorem model_truth_boundary_nonempty
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (δ : Q × A → ℝ) (hδ : Continuous δ)
    (M : Q → A × ℝ) (hM_ans : Continuous (fun q => (M q).1))
    (q₁ q₂ : Q)
    (h₁ : δ (q₁, (M q₁).1) < 0) (h₂ : δ (q₂, (M q₂).1) > 0) :
    ∃ q, δ (q, (M q).1) = 0 := by
  -- The composite F : Q → ℝ given by F q = δ(q, (M q).1) is continuous.
  set F : Q → ℝ := fun q => δ (q, (M q).1) with hF_def
  have h_pair : Continuous (fun q : Q => (q, (M q).1)) :=
    continuous_id.prodMk hM_ans
  have hF : Continuous F := hδ.comp h_pair
  -- Apply preconnectedness of `univ` and IVT.
  have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
  have h₁_mem : q₁ ∈ (Set.univ : Set Q) := Set.mem_univ _
  have h₂_mem : q₂ ∈ (Set.univ : Set Q) := Set.mem_univ _
  obtain ⟨q, _, hq⟩ := h_conn.intermediate_value₂ h₁_mem h₂_mem
    hF.continuousOn continuous_const.continuousOn (le_of_lt h₁) (le_of_lt h₂)
  exact ⟨q, hq⟩

/-! ## 4. Confidence Boundary Crossing (Model Form) -/

/--
**Confidence half-set is nonempty.**

If `M : Q → ℝ × ℝ` has a continuous confidence-component
`q ↦ (M q).2`, and there exist `q₁, q₂ ∈ Q` with confidences below
and above 1/2 respectively, then there exists `q ∈ Q` whose
confidence is exactly 1/2.

(The product type `ℝ × ℝ` is a placeholder — only the second
component is used. The point is to display the IVT skeleton for the
confidence map.)
-/
theorem model_confidence_half_set_nonempty
    {Q : Type*} [TopologicalSpace Q] [ConnectedSpace Q]
    (M : Q → ℝ × ℝ) (hM_conf : Continuous (fun q => (M q).2))
    (q₁ q₂ : Q)
    (h₁ : (M q₁).2 < 1/2) (h₂ : (M q₂).2 > 1/2) :
    ∃ q, (M q).2 = 1/2 := by
  have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
  have h₁_mem : q₁ ∈ (Set.univ : Set Q) := Set.mem_univ _
  have h₂_mem : q₂ ∈ (Set.univ : Set Q) := Set.mem_univ _
  obtain ⟨q, _, hq⟩ := h_conn.intermediate_value₂ h₁_mem h₂_mem
    hM_conf.continuousOn continuous_const.continuousOn
    (le_of_lt h₁) (le_of_lt h₂)
  exact ⟨q, hq⟩

/-! ## 5. Generalized Confidence Crossing -/

/--
**Generalized confidence crossing (the form actually used downstream).**

For any continuous `c : Q → ℝ` on a connected space `Q`, if there
exist `q₁, q₂ ∈ Q` with `c q₁ < 1/2 < c q₂`, then there exists
`q ∈ Q` with `c q = 1/2`.

This is the IVT specialized to the confidence threshold.
-/
theorem confidence_half_nonempty
    {Q : Type*} [TopologicalSpace Q] [ConnectedSpace Q]
    (c : Q → ℝ) (hc : Continuous c)
    (q₁ q₂ : Q) (h₁ : c q₁ < 1/2) (h₂ : c q₂ > 1/2) :
    ∃ q, c q = 1/2 := by
  have h_conn : IsPreconnected (Set.univ : Set Q) := isPreconnected_univ
  have h₁_mem : q₁ ∈ (Set.univ : Set Q) := Set.mem_univ _
  have h₂_mem : q₂ ∈ (Set.univ : Set Q) := Set.mem_univ _
  obtain ⟨q, _, hq⟩ := h_conn.intermediate_value₂ h₁_mem h₂_mem
    hc.continuousOn continuous_const.continuousOn (le_of_lt h₁) (le_of_lt h₂)
  exact ⟨q, hq⟩

/-! ## 6. Closedness of the Model Truth Boundary -/

/--
**Closedness of the model truth boundary.**

For any topological spaces `Q`, `A`, continuous truth-distance
`δ : Q × A → ℝ`, and model `M : Q → A × ℝ` with continuous
answer-component, the model truth-boundary set

  `{q ∈ Q | δ(q, (M q).1) = 0}`

is a *closed* subset of `Q`.
-/
theorem model_truth_boundary_isClosed
    {Q A : Type*} [TopologicalSpace Q] [TopologicalSpace A]
    (δ : Q × A → ℝ) (hδ : Continuous δ)
    (M : Q → A × ℝ) (hM_ans : Continuous (fun q => (M q).1)) :
    IsClosed {q : Q | δ (q, (M q).1) = 0} := by
  -- Build the continuous composite F.
  have h_pair : Continuous (fun q : Q => (q, (M q).1)) :=
    continuous_id.prodMk hM_ans
  have hF : Continuous (fun q : Q => δ (q, (M q).1)) := hδ.comp h_pair
  -- The level set {F = 0} is the preimage of the closed singleton {0}.
  have h_eq :
      {q : Q | δ (q, (M q).1) = 0} =
        (fun q : Q => δ (q, (M q).1)) ⁻¹' ({0} : Set ℝ) := by
    ext q; simp [Set.mem_preimage, Set.mem_singleton_iff]
  rw [h_eq]
  exact isClosed_singleton.preimage hF

/-! ## Summary

| # | Statement                                     | Status |
|---|-----------------------------------------------|--------|
| 1 | `confidence_path_crosses_half` (IVT on ℝ)     | Proved |
| 2 | `path_crosses_truth_boundary` (IVT along γ)   | Proved |
| 3 | `model_truth_boundary_nonempty` (connected Q) | Proved |
| 4 | `model_confidence_half_set_nonempty`          | Proved |
| 5 | `confidence_half_nonempty` (general c : Q→ℝ)  | Proved |
| 6 | `model_truth_boundary_isClosed` (any Q, A)    | Proved |

All results are sorry-free. Each proof reduces to a direct
application of `IsPreconnected.intermediate_value₂` and continuity
of compositions / products, mirroring `MoF_03_ThresholdCrossing.lean`
but specialized to the model truth-distance composite
`q ↦ δ(q, (M q).1)`.
-/

end HoF
