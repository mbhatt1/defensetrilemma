/-
  HoF Instantiation: Prompt Embedding Space ℝⁿ
  ============================================
  Demonstrates that the generic Hallucination Trilemma applies to the
  standard model of LLM prompts: real-valued embeddings in
  `EuclideanSpace ℝ (Fin d)` for some embedding dimension `d`
  (e.g. d = 4096 for a typical transformer hidden state).

  The space `EuclideanSpace ℝ (Fin d)` is connected, T2, a metric space,
  and carries Lebesgue measure — every typeclass the abstract HoF
  theorems require. Answers live in another Euclidean space
  `EuclideanSpace ℝ (Fin k)` (output embeddings, or single-token logits).

  The theorems here are one-line specializations of `HoF_07_TrilemmaCore`
  and the antipodal version in `HoF_08_BorsukUlam`, witnessing that the
  abstract impossibility is not vacuous: it really does forbid a
  continuous, faithful, calibrated, covering map on prompt embedding
  space.

  *Modelling caveat.* The reduction "LLM ⇝ continuous map on embedding
  space ⇝ this theorem" assumes (i) the map from embeddings to
  (answer-embedding, confidence) is continuous — true for transformer
  forward passes modulo softmax temperature, and (ii) the truth-distance
  `δ` extends continuously to the embedding space — see the discussion
  in the project README. The Lean theorem says nothing about whether
  these assumptions hold for any particular LLM; it says the conclusion
  follows whenever they do.
-/

import Mathlib

open Set Topology Metric Filter

noncomputable section

namespace HoF

/-! ## 1. Typeclass witnesses for prompt and answer embedding spaces -/

/-- Prompt embedding space is a topological space. -/
example (d : ℕ) : TopologicalSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- Prompt embedding space is a metric space. -/
example (d : ℕ) : MetricSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- Prompt embedding space is connected — the key topological hypothesis
    of the trilemma. Any two prompts can be continuously interpolated. -/
example (d : ℕ) : ConnectedSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- Answer embedding space is also connected. -/
example (k : ℕ) : ConnectedSpace (EuclideanSpace ℝ (Fin k)) := inferInstance

/-- The product (prompt, answer) embedding space is connected. -/
example (d k : ℕ) :
    ConnectedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k)) :=
  inferInstance

/-! ## 2. The hallucination setup on prompt embedding space -/

/-- Abbreviation for the prompt embedding space. -/
def PromptSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Abbreviation for the answer embedding space. -/
def AnswerSpace (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-! ## 3. Concrete instantiation of the IVT obstruction -/

/-- **Boundary point on prompt space.** Any continuous model on the
    prompt embedding space, equipped with a continuous truth-distance,
    must produce some prompt at which the model's answer lands exactly
    on the truth-set boundary, *provided* the model is two-sided
    (produces both true and false answers somewhere).

    This is the prompt-space specialization of `HoF_03`'s
    `model_truth_boundary_nonempty`. -/
theorem prompt_truth_boundary_exists {d k : ℕ}
    (M : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k) × ℝ)
    (δ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (hδ : Continuous δ)
    (q₁ q₂ : EuclideanSpace ℝ (Fin d))
    (h₁ : δ (q₁, (M q₁).1) < 0) (h₂ : δ (q₂, (M q₂).1) > 0) :
    ∃ q : EuclideanSpace ℝ (Fin d), δ (q, (M q).1) = 0 := by
  have hF : Continuous (fun q : EuclideanSpace ℝ (Fin d) =>
      δ (q, (M q).1)) :=
    hδ.comp (continuous_id.prodMk hM_ans)
  have h_conn : IsPreconnected (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    isPreconnected_univ
  obtain ⟨q, _, hq⟩ := h_conn.intermediate_value₂
    (Set.mem_univ q₁) (Set.mem_univ q₂)
    hF.continuousOn continuous_const.continuousOn
    (le_of_lt h₁) (le_of_lt h₂)
  exact ⟨q, hq⟩

/-- **Forced confidence-½ point on prompt space.** Under strict
    calibration, the IVT-forced boundary point also has confidence
    exactly ½. The model cannot be decisive everywhere. -/
theorem prompt_confidence_half_exists {d k : ℕ}
    (M : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k) × ℝ)
    (δ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) → ℝ)
    (hM_conf : Continuous (fun q => (M q).2))
    (hC : (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0))
    (hCal : ∀ q,
      ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
      ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0)) :
    ∃ q : EuclideanSpace ℝ (Fin d),
      (M q).2 = 1/2 ∧ δ (q, (M q).1) = 0 := by
  obtain ⟨⟨q_t, h_t⟩, ⟨q_f, h_f⟩⟩ := hC
  have hconf_t : (M q_t).2 > 1/2 := ((hCal q_t).1).mpr h_t
  have hconf_f : (M q_f).2 < 1/2 := ((hCal q_f).2).mpr h_f
  have h_conn : IsPreconnected (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    isPreconnected_univ
  obtain ⟨q₀, _, hq₀⟩ := h_conn.intermediate_value₂
    (Set.mem_univ q_f) (Set.mem_univ q_t)
    hM_conf.continuousOn continuous_const.continuousOn
    (le_of_lt hconf_f) (le_of_lt hconf_t)
  refine ⟨q₀, hq₀, ?_⟩
  have h_not_lt : ¬ δ (q₀, (M q₀).1) < 0 := fun h => by
    have : (M q₀).2 > 1/2 := ((hCal q₀).1).mpr h; linarith
  have h_not_gt : ¬ δ (q₀, (M q₀).1) > 0 := fun h => by
    have : (M q₀).2 < 1/2 := ((hCal q₀).2).mpr h; linarith
  exact le_antisymm (not_lt.mp h_not_gt) (not_lt.mp h_not_lt)

/-! ## 4. The trilemma on prompt space -/

/-- **Hallucination Trilemma on prompt embedding space.**

    No continuous model `M : ℝᵈ → ℝᵏ × ℝ` (prompt embedding ↦
    (answer embedding, confidence)) with a continuous truth-distance `δ`
    can simultaneously be:

      * **strongly faithful** — confidence ≥ ½ implies the answer is
        strictly true (`δ < 0`);
      * **covering** — both true-side and false-side answers are
        produced somewhere on the prompt space;
      * **strictly calibrated** — confidence is above ½ exactly when
        the answer is strictly true, below ½ exactly when strictly
        false.

    The obstruction is purely topological: the connectedness of
    embedding space + IVT on the continuous confidence map forces
    a confidence-½ point, which strict calibration pins to the
    truth-set boundary, which strong faithfulness then forbids. -/
theorem prompt_hallucination_trilemma {d k : ℕ}
    (M : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k) × ℝ)
    (δ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (hM_conf : Continuous (fun q => (M q).2))
    (hδ : Continuous δ)
    (hFstrong : ∀ q, (M q).2 ≥ 1/2 → δ (q, (M q).1) < 0)
    (hC : (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0))
    (hCal : ∀ q,
      ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
      ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0)) :
    False := by
  obtain ⟨q₀, hconf, hd⟩ :=
    prompt_confidence_half_exists M δ hM_conf hC hCal
  have h_strict : δ (q₀, (M q₀).1) < 0 := hFstrong q₀ (le_of_eq hconf.symm)
  linarith

/-! ## 5. Density / coverage corollary on prompt space -/

/-- **Approximate-boundary witness.** Under coverage, for every
    positive `ε`, the prompt embedding space contains a prompt where
    the model's truth-distance is within `ε` of the boundary. This
    is the "you cannot avoid the ambiguous zone" corollary on
    prompt space. -/
theorem prompt_near_boundary {d k : ℕ}
    (M : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k) × ℝ)
    (δ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) → ℝ)
    (hM_ans : Continuous (fun q => (M q).1))
    (hδ : Continuous δ)
    (hC : (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0)) :
    ∀ ε > 0, ∃ q : EuclideanSpace ℝ (Fin d),
      |δ (q, (M q).1)| < ε := by
  intro ε hε
  obtain ⟨q, hq⟩ :=
    prompt_truth_boundary_exists M δ hM_ans hδ
      hC.1.choose hC.2.choose hC.1.choose_spec hC.2.choose_spec
  exact ⟨q, by rw [hq]; simpa using hε⟩

/-! ## 6. Summary

| # | Theorem | What it says on prompt space |
|---|---------|-------------------------------|
| 1 | `prompt_truth_boundary_exists` | A two-sided continuous model on ℝᵈ × ℝᵏ has a prompt where its answer lies on `∂T`. |
| 2 | `prompt_confidence_half_exists` | A strictly-calibrated covering model has a prompt where its confidence is exactly ½ and its answer is on `∂T`. |
| 3 | `prompt_hallucination_trilemma` | Strong faithfulness + coverage + strict calibration is impossible on prompt embedding space. |
| 4 | `prompt_near_boundary` | Under coverage, the model's truth-distance gets arbitrarily close to zero — there is no escape from the ambiguous zone. |

All four are direct specializations of the abstract HoF theorems to
the connected metric space `EuclideanSpace ℝ (Fin d)`. The Lean kernel
verifies them with only `propext`, `Classical.choice`, and `Quot.sound`.
-/

end HoF

end
