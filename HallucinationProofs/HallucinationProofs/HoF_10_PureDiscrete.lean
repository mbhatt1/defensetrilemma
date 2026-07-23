import Mathlib
import HallucinationProofs.HoF_07_TrilemmaCore

/-!
# Hallucination Trilemma — Part 10: Pure Discrete Impossibility

This file proves the **pure discrete** version of the Hallucination Trilemma.

Unlike `HoF_09_Discrete` (which uses `Fintype Q`, `DecidableEq`, a "decisive"
assumption, and a path-based discrete IVT), the results here require:

* **No topology** on `Q` or `A`.
* **No finiteness** of `Q`.
* **No path structure** or sequence assumptions.
* **No "decisive" assumption** (conf ≠ 1/2 everywhere).

The proof is purely propositional: it follows from the definitions of
`TrilemmaFaithful` and `StrictCalibrated` by two `linarith` steps.

## The key insight

Under `StrictCalibrated`:

  `conf(q) > 1/2 ↔ δ(q) < 0`    ... (Cal₁)
  `conf(q) < 1/2 ↔ δ(q) > 0`    ... (Cal₂)

Taking contrapositives:

  `δ(q) ≥ 0 ↔ conf(q) ≤ 1/2`   (from Cal₁)
  `δ(q) ≤ 0 ↔ conf(q) ≥ 1/2`   (from Cal₂)

So at a **boundary question** `q*` with `δ(q*) = 0`:

  `δ(q*) ≥ 0` ⟹ `conf(q*) ≤ 1/2`
  `δ(q*) ≤ 0` ⟹ `conf(q*) ≥ 1/2`

Hence `conf(q*) = 1/2`.

`TrilemmaFaithful` then gives `conf(q*) ≥ 1/2 → δ(q*) < 0`.
But `δ(q*) = 0`. Contradiction.

## Main results

1. `boundary_conf_half` — calibration alone forces `conf(q*) = 1/2` at any
   boundary question.

2. `boundary_question_impossible` — faithful + calibrated + any boundary
   question → `False`. No coverage hypothesis needed.

3. `three_sided_impossible` — the trilemma with **three-sided coverage**
   (witnesses for `δ < 0`, `δ = 0`, `δ > 0`) is impossible without any
   topological assumptions.

4. `continuous_reduces_to_pure_discrete` — the continuous trilemma
   (`HoF_07_TrilemmaCore.hallucination_trilemma`) factors through
   `boundary_question_impossible`: IVT constructs the boundary question;
   the discrete lemma delivers the contradiction. This shows the continuous
   and discrete results share the same logical core.

All proofs are sorry-free.
-/

open Set

noncomputable section

namespace HoF

/-! ## 1. The core lemma: calibration forces conf = 1/2 at δ = 0 -/

/--
**Boundary confidence pinning.**

If `M` is strictly calibrated and `δ(q*, ans(q*)) = 0`, then
`conf(q*) = 1/2`.

This is a purely logical consequence of the two biconditionals in
`StrictCalibrated` — no topology, no continuity, no finiteness.
-/
theorem boundary_conf_half
    {Q A : Type*}
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (hCal : StrictCalibrated M δ)
    (q : Q)
    (hbdy : δ (q, (M q).1) = 0) :
    (M q).2 = 1/2 := by
  have hCal_q := hCal q
  -- δ = 0 means ¬ (δ < 0), so Cal₁ backwards: ¬ (conf > 1/2)
  have h_not_gt : ¬ (M q).2 > 1/2 := by
    intro h
    have hδ_neg : δ (q, (M q).1) < 0 := hCal_q.1.mp h
    linarith
  -- δ = 0 means ¬ (δ > 0), so Cal₂ backwards: ¬ (conf < 1/2)
  have h_not_lt : ¬ (M q).2 < 1/2 := by
    intro h
    have hδ_pos : δ (q, (M q).1) > 0 := hCal_q.2.mp h
    linarith
  -- Squeeze: conf = 1/2
  exact le_antisymm (not_lt.mp h_not_gt) (not_lt.mp h_not_lt)

/-! ## 2. Main discrete impossibility -/

/--
**Pure Discrete Hallucination Impossibility.**

A model that is faithful and strictly calibrated cannot handle any
truth-boundary question: the existence of a single `q*` with
`δ(q*, ans(q*)) = 0` yields `False`.

**Hypotheses:**
- `hF : TrilemmaFaithful M δ` — high-confidence ⇒ strictly correct
- `hCal : StrictCalibrated M δ` — confidence sign ↔ truth sign, strictly
- `q₀ : Q` — a witness question
- `hbdy : δ (q₀, ans(q₀)) = 0` — the answer sits exactly on the truth boundary

**No topology. No continuity. No finiteness. No path. No "decisive" assumption.**
The proof is two `linarith` calls.
-/
theorem boundary_question_impossible
    {Q A : Type*}
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (hF : TrilemmaFaithful M δ)
    (hCal : StrictCalibrated M δ)
    (q₀ : Q)
    (hbdy : δ (q₀, (M q₀).1) = 0) :
    False := by
  -- Step 1: calibration pins conf(q₀) = 1/2
  have hconf : (M q₀).2 = 1/2 := boundary_conf_half M δ hCal q₀ hbdy
  -- Step 2: faithfulness demands δ(q₀) < 0
  have hge : (M q₀).2 ≥ 1/2 := ge_of_eq hconf
  have hlt : δ (q₀, (M q₀).1) < 0 := hF q₀ hge
  -- Step 3: contradiction with δ(q₀) = 0
  linarith

/-! ## 3. Three-sided coverage trilemma -/

/--
**Three-Sided Coverage.**

Witnesses for all three truth regions: strict truth (`δ < 0`), truth
boundary (`δ = 0`), and falsity (`δ > 0`).

In the continuous setting (\Cref{HoF_07}), two-sided coverage on a
connected space forces boundary existence via the IVT. Here we state it
as an explicit hypothesis, making the discrete result self-contained.
-/
def ThreeSidedCovering {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  (∃ q, δ (q, (M q).1) < 0) ∧
  (∃ q, δ (q, (M q).1) = 0) ∧
  (∃ q, δ (q, (M q).1) > 0)

/--
**Discrete Hallucination Trilemma (three-sided coverage form).**

No model can simultaneously satisfy `TrilemmaFaithful`, `StrictCalibrated`,
and `ThreeSidedCovering`.

This is a purely set-theoretic impossibility: no topology, no metric,
no finiteness, no paths. The boundary witness from `ThreeSidedCovering`
immediately feeds `boundary_question_impossible`.

**Comparison with the continuous trilemma:**
In `HoF_07_TrilemmaCore.hallucination_trilemma`, two-sided coverage
(`TrilemmaCovering`) suffices because IVT on the connected question space
constructs the boundary witness automatically. Here, we supply it directly —
trading the topological hypothesis (connectedness) for a stronger coverage
hypothesis (three-sided). The logical core is identical.
-/
theorem discrete_hallucination_trilemma
    {Q A : Type*}
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (hF : TrilemmaFaithful M δ)
    (hCal : StrictCalibrated M δ)
    (hC : ThreeSidedCovering M δ) :
    False := by
  obtain ⟨_, ⟨q₀, hbdy⟩, _⟩ := hC
  exact boundary_question_impossible M δ hF hCal q₀ hbdy

/-! ## 4. Characterisation: faithful ↔ boundary-free (under calibration) -/

/--
**Faithfulness characterisation.**

Under strict calibration, the following are equivalent:
(a) The model is faithful (`TrilemmaFaithful`).
(b) The model has no truth-boundary questions: `∀ q, δ(q, ans(q)) ≠ 0`.

This is the exact discrete analogue of the continuous boundary fixation
result: faithfulness is precisely the condition that excludes boundary
questions.
-/
theorem faithful_iff_boundary_free
    {Q A : Type*}
    (M : Q → A × ℝ)
    (δ : Q × A → ℝ)
    (hCal : StrictCalibrated M δ) :
    TrilemmaFaithful M δ ↔ ∀ q, δ (q, (M q).1) ≠ 0 := by
  constructor
  · -- (a → b) If faithful, no boundary questions
    intro hF q hbdy
    exact boundary_question_impossible M δ hF hCal q hbdy
  · -- (b → a) If boundary-free, then faithful
    intro hno_bdy q hge
    -- conf(q) ≥ 1/2: either conf > 1/2 or conf = 1/2.
    by_cases h : (M q).2 > 1/2
    · -- conf > 1/2: calibration directly gives δ < 0.
      exact (hCal q).1.mp h
    · -- conf = 1/2 (conf ≥ 1/2 and ¬ conf > 1/2).
      have hconf : (M q).2 = 1/2 := le_antisymm (not_lt.mp h) hge
      -- Calibration forces δ(q) = 0 (same squeeze as boundary_conf_half).
      have hδ_not_neg : ¬ δ (q, (M q).1) < 0 := fun hlt =>
        absurd ((hCal q).1.mpr hlt) (by linarith)
      have hδ_not_pos : ¬ δ (q, (M q).1) > 0 := fun hpos =>
        absurd ((hCal q).2.mpr hpos) (by linarith)
      have hδ_zero : δ (q, (M q).1) = 0 :=
        le_antisymm (not_lt.mp hδ_not_pos) (not_lt.mp hδ_not_neg)
      -- boundary-free hypothesis contradicts δ(q) = 0.
      exact (hno_bdy q hδ_zero).elim

/-! ## 5. The continuous impossibility factors through the discrete -/

/--
**Factorisation lemma.**

The continuous `hallucination_trilemma` (from `HoF_07_TrilemmaCore`) can be
decomposed into two steps:

1. IVT step: Coverage + Connectedness → `∃ q₀, δ_M(q₀) = 0` (boundary exists).
2. Discrete step: Faithful + Calibrated + `δ_M(q₀) = 0` → `False`.

The second step is `boundary_question_impossible`. This file provides the
discrete core; the IVT wrapper lives in `HoF_07`.

We state the factorisation as a direct proof of the continuous trilemma
using `boundary_question_impossible` as the final step.
-/
theorem hallucination_trilemma_via_pure_discrete
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
  -- IVT step: extract boundary question from two-sided coverage
  obtain ⟨q₀, _, hbdy⟩ :=
    hallucination_trilemma_strict M δ hM_ans hM_conf hδ hC hCal
  -- Discrete step: boundary question + faithful + calibrated → False
  exact boundary_question_impossible M δ hF hCal q₀ hbdy

/-! ## 6. Summary

| Theorem | Hypotheses | Says |
|---------|------------|------|
| `boundary_conf_half` | Calibrated, `δ(q*) = 0` | `conf(q*) = 1/2` |
| `boundary_question_impossible` | Faithful, Calibrated, `δ(q*) = 0` | `False` |
| `discrete_hallucination_trilemma` | Faithful, Calibrated, Three-Sided Coverage | `False` |
| `faithful_iff_boundary_free` | Calibrated | Faithful ↔ no `δ = 0` questions |
| `hallucination_trilemma_via_pure_discrete` | Continuous trilemma hypotheses | `False` |

**The logical structure:**

```
Continuous case:    Coverage + Connectedness ──(IVT)──→ ∃q₀ with δ(q₀)=0
                                                              │
Discrete core:  Faithful + Calibrated + δ(q₀)=0 ──────→ False
```

The discrete core (`boundary_question_impossible`) is the trapped result:
it requires no topology, no metric, no finiteness, no path, no decisive
assumption. Any model that is simultaneously faithful and strictly calibrated
has no boundary questions — and the continuous IVT (or three-sided coverage)
supplies one.
-/

end HoF

end
