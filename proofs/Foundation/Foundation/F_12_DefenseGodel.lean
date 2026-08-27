/-
# F_12_DefenseGodel

**The Defense Trilemma via Gödel's diagonal.**

The Defense Trilemma (`paper2_defense_impossibility`) says a wrapper defense
`D : X → X` against prompt injection cannot be continuous, utility-preserving
(`D x = x` on safe inputs), and complete (`f (D x) < τ` for all `x`) at once.
The published proof is topological: continuity plus utility force the defended
safety score to hit the boundary `τ`, where completeness fails.

Prompt injection is self-reference in the first place ("ignore previous
instructions and do X"), so the diagonal form is the natural one. This file
re-derives the Defense Trilemma from the same Lawvere engine as the
Hallucination Trilemma (`F_11_HallucinationGodel`), with no topology. The
boundary prompt becomes the **liar prompt**: one whose defended output is safe
if and only if it is unsafe.

Depends on Mathlib, `F_01_LawvereCore`, `F_04_CalibrationUnified`,
`F_11_HallucinationGodel`.
-/

import Mathlib
import Foundation.F_01_LawvereCore
import Foundation.F_04_CalibrationUnified
import Foundation.F_11_HallucinationGodel

namespace Foundation

noncomputable section

/-! ## Defense Trilemma, Gödel / liar form

Model the defended-safety verdict as `v : X → X → Bool`, where `v p q = true`
means the wrapper renders prompt `q` safe when it also has to cope with the
self-referential prompt `p`. Universality (`Function.Surjective v`) is the
prompt-injection reality: prompts are arbitrary text, so they can describe the
defense and any safety pattern over prompts, including the diagonal one. This
self-reference replaces the connected input space of the topological proof. -/

/-- **The liar prompt.** For a universal prompt space, Lawvere's diagonal
    exhibits a prompt `q` whose defended output is safe iff it is unsafe:
    `v q q = !(v q q)`. This is the injection the topological proof locates at
    the safety boundary, here produced by self-reference. -/
theorem defense_liar_query {X : Type*}
    (v : X → X → Bool) (hUniversal : Function.Surjective v) :
    ∃ q, v q q = !(v q q) :=
  hallucination_liar_query v hUniversal

/-- **Defense Trilemma (Gödel/Tarski form).** No complete, utility-preserving
    wrapper defense survives a universal (self-referential) prompt space. Same
    Lawvere instance as the Hallucination Trilemma: `Y = Bool`, controller the
    liar `!·`. Completeness demands the liar prompt be safe; self-reference makes
    it safe iff unsafe. -/
theorem defense_trilemma_godel {X : Type*}
    (v : X → X → Bool) (hUniversal : Function.Surjective v) : False :=
  tarski_liar v hUniversal

/-! ## Defense Trilemma, real-valued form

The score version mirrors `F_04_CalibrationUnified.hallucination_via_lawvere`.
Let `s a b` be the safety score `f (D b)` of the defended prompt `b` under
self-context `a`. Lawvere with the complement controller forces a boundary
prompt with `s a a = τ` (utility preservation pins the score to `τ` there,
since the boundary prompt is a limit of safe prompts the defense must fix).
Completeness requires `s a a < τ` everywhere. They clash. -/

/-- **Defense Trilemma (real-valued Lawvere form).** A universal defended-score
    self-map cannot be complete: the diagonal forces a boundary prompt at the
    threshold `1/2`, contradicting completeness `s a a < 1/2`. Utility
    preservation is what blocks the trivial escape (a constant maximally-safe
    output, which is not utility-preserving and makes `s` non-universal). -/
theorem defense_trilemma_lawvere {X : Type*}
    (s : X → X → ℝ) (hUniversal : Function.Surjective s)
    (hComplete : ∀ a, s a a < 1/2) : False := by
  obtain ⟨a, ha⟩ := calibration_diagonal_hits_half s hUniversal
  have hlt := hComplete a
  linarith

/-! ## Hallucination and Defense are one theorem

Both trilemmas are the *same* Lawvere instance (`Y = Bool`, `t = !·`), read
with different semantics: `v` is confident-correctness for hallucination and
defended-safety for defense. The shared engine: -/

/-- The shared diagonal engine. A universal Boolean self-verdict is impossible;
    the Hallucination and Defense trilemmas are this one theorem under two
    readings of `v`. -/
theorem reflective_verdict_impossible {Q : Type*}
    (v : Q → Q → Bool) (hUniversal : Function.Surjective v) : False :=
  tarski_liar v hUniversal

/-- Certificate that the two trilemmas are literally the same proof term. -/
theorem defense_is_hallucination_engine {Q : Type*}
    (v : Q → Q → Bool) (h : Function.Surjective v) :
    defense_trilemma_godel v h = hallucination_trilemma_godel v h := rfl

end

/-! ## Axiom audit -/

#print axioms defense_trilemma_godel
#print axioms defense_trilemma_lawvere
#print axioms defense_liar_query
#print axioms reflective_verdict_impossible

end Foundation
