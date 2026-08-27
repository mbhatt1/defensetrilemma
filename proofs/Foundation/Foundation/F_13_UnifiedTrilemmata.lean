/-
# F_13_UnifiedTrilemmata

**One diagonal, three trilemmata.**

The Hallucination Trilemma (`F_11`), the Defense Trilemma (`F_12`), and the
truth-boundary coupling theorem ("Truth Has a Boundary") are not three results
that happen to rhyme. Read the right way they are a single Lawvere instance:
`Y = Bool`, controller the liar `!·`, engine `F_01_LawvereCore`. The only thing
that changes across the three is what the Boolean self-verdict `v : Q → Q → Bool`
is *about*.

* Hallucination: `v p q` = "confident and correct about query `q`."
* Defense:       `v p q` = "prompt `q` rendered safe by the wrapper."
* Coupling:      `v p q` = "confidence places `q` on the true side."

In each case universality of `v` (self-reference) is the hypothesis that in the
topological proofs is supplied by connectedness of the domain, and in each case
the liar diagonal produces the boundary object the IVT would.

Depends on Mathlib and `F_01`, `F_11`, `F_12`.
-/

import Mathlib
import Foundation.F_01_LawvereCore
import Foundation.F_11_HallucinationGodel
import Foundation.F_12_DefenseGodel

namespace Foundation

noncomputable section

/-! ## The abstract schema

A *reflective verdict* on a domain `Q` is a Boolean self-application
`v : Q → Q → Bool` that is surjective. The single theorem below is the whole
content; the three named trilemmata are its readings. -/

/-- **The trilemma schema.** No reflective (surjective) Boolean self-verdict
    exists. This is `F_01`'s Lawvere with `t = !·`, i.e. Tarski's liar, and it is
    the shared core of every trilemma in this development. -/
theorem no_reflective_verdict {Q : Type*}
    (v : Q → Q → Bool) (hUniversal : Function.Surjective v) : False :=
  tarski_liar v hUniversal

/-- The boundary object the schema always produces: a self-negating query,
    `v q q = !(v q q)`. Hallucination's boundary question, defense's liar
    prompt, and coupling's coupled point are all this one witness. -/
theorem schema_boundary {Q : Type*}
    (v : Q → Q → Bool) (hUniversal : Function.Surjective v) :
    ∃ q, v q q = !(v q q) :=
  lawvere_diagonal v hUniversal (fun b => !b)

/-! ## The three readings

Each is definitionally the schema, so the certificates below are `rfl`. -/

/-- Truth-boundary coupling ("Truth Has a Boundary"), Gödel form: if a model's
    truth-separating verdict over its representation space is universal, a
    self-referential query is forced onto the truth boundary. Same engine. -/
theorem coupling_trilemma_godel {X : Type*}
    (v : X → X → Bool) (hUniversal : Function.Surjective v) : False :=
  no_reflective_verdict v hUniversal

/-- All three trilemmata are the same proof term. -/
theorem trilemmata_unified {Q : Type*}
    (v : Q → Q → Bool) (h : Function.Surjective v) :
    hallucination_trilemma_godel v h = defense_trilemma_godel v h
      ∧ defense_trilemma_godel v h = coupling_trilemma_godel v h :=
  ⟨rfl, rfl⟩

end

/-! ## Axiom audit -/

#print axioms no_reflective_verdict
#print axioms coupling_trilemma_godel
#print axioms trilemmata_unified

end Foundation
