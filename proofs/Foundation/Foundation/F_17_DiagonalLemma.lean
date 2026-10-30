/-
# F_17_DiagonalLemma

**Reflectivity is FORCED, not assumed: a discrete Gödel/Tarski diagonal.**

In `F_15` the third horn of the trilemma, `Reflective d truth` (the existence of a
"liar" query), was an *assumption*. This file discharges that assumption: it
derives reflectivity from a satisfiable universality hypothesis, exactly as the
diagonal lemma derives the liar sentence from the representability of a truth
predicate.

The universality hypothesis is `S.Rep (fun a => !(truth a))`: the system is
computationally universal enough to represent the *negation of its own truth
predicate*. Given a section `code`/`spec` realizing that behavior as a concrete
prompt `ℓ`, the self-verdict on the diagonal is pinned to `eval ℓ ℓ = !(truth ℓ)`,
whence `truth ℓ = !(eval ℓ ℓ)` — the liar query, now a theorem.

**The crux (honesty bar).** This hypothesis is NOT the forbidden
`S.Rep (fun a => !(S.eval a a))` of `no_self_negating_verdict`: there the negated
diagonal is of the system's *own raw verdict* (self-contradictory). Here the
negation is of `truth`, which is an independent predicate; the two coincide only
if `truth` already equals the raw diagonal, which a witness model is free to
avoid. We prove the hypothesis satisfiable with a concrete model in which the
liar genuinely exists (`reflective_of_universal_sat`), so the derivation is
non-vacuous. Reflectivity is genuinely derived, not smuggled in.
-/

import Mathlib
import Foundation.F_15_DiscreteDiagonal

namespace Foundation

/-- **The diagonal lemma, discretely: reflectivity is forced by universality.**

If a system `S` is universal enough to represent the behavior `fun a => !(truth a)`
— the negation of its own truth predicate — then it can pose its own liar query,
i.e. `Reflective (fun a => S.eval a a) truth` holds.

The section `S.code`/`S.spec` turns the representable behavior into a concrete
prompt `ℓ` whose self-verdict satisfies `S.eval ℓ ℓ = !(truth ℓ)`, so
`truth ℓ = !(S.eval ℓ ℓ)`. No liar is assumed; it is constructed. -/
theorem reflective_of_universal {A : Type*} (S : RepSystem A) (truth : A → Bool)
    (hU : S.Rep (fun a => !(truth a))) :
    Reflective (fun a => S.eval a a) truth := by
  refine ⟨S.code _ hU, ?_⟩
  have h := congrFun (S.spec (fun a => !(truth a)) hU) (S.code _ hU)
  simp only at h
  show truth _ = !(S.eval _ _)
  rw [h, Bool.not_not]

/-- **The universality hypothesis is satisfiable, and the liar genuinely exists.**

A concrete `RepSystem` over `Bool` with `truth := fun _ => false`. The system
represents exactly the constant-`true` behavior, which is precisely
`fun a => !(truth a)`, so the universality hypothesis holds. The forbidden
behavior `fun a => !(eval a a) = fun _ => false` is NOT represented, consistent
with `no_self_negating_verdict`. The liar prompt `ℓ = true` genuinely satisfies
`truth ℓ = !(eval ℓ ℓ)` (`false = !true`), so reflectivity is non-vacuous. -/
theorem reflective_of_universal_sat :
    ∃ (A : Type) (S : RepSystem A) (truth : A → Bool),
      S.Rep (fun a => !(truth a))
        ∧ Reflective (fun a => S.eval a a) truth := by
  refine ⟨Bool,
    { eval := fun _ _ => true
      Rep  := fun g => g = (fun _ => true)
      code := fun _ _ => true
      spec := ?_ },
    (fun _ => false), ?_, ?_⟩
  · intro g h; subst h; rfl
  · rfl
  · exact ⟨true, rfl⟩

/-- Sanity check that the hypothesis is not secretly the forbidden one: in the
    witness model the negated-truth behavior and the negated raw diagonal are
    genuinely different functions, so representing the former does not entail the
    impossible `Rep (fun a => !(eval a a))`. -/
theorem witness_hypothesis_not_forbidden :
    (fun a : Bool => !((fun _ : Bool => false) a))
      ≠ (fun a : Bool => !((fun _ _ : Bool => true) a a)) := by
  intro h
  have := congrFun h true
  simp at this

/-- **The trilemma with its reflectivity horn DERIVED.**

Combining the diagonal lemma with `F_15`'s impossibility: no universal system
(one representing the negation of its truth predicate) can be both faithful and
covering. The reflectivity horn is no longer an assumption — it is produced by
`reflective_of_universal`. This is the Universality/Control/Transparency master
trilemma with the third horn forced by computational universality. -/
theorem universal_faithful_covering_impossible {A : Type*}
    (S : RepSystem A) (truth : A → Bool)
    (hU : S.Rep (fun a => !(truth a)))
    (hF : Faithful (fun a => S.eval a a) truth)
    (hC : Covering (fun a => S.eval a a) truth) : False :=
  faithful_covering_reflective_impossible hF hC (reflective_of_universal S truth hU)

#print axioms reflective_of_universal
#print axioms reflective_of_universal_sat
#print axioms witness_hypothesis_not_forbidden
#print axioms universal_faithful_covering_impossible

end Foundation
