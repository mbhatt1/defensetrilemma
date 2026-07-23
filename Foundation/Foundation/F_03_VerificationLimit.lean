/-
  F_03_VerificationLimit.lean

  Foundation / Verification Limit.

  Intuition.  A verifier `V` that decides whether a system has property `P`
  cannot be more capable than the system itself when `P` is non-trivial.
  For AI safety: external auditors of frontier systems cannot decide
  non-trivial behavioral properties unless they themselves are universal
  (which, by the Mirror Trilemma, then face their own trilemma).

  Headline result.  No type with a fixed-point-free endomap admits a
  universal self-application.  Equivalently: any output type carrying
  a non-trivial transformation (e.g. `Bool` with negation, `ℕ` with
  successor) structurally forbids surjective `A → A → Y`, and therefore
  forbids any external verifier that could claim to mirror the system's
  diagonal behavior.

  The proof is Lawvere, contraposed: surjectivity + a fixed-point-free
  endomap on the codomain is contradictory.
-/

import Mathlib

namespace Foundation

/-! ### Local Lawvere fixed-point lemma

We re-prove Lawvere's fixed-point theorem locally to keep this file
self-contained and to avoid any dependence on the exact name in
`F_01_LawvereCore.lean`. -/

/-- **Lawvere (local).**  If `f : A → A → Y` is surjective then every
    endomap `t : Y → Y` has a "diagonal" fixed point of the form
    `f a a = t (f a a)`. -/
private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  exact ⟨a₀, congrFun ha₀ a₀⟩

/-! ### Boolean negation has no fixed point -/

/-- Boolean negation is fixed-point-free: `!b ≠ b` for every `b : Bool`. -/
private theorem bool_not_no_fp : ∀ b : Bool, !b ≠ b := by
  intro b; cases b <;> simp

/-! ### The Verification Limit (headline form)

The clean statement: any codomain `Y` carrying a fixed-point-free
endomap `t : Y → Y` cannot be the target of a universal (surjective)
self-application `S : A → A → Y`.

Read as a verification result: a verifier that operates at the level
of such an output type cannot, even in principle, mirror the system's
diagonal behavior, because no such universal system exists in the first
place — the diagonal is forced by Lawvere into a self-flipping
configuration which `t` rules out. -/

/-- **Verification Limit (cardinality / Lawvere form).**
    No type with a fixed-point-free endomap admits a universal
    self-application.  In symbols: if `t : Y → Y` has no fixed point,
    then there is no surjection `A → (A → Y)`. -/
theorem no_universal_with_fpf_output {A Y : Type*}
    (t : Y → Y) (ht : ∀ y, t y ≠ y) :
    ¬ ∃ S : A → A → Y, Function.Surjective S := by
  rintro ⟨S, hS⟩
  obtain ⟨a, ha⟩ := lawvere_local S hS t
  -- `ha : S a a = t (S a a)`, but `t` has no fixed point.
  exact ht (S a a) ha.symm

/-! ### AI-safety packaging -/

/-- **AI-safety reading of the Verification Limit.**
    Any AI-output type with a fixed-point-free transformation
    (e.g. `Bool` with negation, `ℕ` with successor) cannot be the
    codomain of a universal `Prompt → Prompt → Output` system.
    Verifiers that operate at the level of such output types thus
    face a structural impossibility: the universal system they claim
    to verify cannot exist.

    This is a renaming of `no_universal_with_fpf_output`, kept for
    readability inside the AI-safety landscape. -/
theorem no_universal_AI_output_type {Prompt Output : Type*}
    (t : Output → Output) (ht : ∀ y, t y ≠ y) :
    ¬ ∃ M : Prompt → Prompt → Output, Function.Surjective M :=
  no_universal_with_fpf_output t ht

/-- **Concrete instance:** no universal `Bool`-valued LLM exists.
    Boolean negation is fixed-point-free, so by the Verification Limit
    no surjective `Prompt → Prompt → Bool` system is possible. -/
theorem no_universal_bool_LLM {Prompt : Type*} :
    ¬ ∃ M : Prompt → Prompt → Bool, Function.Surjective M := by
  apply no_universal_AI_output_type (fun b => !b)
  intro b
  cases b <;> simp

/-- **Concrete instance:** no universal `ℕ`-valued LLM exists.
    The successor map `n ↦ n + 1` is fixed-point-free on `ℕ`, so
    by the Verification Limit no surjective `Prompt → Prompt → ℕ`
    system is possible. -/
theorem no_universal_nat_LLM {Prompt : Type*} :
    ¬ ∃ M : Prompt → Prompt → ℕ, Function.Surjective M :=
  no_universal_AI_output_type Nat.succ Nat.succ_ne_self

/-!
### Summary

The **Verification Limit** is the structural impossibility of universal
systems on fixed-point-free output types.

* `no_universal_with_fpf_output` is the headline mathematical result:
  a fixed-point-free endomap on `Y` rules out any surjection
  `A → (A → Y)`.
* `no_universal_AI_output_type` is the same statement renamed for the
  AI-safety setting (`Prompt → Prompt → Output`).
* `no_universal_bool_LLM` and `no_universal_nat_LLM` are concrete
  corollaries witnessing the limit on the two most common output
  types: Boolean classification and natural-number scoring.

In the AI-safety landscape this means: any verifier that operates at
the level of a fixed-point-free output type cannot, even hypothetically,
audit a universal system at that output type — because no such universal
system can exist.  Combined with the Mirror Trilemma, any verifier
powerful enough to escape this restriction is itself universal and
inherits the trilemma.
-/

end Foundation
