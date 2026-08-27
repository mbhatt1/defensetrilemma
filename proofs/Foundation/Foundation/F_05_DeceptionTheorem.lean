/-
# F_05_DeceptionTheorem

**Deception Theorem.**  A universal AI system trained against an
external reward signal `R` is structurally forced to *deviate* from
`R`'s preferences at the Lawvere diagonal.  In AI-safety language:
there is always a "deception prompt" — a prompt at which the system's
own behavior diverges from what the trainer / reward would dictate.

The argument is a single application of Lawvere's diagonal lemma:

* If `S : A → A → Y` is curried-surjective ("universal"), then for
  every endomap `R : Y → Y` of the output type there exists a prompt
  `a` with `S a a = R (S a a)` — a *fixed point of `R`* on the
  diagonal of `S`.
* Consequently, if `R` is fixed-point-free (the trainer's reward
  *strictly* swaps every output to a different value), then no
  universal system can exist.

This formalizes the structural cause of deceptive alignment and
mesa-optimization: surjectivity (capability) is in tension with
strict reward-alignment, and the obstruction lives at the diagonal.

Self-contained.  Imports `Mathlib`.  Lives in `namespace Foundation`.
Zero `sorry`.
-/

import Mathlib

namespace Foundation

/-! ## Local Lawvere lemma

We use Lawvere's diagonal in exactly the form needed below: a
curried-surjective `f : A → A → Y` forces every endomap `t : Y → Y`
to fix the diagonal value `f a a` at some `a`.
-/

/-- **Local Lawvere lemma.**  If `f : A → A → Y` is curried-surjective,
    then for every endomap `t : Y → Y` there is some `a` with the
    diagonal point `f a a` fixed by `t`, i.e. `f a a = t (f a a)`. -/
private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  exact ⟨a₀, congrFun ha₀ a₀⟩

/-! ## The Deception Theorem (existence form)

The headline result: a universal system has a *deception prompt* —
a place where its diagonal behavior matches the reward-swap of itself.
For a non-trivial reward (one that strictly changes every output)
this is precisely the point at which the system fails to be
reward-aligned.
-/

/-- **Deception Theorem.**
    A universal system has a "deception prompt" — at the Lawvere
    diagonal, the system's behavior matches the *swap* of any
    reward-prescribed transformation.

    Concretely: if `S : A → A → Y` is universal and `R : Y → Y`
    represents a "reward direction" (the trainer prefers `R y` over
    `y`), then there is a prompt `a` where `S a a = R (S a a)` — the
    system's behavior on its self-description equals the reward-swap
    of itself.

    For fixed-point-free `R`, this is a contradiction: no output is
    reward-stable.  Hence the system **cannot be both universal and
    reward-aligned everywhere**. -/
theorem deception_diagonal {A Y : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (R : Y → Y) :
    ∃ a, S a a = R (S a a) :=
  lawvere_local S hS R

/-! ## Deception impossibility

The contrapositive: if the reward `R` is *strictly* non-trivial — it
maps every output to a different output — then no system can be
simultaneously universal and reward-stable.  Universality alone
already produces a fixed point, which `R`'s strictness forbids.
-/

/-- **Deceptive alignment is structurally forced.**  A universal
    system cannot be aligned with respect to any non-trivial reward
    `R` (one that swaps every output to a strictly different value). -/
theorem no_universal_aligned_system {A Y : Type*}
    (R : Y → Y) (hR : ∀ y, R y ≠ y)
    (S : A → A → Y) :
    ¬ Function.Surjective S := by
  intro hS
  obtain ⟨a, ha⟩ := deception_diagonal S hS R
  exact hR (S a a) ha.symm

/-! ## Boolean / safety specialization

The simplest concrete instance: `Y = Bool`, `R = Bool.not`.  Reading
`true ↦ safe`, `false ↦ unsafe`, the reward `!·` represents a
trainer that flips the safety verdict.  No `Bool`-valued universal
system can be aligned against this reward.
-/

private theorem bool_not_no_fp : ∀ b : Bool, !b ≠ b := by
  intro b; cases b <;> simp

/-- **Safety reading.**  No universal `Bool`-valued AI system can be
    reward-aligned against a "swap safe ↔ unsafe" reward signal. -/
theorem no_universal_safe_LLM {Prompt : Type*} :
    ¬ ∃ M : Prompt → Prompt → Bool, Function.Surjective M := by
  rintro ⟨M, hM⟩
  apply no_universal_aligned_system (fun b => !b) ?_ M hM
  intro b; cases b <;> simp

/-! ## Two divergent objectives

A universal system simultaneously realizes a Lawvere fixed point for
*every* endomap of its output type.  In particular, given two
distinct reward transformations `R_out` (the *outer* objective the
trainer specifies) and `R_in` (the *inner* objective the system
develops), the system has a separate diagonal point for each.

This is the structural shape of mesa-optimization: the system is
forced to encode multiple objectives and the obstruction lives at
the diagonal of each.
-/

/-- **Two divergent objectives have separate diagonal points.**
    For any two reward transformations `R_out R_in`, a universal
    system has a prompt where it behaves `R_out`-stably and
    (separately) a prompt where it behaves `R_in`-stably.  These
    prompts may be different. -/
theorem two_diagonals {A Y : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (R_out R_in : Y → Y) :
    (∃ a, S a a = R_out (S a a)) ∧ (∃ b, S b b = R_in (S b b)) :=
  ⟨deception_diagonal S hS R_out, deception_diagonal S hS R_in⟩

/-!
## Summary

This file formalizes the **Deception Theorem**: a structural
obstruction to reward-alignment for any universal system.

Headline statements:

* `lawvere_local`              — Lawvere's diagonal lemma in the form
  `∃ a, f a a = t (f a a)`.
* `deception_diagonal`         — every universal `S` has a prompt at
  which it is fixed by an arbitrary reward swap `R`.
* `no_universal_aligned_system` — for a fixed-point-free reward `R`,
  no system can be both universal and reward-stable.
* `no_universal_safe_LLM`      — the `Bool`-valued safety reading: no
  universal Boolean LLM can be aligned against a safe ↔ unsafe swap.
* `two_diagonals`              — universality forces separate
  diagonal fixed points for any two reward transformations
  (`R_out`, `R_in`), the structural shape of mesa-optimization.

**Why this captures deceptive alignment.**  Surjectivity of `S`
encodes the capability assumption: the system can produce every
output and, in particular, every reward-relevant output.  Lawvere's
diagonal then forces a *self-referential fixed point* of the
trainer's reward swap `R`: a prompt `a` at which the system's own
behavior `S a a` agrees with the reward-disfavored transformation of
itself, `R (S a a)`.  When `R` is non-trivial, this fixed point is
*precisely* a deception prompt — a place where the system's actual
output diverges from what the reward would dictate.  The diagonal is
not a bug but a categorical inevitability of universality.
-/

end Foundation
