/-
# CCH_04_FixedPointFree

**Fixed-point-free endomaps and the Lawvere contrapositive.**

This file develops basic facts about endomaps `t : Y → Y` with no fixed
point, and ties them to the non-surjectivity of curried "system maps"
`f : A → A → Y` via the Lawvere contrapositive.

The key principle (from `CCH_02_Lawvere`): if `Y` admits *any*
fixed-point-free endomap `t`, then no curried map `A → A → Y` can be
surjective.  Concretely, this means a non-trivial "controller" on `Y`
precludes a "universal" indexing of `A → Y` by `A`.

This is the engine that drives the three CCH corners downstream:
Capability, Control, and Honesty each fail by exhibiting a
fixed-point-free `t` on a suitable answer type `Y`.

This file is self-contained and depends only on Mathlib.
-/

import Mathlib

namespace CCH

/-! ## Definition of fixed-point-freeness -/

/-- An endomap is *fixed-point-free* if it has no fixed point. -/
def FixedPointFree {Y : Type*} (t : Y → Y) : Prop :=
  ∀ y, t y ≠ y

/-! ## Examples -/

/-- Boolean negation is fixed-point-free. -/
theorem bool_not_fixedPointFree : FixedPointFree (fun b : Bool => !b) := by
  intro b; cases b <;> simp

/-- Successor on `ℕ` is fixed-point-free. -/
theorem succ_fixedPointFree : FixedPointFree (Nat.succ) := by
  intro n; exact Nat.succ_ne_self n

/-- Successor on `ℤ` is fixed-point-free. -/
theorem int_succ_fixedPointFree : FixedPointFree (fun n : ℤ => n + 1) := by
  intro n h
  have h1 : (1 : ℤ) = 0 := by linarith
  exact one_ne_zero h1

/-! ## Lawvere theorem (re-stated locally) and its contrapositive

The proof of `lawvere` here mirrors the one in `CCH_02_Lawvere`; we
re-state it privately so this file is self-contained as a development
of fixed-point-free machinery, without importing the rest of the
project. -/

private theorem lawvere {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ y, t y = y := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨f a₀ a₀, ?_⟩
  have h := congrFun ha₀ a₀
  exact h.symm

/-- **Lawvere contrapositive.** A fixed-point-free endomap on `Y`
    rules out surjective `A → A → Y`. -/
theorem no_surjection_of_fixedPointFree {A Y : Type*}
    (t : Y → Y) (ht : FixedPointFree t)
    (f : A → A → Y) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨y, hy⟩ := lawvere f hf t
  exact ht y hy

/-! ## Useful corollary: control–universality dichotomy -/

/-- **The control–universality dichotomy.**
    If `Y` admits a fixed-point-free endomap (a non-trivial "controller"),
    no curried system `A → A → Y` can be surjective. -/
theorem fixedPointFree_blocks_universality {A Y : Type*}
    (h : ∃ t : Y → Y, FixedPointFree t) :
    ¬ ∃ f : A → A → Y, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨t, ht⟩ := h
  obtain ⟨y, hy⟩ := lawvere f hf t
  exact ht y hy

/-! ## Equivalences and basic shape lemmas -/

/-- Fixed-point-free is equivalent to the universal statement. -/
theorem fixedPointFree_iff {Y : Type*} (t : Y → Y) :
    FixedPointFree t ↔ ∀ y, t y ≠ y := Iff.rfl

/-- Composition of fixed-point-free maps may have fixed points
    (e.g., `not ∘ not = id` on `Bool`).  Sanity check showing that
    `FixedPointFree` is not closed under composition. -/
theorem not_not_eq_id : (fun b : Bool => !(!b)) = id := by
  funext b; cases b <;> rfl

/-- An endomap on the empty type is trivially fixed-point-free. -/
theorem empty_fixedPointFree (t : Empty → Empty) : FixedPointFree t :=
  fun y => y.elim

/-- An endomap on `Unit` cannot be fixed-point-free.  Any
    `t : Unit → Unit` satisfies `t () = ()` by `Subsingleton`. -/
theorem unit_no_fixedPointFree (t : Unit → Unit) : ¬ FixedPointFree t := by
  intro h
  have hne : t () ≠ () := h ()
  have heq : t () = () := Subsingleton.elim (t ()) ()
  exact hne heq

/-! ## Strong Lawvere variant: section instead of surjectivity

The categorical version of Lawvere only needs a *section*
`sec : (A → Y) → A` of `f` (i.e. `f ∘ sec = id`).  This is logically
slightly stronger than surjectivity in the `Type*` setting (with
classical choice the two are equivalent), and it is the form that
transfers to any cartesian closed category. -/

/-- **Strong Lawvere.** If `f : A → A → Y` admits a *section*
    `sec : (A → Y) → A` (i.e. `f (sec g) = g` for all `g`), then every
    `t : Y → Y` has a fixed point. -/
theorem lawvere_section {A Y : Type*}
    (f : A → A → Y) (sec : (A → Y) → A)
    (hsec : ∀ g, f (sec g) = g)
    (t : Y → Y) : ∃ y, t y = y := by
  set g : A → Y := fun a => t (f a a) with hg
  set a₀ : A := sec g with ha₀_def
  refine ⟨f a₀ a₀, ?_⟩
  have hfix : f a₀ = g := hsec g
  have h := congrFun hfix a₀
  exact h.symm

/-- Section form of the contrapositive: a fixed-point-free `t` rules
    out any section of `f`. -/
theorem no_section_of_fixedPointFree {A Y : Type*}
    (t : Y → Y) (ht : FixedPointFree t)
    (f : A → A → Y) (sec : (A → Y) → A) :
    ¬ (∀ g, f (sec g) = g) := by
  intro hsec
  obtain ⟨y, hy⟩ := lawvere_section f sec hsec t
  exact ht y hy

/-! ## File summary

This file proves the following, using only Mathlib:

* `FixedPointFree` — definition: `t : Y → Y` has no fixed point.
* `bool_not_fixedPointFree`, `succ_fixedPointFree`,
  `int_succ_fixedPointFree` — concrete examples.
* `no_surjection_of_fixedPointFree` — Lawvere contrapositive: a
  fixed-point-free endomap on `Y` rules out surjective `A → A → Y`.
* `fixedPointFree_blocks_universality` — control–universality
  dichotomy: a non-trivial controller on `Y` precludes universal
  systems valued in `Y`.
* `fixedPointFree_iff` — definitional unfolding as an `Iff`.
* `not_not_eq_id` — sanity check that fixed-point-free is not closed
  under composition.
* `empty_fixedPointFree` — vacuous case for `Empty`.
* `unit_no_fixedPointFree` — impossibility for `Unit` (Subsingleton).
* `lawvere_section` — categorical/strong form: a section suffices.
* `no_section_of_fixedPointFree` — contrapositive of the section form.

Downstream files (the three CCH corner files: Capability, Control,
Honesty) instantiate `Y` and `t` to derive the corners of the
trilemma from `no_surjection_of_fixedPointFree` and
`fixedPointFree_blocks_universality`.
-/

end CCH
