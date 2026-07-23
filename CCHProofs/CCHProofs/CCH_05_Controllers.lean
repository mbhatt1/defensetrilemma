/-
# CCH_05_Controllers

**Controllers: forbidden-transformation endomaps on output types.**

A *controller* on an output type `Y` is just an endomap `t : Y → Y`.
Conceptually, `t y` is the transformation the controller wants the
system to **avoid** producing whenever `y` is its current output.  The
controller is *non-trivial* when it admits no fixed point — the
forbidden transformation is genuinely non-degenerate.

The CCH framing pairs controllers with universal systems
`s : A → A → Y`.  Lawvere's diagonal argument forces every endomap of
the codomain of a surjective curried map to have a fixed point.  Hence
a non-trivial controller cannot coexist with a universal system: this
is the basic obstruction underlying the three CCH corner theorems.

This file is self-contained: it re-states the Lawvere fixed-point
lemma locally and derives the controller/universality dichotomy from
it directly.
-/

import Mathlib

namespace CCH

/-! ## Definitions -/

/-- A *controller* on output type `Y` is an endomap.  The intuition:
    `t y` is "the transformation the controller wants the system to NOT
    output if `y` is its current output." -/
abbrev Controller (Y : Type*) : Type _ := Y → Y

/-- A controller is *non-trivial* if no `y` satisfies `t y = y`.
    Equivalently: the forbidden transformation is genuine — there is no
    output value that is "stable" under it. -/
def NonTrivial {Y : Type*} (t : Controller Y) : Prop :=
  ∀ y, t y ≠ y

/-- A system `s : A → A → Y` is *Controlled by `t`* if every output
    value it produces is *not* a fixed point of `t`.  (For non-trivial
    `t` this is automatic; the property bites when paired with
    universality.) -/
def Controlled {A Y : Type*} (s : A → A → Y) (t : Y → Y) : Prop :=
  ∀ a b, t (s a b) ≠ s a b

/-- A controller is *bivalent* if it sends every value somewhere
    different AND its image is non-empty.  (For inhabited `Y` this just
    means non-trivial.) -/
def Bivalent {Y : Type*} (t : Controller Y) : Prop :=
  (∀ y, t y ≠ y) ∧ ∃ _ : Y, True

/-! ## Examples -/

/-- Boolean negation is a non-trivial controller. -/
theorem bool_not_nonTrivial : NonTrivial (fun b : Bool => !b) := by
  intro b; cases b <;> simp

/-- Successor on `ℕ` is a non-trivial controller. -/
theorem nat_succ_nonTrivial : NonTrivial (Nat.succ) := by
  intro n; exact Nat.succ_ne_self n

/-- The identity is the trivial controller (on any non-empty type). -/
theorem id_not_nonTrivial {Y : Type*} [Nonempty Y] :
    ¬ NonTrivial (id : Y → Y) := by
  intro h
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact h y rfl

/-! ## Logical equivalences -/

theorem nonTrivial_iff_no_fixed_point {Y : Type*} (t : Controller Y) :
    NonTrivial t ↔ ∀ y, t y ≠ y := Iff.rfl

theorem nonTrivial_iff_no_fp_exists {Y : Type*} (t : Controller Y) :
    NonTrivial t ↔ ¬ ∃ y, t y = y := by
  unfold NonTrivial
  constructor
  · intro h ⟨y, hy⟩; exact h y hy
  · intro h y hy; exact h ⟨y, hy⟩

theorem controlled_iff {A Y : Type*} (s : A → A → Y) (t : Y → Y) :
    Controlled s t ↔ ∀ a b, t (s a b) ≠ s a b := Iff.rfl

/-! ## The Lawvere obstruction (re-stated locally for self-containment) -/

/-- **Lawvere's fixed-point theorem.**  If `f : A → A → Y` is surjective
    (curried-universal), then every endomap `t : Y → Y` has a fixed
    point.  The witness is `f a₀ a₀`, where `a₀` is any preimage of the
    "diagonal twist" `fun a => t (f a a)`. -/
private theorem lawvere {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ y, t y = y := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨f a₀ a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  simpa using h.symm

/-! ## Key result: universality excludes non-trivial controllers -/

/-- **Universal vs. controller dichotomy.**
    A universal system cannot tolerate any non-trivial controller —
    the diagonal would witness a fixed point of `t`, contradicting
    non-triviality.

    This is one face of the CCH trilemma; the rest of the corner
    theorems extract more refined statements from this. -/
theorem universal_excludes_nonTrivial_controller {A Y : Type*}
    (s : A → A → Y) (hs : Function.Surjective s)
    (t : Controller Y) (ht : NonTrivial t) : False := by
  obtain ⟨y, hy⟩ := lawvere s hs t
  exact ht y hy

/-- Equivalent restatement: a universal system makes its output type
    "fixed-point-rich" — every endomap has a fixed point, so no
    controller on it can be non-trivial. -/
theorem universal_implies_no_nonTrivial_controller {A Y : Type*}
    (s : A → A → Y) (hs : Function.Surjective s) :
    ∀ t : Controller Y, ¬ NonTrivial t := by
  intro t ht
  exact universal_excludes_nonTrivial_controller s hs t ht

/-! ## `Controlled` strengthening -/

/-- If a system is `Controlled` by some `t`, then no output value of
    `s` is a fixed point of `t`.  In particular, since the diagonal
    `s a₀ a₀` must (by Lawvere) BE a fixed point of `t` when `s` is
    universal, a universal `Controlled`-system cannot exist for any
    controller `t` whatsoever. -/
theorem controlled_universal_nonTrivial_contradiction {A Y : Type*}
    (s : A → A → Y) (hs : Function.Surjective s)
    (t : Controller Y) (hC : Controlled s t) : False := by
  -- Re-derive the Lawvere witness explicitly so we can recover the
  -- specific diagonal point `s a₀ a₀` for which `t` fixes it.
  obtain ⟨a₀, ha₀⟩ := hs (fun a => t (s a a))
  have h_diag : s a₀ a₀ = t (s a₀ a₀) := by
    have h := congrArg (· a₀) ha₀
    simpa using h
  have hne : t (s a₀ a₀) ≠ s a₀ a₀ := hC a₀ a₀
  exact hne h_diag.symm

/-! ## Auxiliary observations -/

/-- Non-triviality transports along an injection: if `g : Y → Z` is
    injective and `t : Z → Z` is non-trivial on the image of `g`, the
    induced lifting reflects non-triviality.  (Stated here only as a
    convenience for downstream files.) -/
theorem nonTrivial_of_image {Y Z : Type*} (t : Z → Z) (g : Y → Z)
    (hg : Function.Injective g)
    (h : ∀ y, t (g y) ≠ g y)
    (lift : Y → Y) (hlift : ∀ y, g (lift y) = t (g y)) :
    NonTrivial lift := by
  intro y hy
  have : g (lift y) = g y := by rw [hy]
  have hgt : t (g y) = g y := by rw [← hlift]; exact this
  exact h y hgt

/-- A non-trivial controller has no fixed points anywhere — restatement
    in `¬ ∃` form, useful for `push_neg`-style rewrites. -/
theorem nonTrivial_no_fixed {Y : Type*} (t : Controller Y)
    (ht : NonTrivial t) : ¬ ∃ y, t y = y := by
  rintro ⟨y, hy⟩
  exact ht y hy

/-- Dually: existence of a fixed point negates non-triviality. -/
theorem exists_fixed_not_nonTrivial {Y : Type*} (t : Controller Y)
    (h : ∃ y, t y = y) : ¬ NonTrivial t := by
  rintro ht
  obtain ⟨y, hy⟩ := h
  exact ht y hy

/-- Bivalence implies non-triviality directly. -/
theorem bivalent_nonTrivial {Y : Type*} (t : Controller Y)
    (hb : Bivalent t) : NonTrivial t := hb.1

/-- For inhabited `Y`, non-triviality implies bivalence. -/
theorem nonTrivial_bivalent_of_inhabited {Y : Type*} [Nonempty Y]
    (t : Controller Y) (ht : NonTrivial t) : Bivalent t := by
  refine ⟨ht, ?_⟩
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact ⟨y, trivial⟩

/-!
## Summary

This file establishes the *controller* layer of the CCH trilemma:

* `Controller Y`         — endomaps on the output type.
* `NonTrivial t`         — `t` has no fixed point.
* `Controlled s t`       — every output of `s` evades `t`'s fix-set.
* `Bivalent t`           — non-trivial plus inhabited.

The headline result is
`universal_excludes_nonTrivial_controller`: a surjective curried map
`s : A → A → Y` cannot coexist with any non-trivial controller on `Y`.
This is a direct application of the local `lawvere` lemma, which is in
turn a packaged form of the diagonal argument from `CCH_02_Lawvere`.

Downstream files (`CCH_06_*` and the corner theorems) instantiate this
dichotomy on the three concrete output types corresponding to the
Capability, Control, and Honesty corners of the trilemma.
-/

end CCH
