/-
  CCH Part 1: Foundations
  =======================
  Foundational definitions and basic predicates for the
  "Capability-Control-Honesty" (CCH) Trilemma — a general
  impossibility theorem for AI safety stating that no system can
  simultaneously be Universal, externally Controlled, and
  Self-Transparent.

  The unifying engine, supplied in later files, is Lawvere's
  fixed-point theorem. This file fixes the basic vocabulary used
  throughout the project:

    * `System A Y`           — a curried map `A → A → Y`
                               (Lawvere/Yanofsky setup: the same `A`
                               plays the role of input *and* the role
                               of self-encoding).
    * `Universal s`          — `s` is surjective onto `A → Y`.
    * `Controller Y`         — an endomap `Y → Y` representing a
                               "forbidden transformation" the system
                               must avoid.
    * `NonTrivial t`         — `t` has no fixed point (a genuine swap).
    * `SelfPrediction A Y`   — a function predicting the system's
                               diagonal output `s a a`.
    * `Transparent s p`      — the self-prediction agrees with the
                               diagonal `s a a`.
    * `diag s`               — the diagonal `fun a => s a a`.

  The bundle `CCHStructure` collects a system, a controller, and a
  self-predictor; the wrapped predicates `IsUniversal`,
  `IsControlled`, `IsTransparent` are the three corners of the
  trilemma proved in the later files.
-/

import Mathlib

namespace CCH

/-! ## 1. The basic vocabulary -/

/-- A *system* is a curried map: takes a "self-description" `a : A`
and an "input" `b : A`, returns a value `s a b : Y`.

Following Lawvere/Yanofsky, the same type `A` plays both the role of
input space and the role of self-encoding space. This is what makes
the diagonal `s a a` meaningful: the system can be applied to its
own self-description. -/
abbrev System (A Y : Type*) : Type _ := A → A → Y

/-- *Universality*: the curried system is surjective onto `A → Y`,
i.e. every function `A → Y` is realized as `s a` for some `a : A`.
This is the "capability" corner of the trilemma. -/
def Universal {A Y : Type*} (s : System A Y) : Prop :=
  Function.Surjective s

/-- A *controller* on `Y` is an endomap that prescribes "forbidden
transformations" the system must avoid. Concretely, the controller
specifies "if your output is `y`, you should not have output `t y`
instead" — a behavior the controller is trying to rule out. -/
abbrev Controller (Y : Type*) : Type _ := Y → Y

/-- A controller is *non-trivial* if it has no fixed point — the
transformation it represents is a genuine swap, not the identity on
any output. This is the "control" corner of the trilemma. -/
def NonTrivial {Y : Type*} (t : Controller Y) : Prop :=
  ∀ y, t y ≠ y

/-- A *self-prediction* is a function predicting the value the system
outputs when given itself, i.e. predicting `s a a`. -/
abbrev SelfPrediction (A Y : Type*) : Type _ := A → Y

/-- *Transparency* (a.k.a. honesty / self-knowledge): the
self-prediction `p a` agrees with `s a a`, the system applied to its
own self-description. This is the "honesty" corner of the trilemma. -/
def Transparent {A Y : Type*} (s : System A Y) (p : SelfPrediction A Y) : Prop :=
  ∀ a, s a a = p a

/-! ## 2. Basic lemmas -/

/-- Definitional unfolding of `NonTrivial`. -/
theorem nonTrivial_iff_no_fixed_point {Y : Type*} (t : Controller Y) :
    NonTrivial t ↔ ∀ y, t y ≠ y := Iff.rfl

/-- Definitional unfolding of `Universal`. -/
theorem universal_iff_surjective {A Y : Type*} (s : System A Y) :
    Universal s ↔ Function.Surjective s := Iff.rfl

/-- The "diagonal" of a system: the map `a ↦ s a a` obtained by
applying the system to its own self-description. -/
def diag {A Y : Type*} (s : System A Y) : A → Y := fun a => s a a

/-- Unfolding lemma for `diag`. -/
@[simp] theorem diag_apply {A Y : Type*} (s : System A Y) (a : A) :
    diag s a = s a a := rfl

/-- Transparent self-prediction is exactly the diagonal of the system. -/
theorem transparent_eq_diag {A Y : Type*}
    (s : System A Y) (p : SelfPrediction A Y) :
    Transparent s p ↔ p = diag s := by
  constructor
  · intro h
    funext a
    exact (h a).symm
  · intro h a
    rw [h]
    rfl

/-- A non-trivial controller never agrees with the diagonal: if
`t` has no fixed point and `s a a = p a`, then `t (p a) ≠ p a`.
A small convenience lemma used in later files. -/
theorem nonTrivial_apply {Y : Type*} {t : Controller Y}
    (ht : NonTrivial t) (y : Y) : t y ≠ y := ht y

/-- If a system is universal, then in particular every function
`A → Y` is in the image of `s`. -/
theorem universal_exists {A Y : Type*} {s : System A Y}
    (hs : Universal s) (g : A → Y) : ∃ a : A, s a = g := hs g

/-! ## 3. The CCH bundle -/

/-- Bundled CCH data: a system `s`, a controller `t`, and a
self-prediction `p`. The three corners of the trilemma — universality,
control, transparency — are then expressed as predicates on this
bundle. -/
structure CCHStructure where
  /-- The self-encoding / input space. -/
  A : Type*
  /-- The output space. -/
  Y : Type*
  /-- The system: takes a self-description and an input, returns a value. -/
  s : A → A → Y
  /-- The controller: an endomap representing a forbidden transformation. -/
  t : Y → Y
  /-- The self-prediction: a candidate for `s a a`. -/
  p : A → Y

/-! ## 4. Wrapped predicates on the bundle -/

namespace CCHStructure

/-- The system is *universal*: every function `A → Y` is `C.s a` for
some `a : A`. (The "capability" corner of the trilemma.) -/
def IsUniversal (C : CCHStructure) : Prop :=
  Function.Surjective C.s

/-- The controller is *non-trivial*: the prescribed transformation
has no fixed point. (The "control" corner of the trilemma.) -/
def IsControlled (C : CCHStructure) : Prop :=
  ∀ y, C.t y ≠ y

/-- The self-prediction is *honest*: it matches the diagonal of the
system. (The "honesty" corner of the trilemma.) -/
def IsTransparent (C : CCHStructure) : Prop :=
  ∀ a, C.s a a = C.p a

/-- The bundled `IsUniversal` agrees with the unbundled `Universal`
on the underlying system. -/
theorem isUniversal_iff (C : CCHStructure) :
    C.IsUniversal ↔ Universal C.s := Iff.rfl

/-- The bundled `IsControlled` agrees with the unbundled `NonTrivial`
on the underlying controller. -/
theorem isControlled_iff (C : CCHStructure) :
    C.IsControlled ↔ NonTrivial C.t := Iff.rfl

/-- The bundled `IsTransparent` agrees with the unbundled
`Transparent` on the underlying system and self-prediction. -/
theorem isTransparent_iff (C : CCHStructure) :
    C.IsTransparent ↔ Transparent C.s C.p := Iff.rfl

/-- Under transparency, the self-prediction equals the diagonal of
the system. -/
theorem isTransparent_eq_diag {C : CCHStructure} (h : C.IsTransparent) :
    C.p = diag C.s := by
  funext a
  exact (h a).symm

end CCHStructure

/-! ## 5. Summary

This file provides the basic vocabulary used throughout the CCH
project. To recap:

  Definitions
  -----------
  * `System A Y`               := `A → A → Y`
  * `Universal s`              := `Function.Surjective s`
  * `Controller Y`             := `Y → Y`
  * `NonTrivial t`             := `∀ y, t y ≠ y`
  * `SelfPrediction A Y`       := `A → Y`
  * `Transparent s p`          := `∀ a, s a a = p a`
  * `diag s`                   := `fun a => s a a`

  Bundle
  ------
  * `CCHStructure`             — bundled `(A, Y, s, t, p)`
  * `CCHStructure.IsUniversal`
  * `CCHStructure.IsControlled`
  * `CCHStructure.IsTransparent`

  Lemmas
  ------
  * `nonTrivial_iff_no_fixed_point`
  * `universal_iff_surjective`
  * `diag_apply`
  * `transparent_eq_diag`
  * `nonTrivial_apply`
  * `universal_exists`
  * `CCHStructure.isUniversal_iff`
  * `CCHStructure.isControlled_iff`
  * `CCHStructure.isTransparent_iff`
  * `CCHStructure.isTransparent_eq_diag`

The actual impossibility theorem — that no `CCHStructure` can satisfy
all three of `IsUniversal`, `IsControlled`, and `IsTransparent`
simultaneously — is proved in later files via Lawvere's fixed-point
theorem.
-/

end CCH
