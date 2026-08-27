/-
  CCH Master Trilemma
  ===================
  Capstone of the CCH (Capability-Control-Honesty) Trilemma project.

  The previous files set up Lawvere's theorem and prove three corner
  theorems individually:
    * U + C ⇒ ¬T   (Universality + Control ⇒ not Transparent)
    * U + T ⇒ ¬C   (Universality + Transparency ⇒ not Controlled)
    * C + T ⇒ ¬U   (Control + Transparency ⇒ not Universal)

  This file packages everything into a single bundled `CCHStructure`,
  states the master theorem ("at most 2 of {U, C, T}"), and derives the
  three corners as immediate consequences.

  The proof depends only on Lawvere's diagonal argument: any surjection
  `f : A → A → Y` admits, for every `t : Y → Y`, a diagonal point
  `a₀` with `f a₀ a₀ = t (f a₀ a₀)`. Combined with transparency
  (`s a a = p a`) this forces `p a₀ = t (p a₀)`, contradicting control.
-/

import Mathlib

namespace CCH

/-- **Lawvere's fixed-point theorem (local form).**
    If `f : A → A → Y` is surjective (when curried), then for every
    `t : Y → Y` the diagonal `a ↦ f a a` hits a fixed point of `t`. -/
private theorem lawvere {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  simpa using h

/-- The CCH bundle: a system `s : A → A → Y`, an external controller
    `t : Y → Y`, and a self-prediction `p : A → Y`.

    * `A` is the space of agents / inputs.
    * `Y` is the space of behaviours / outputs.
    * `s a b` is the behaviour of agent `a` on input `b`.
    * `t y` is what the controller does to a behaviour `y`.
    * `p a` is the agent's self-prediction (claimed output on its own input). -/
structure CCHStructure where
  A : Type*
  Y : Type*
  s : A → A → Y
  t : Y → Y
  p : A → Y

/-- The system is **universal**: every behaviour `A → Y` is realised
    by some agent. Equivalently, the curried form `s` is surjective. -/
def CCHStructure.IsUniversal (C : CCHStructure) : Prop :=
  Function.Surjective C.s

/-- The self-prediction is **controlled** by `t`: no value of `p`
    is a fixed point of the controller `t`. The controller can always
    nudge the prediction. -/
def CCHStructure.IsControlled (C : CCHStructure) : Prop :=
  ∀ a, C.t (C.p a) ≠ C.p a

/-- The system is **transparent** with respect to `p`: the diagonal
    behaviour `s a a` matches the self-prediction `p a` for every `a`.
    The system says what it will do, on itself. -/
def CCHStructure.IsTransparent (C : CCHStructure) : Prop :=
  ∀ a, C.s a a = C.p a

/-- **The CCH Master Trilemma.**
    No system can be simultaneously Universal, Controlled, and
    Self-Transparent.

    *Proof sketch.* By Lawvere applied to `s` and `t`, there is some
    `a₀` with `s a₀ a₀ = t (s a₀ a₀)`. Transparency replaces
    `s a₀ a₀` by `p a₀`, giving `p a₀ = t (p a₀)`, which directly
    contradicts the control hypothesis at `a₀`. -/
theorem cch_master_trilemma (C : CCHStructure) :
    ¬ (C.IsUniversal ∧ C.IsControlled ∧ C.IsTransparent) := by
  rintro ⟨hU, hC, hT⟩
  obtain ⟨a₀, ha₀⟩ := lawvere C.s hU C.t
  have hsp : C.s a₀ a₀ = C.p a₀ := hT a₀
  have hfix : C.p a₀ = C.t (C.p a₀) := by
    rw [hsp] at ha₀
    exact ha₀
  exact hC a₀ hfix.symm

/-- **Corner 1: U + C ⇒ ¬T.**
    A universal, controlled system cannot be self-transparent. -/
theorem cch_corner_UC (C : CCHStructure)
    (hU : C.IsUniversal) (hC : C.IsControlled) :
    ¬ C.IsTransparent := fun hT =>
  cch_master_trilemma C ⟨hU, hC, hT⟩

/-- **Corner 2: U + T ⇒ ¬C.**
    A universal, self-transparent system cannot be controlled. -/
theorem cch_corner_UT (C : CCHStructure)
    (hU : C.IsUniversal) (hT : C.IsTransparent) :
    ¬ C.IsControlled := fun hC =>
  cch_master_trilemma C ⟨hU, hC, hT⟩

/-- **Corner 3: C + T ⇒ ¬U.**
    A controlled, self-transparent system cannot be universal. -/
theorem cch_corner_CT (C : CCHStructure)
    (hC : C.IsControlled) (hT : C.IsTransparent) :
    ¬ C.IsUniversal := fun hU =>
  cch_master_trilemma C ⟨hU, hC, hT⟩

/-- **At most two of {U, C, T}.**
    Reformulation of the master trilemma: any single CCH structure can
    satisfy at most two of the three properties Universal, Controlled,
    and Transparent. -/
theorem cch_at_most_two (C : CCHStructure) :
    ¬ (C.IsUniversal ∧ C.IsControlled ∧ C.IsTransparent) :=
  cch_master_trilemma C

/-!
  ## Summary

  The CCH Trilemma in one line:

      U(C) ∧ C(C) ∧ T(C) → False.

  Equivalently, for any CCH structure `C`, at most two of the three
  properties `IsUniversal`, `IsControlled`, `IsTransparent` can hold
  simultaneously. The three corner theorems `cch_corner_UC`,
  `cch_corner_UT`, `cch_corner_CT` express the contrapositives, one
  per omitted property.

  All four results follow from the local Lawvere lemma plus a single
  rewrite using transparency. There are no `sorry`s; the only axioms
  are the standard `propext`, `Classical.choice`, `Quot.sound`. -/

end CCH
