/-
# CCH_07_CornerUC

**Corner 1 of the CCH Trilemma: U + C ⇒ ¬T.**

This file formalizes the *Defense Trilemma face* of the CCH trilemma:
a system that is simultaneously **Universal** (curried-surjective) and
**Controlled** (its self-prediction is forbidden by some endomap of
the output type) cannot also be **Transparent** (its diagonal
behaviour `s a a` matching a stated self-prediction `p a`).

The argument is a direct application of Lawvere's diagonal:

* Surjectivity of `s : A → A → Y` forces every endomap `t : Y → Y` to
  fix some diagonal point `s a₀ a₀`.
* Transparency identifies that diagonal point with `p a₀`, the system's
  stated self-prediction at `a₀`.
* Controlledness (in its "self-prediction" form) rules out exactly
  this: `t (p a₀) ≠ p a₀`.

All three hypotheses are used.  Without Universality there is no
Lawvere fixed point; without Transparency the fixed point need not
land on `p`; without Controlledness there is no contradiction at the
fixed point.

The file also records the *strong* form (Universal + Controlled-
everywhere is already inconsistent, by Lawvere applied to `t`
directly) and a few convenience corollaries.

Self-contained: imports `Mathlib`, lives in `namespace CCH`, uses
zero `sorry`.
-/

import Mathlib

namespace CCH

/-! ## Local Lawvere fixed-point lemma

We restate Lawvere's diagonal argument in the precise form we need
here: surjectivity of a curried map `f : A → A → Y` forces every
endomap `t : Y → Y` to fix the diagonal value `f a a` for some `a`.

The statement is oriented as `f a a = t (f a a)`, which is the form
most directly useful for the Corner 1 contradiction below.
-/

/-- **Local Lawvere lemma.**  If `f : A → A → Y` is curried-surjective,
    then for every endomap `t : Y → Y` there is some `a` with the
    diagonal point `f a a` fixed by `t`, i.e. `f a a = t (f a a)`. -/
private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  simpa using h

/-! ## The corner theorem (sharp form)

The Defense-Trilemma face: Universal + Controlled-on-self-prediction
implies *not* Transparent-with-respect-to-that-prediction.

This is the cleanest "trilemma corner" statement: it asserts the
*incompatibility* of all three properties, with each contributing to
the proof.
-/

/-- **CCH Corner 1: U + C ⇒ ¬T.**

If a system `s : A → A → Y` is universal, with a controller `t : Y → Y`
that forbids every value of the stated self-prediction `p : A → Y`
(i.e. `∀ a, t (p a) ≠ p a`), then `s` cannot be transparent with
respect to `p`.

Equivalently: a universal system whose self-prediction the controller
blocks cannot match its self-prediction at the diagonal — there must
be some `a` where `s a a ≠ p a`. -/
theorem corner_UC_not_T {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hC : ∀ a, t (p a) ≠ p a) :
    ¬ (∀ a, s a a = p a) := by
  intro hT
  -- Lawvere: ∃ a₀ with s a₀ a₀ = t (s a₀ a₀).
  obtain ⟨a₀, ha₀⟩ := lawvere_local s hU t
  -- Transparency at a₀: s a₀ a₀ = p a₀.
  have hsp : s a₀ a₀ = p a₀ := hT a₀
  -- Substitute s a₀ a₀ ↦ p a₀ in `ha₀` to get p a₀ = t (p a₀).
  have hfix : p a₀ = t (p a₀) := by
    rw [hsp] at ha₀; exact ha₀
  -- Controlledness on the self-prediction rules this out.
  exact hC a₀ hfix.symm

/-! ## Contrapositive form (impossibility)

Phrased as "all three jointly imply False", which is the form most
useful when chaining with the rest of the trilemma.
-/

/-- **CCH Corner 1 (contrapositive).**

Universal + Controlled (on self-prediction) + Transparent (with
respect to that prediction) cannot all hold simultaneously. -/
theorem corner_UC_impossible {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hC : ∀ a, t (p a) ≠ p a)
    (hT : ∀ a, s a a = p a) : False :=
  corner_UC_not_T s t p hU hC hT

/-! ## Strong form

Without invoking Transparency at all: if `t` is forbidden on *every*
output of `s` (the original, stronger `Controlled` predicate), then
universality already contradicts.  This is just Lawvere applied to
`t` and `s`.
-/

/-- **Strong form: Universal + Controlled-everywhere ⇒ False.**

This is Lawvere applied directly to the controller `t`: surjectivity
of `s` produces a diagonal fixed point `s a₀ a₀` of `t`, contradicting
the assumption that `t` has no fixed points among the values of `s`. -/
theorem corner_UC_strong {A Y : Type*}
    (s : A → A → Y) (t : Y → Y)
    (hU : Function.Surjective s)
    (hC : ∀ a b, t (s a b) ≠ s a b) : False := by
  obtain ⟨a₀, ha₀⟩ := lawvere_local s hU t
  exact hC a₀ a₀ ha₀.symm

/-! ## Symmetric corollary

The image of the diagonal `a ↦ s a a` of any universal `s` is "fixed-
point-rich": it intersects the fixed-point set of every endomap of
`Y`.
-/

/-- **Universal diagonal hits every endomap's fixed-point set.**

For a universal `s : A → A → Y` and any endomap `t : Y → Y`, the
diagonal value `s a a` is fixed by `t` for some `a`. -/
theorem universal_diagonal_hits_fixed_point {A Y : Type*}
    (s : A → A → Y) (hU : Function.Surjective s)
    (t : Y → Y) : ∃ a, t (s a a) = s a a := by
  obtain ⟨a₀, ha₀⟩ := lawvere_local s hU t
  exact ⟨a₀, ha₀.symm⟩

/-! ## Defense Trilemma reading

Re-export of `corner_UC_impossible` under a name that matches the
Defense-Trilemma narrative used in the surrounding paper: `Y` is the
LLM's safety judgement, `t` is the wrapper's "swap-judgement" attack,
`p` is the wrapper's stated boundary.  The conclusion is that a
universal LLM whose stated boundary is non-trivially controlled
cannot have its self-judgement match its boundary.
-/

/-- **Reading: the Defense Trilemma face.**

Interpreting `Y` as the safety judgment of an LLM, `t` as the
wrapper's "swap-judgment" attack, and `p` as the wrapper's stated
boundary: a universal LLM whose stated boundary is non-trivially
controlled cannot have its self-judgment match its boundary. -/
theorem defense_trilemma_face {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hC : ∀ a, t (p a) ≠ p a)
    (hT : ∀ a, s a a = p a) : False :=
  corner_UC_impossible s t p hU hC hT

/-! ## Convenience corollaries

A pair of "extracted witness" forms — useful when one wants the
specific diagonal point `a₀` at which the corner contradiction
manifests, rather than just `False`.
-/

/-- **Witness form.**  Under U and C-on-self-prediction, there
    *exists* a concrete `a` at which transparency fails. -/
theorem corner_UC_exists_failure {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hC : ∀ a, t (p a) ≠ p a) :
    ∃ a, s a a ≠ p a := by
  by_contra hall
  push_neg at hall
  exact corner_UC_not_T s t p hU hC hall

/-- **Symmetric witness form.**  Under U and Transparency, there
    exists `a` whose self-prediction `p a` is fixed by `t` — this is
    the dual statement, where the failure is loaded onto the
    controller rather than onto transparency. -/
theorem corner_UC_prediction_fixed_point {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hT : ∀ a, s a a = p a) :
    ∃ a, t (p a) = p a := by
  obtain ⟨a₀, ha₀⟩ := lawvere_local s hU t
  refine ⟨a₀, ?_⟩
  have hsp : s a₀ a₀ = p a₀ := hT a₀
  -- ha₀ : s a₀ a₀ = t (s a₀ a₀); rewrite using hsp.
  have hfix : p a₀ = t (p a₀) := by
    rw [hsp] at ha₀; exact ha₀
  exact hfix.symm

/-!
## Summary

This file establishes **Corner 1** of the CCH trilemma — the
Defense-Trilemma face — formalizing the obstruction

  Universal  +  Controlled-on-self-prediction  +  Transparent  ⊢  ⊥.

Headline statements:

* `lawvere_local`                        — Lawvere's diagonal lemma in
  the form `∃ a, f a a = t (f a a)`.
* `corner_UC_not_T`                      — U + C ⇒ ¬T (sharp form).
* `corner_UC_impossible`                 — U + C + T ⇒ False.
* `corner_UC_strong`                     — U + Controlled-everywhere
  ⇒ False (uses Lawvere directly, no Transparency required).
* `universal_diagonal_hits_fixed_point`  — every endomap of `Y` has
  a diagonal fixed point in the image of a universal `s`.
* `defense_trilemma_face`                — Defense-Trilemma rebrand
  of `corner_UC_impossible`.
* `corner_UC_exists_failure`             — extracted witness `a` with
  `s a a ≠ p a`.
* `corner_UC_prediction_fixed_point`     — dual extracted witness:
  `∃ a, t (p a) = p a`.

The remaining two corners of the CCH trilemma — corresponding to the
**Capability** face (U + T ⇒ ¬C) and the **Honesty** face (C + T ⇒
¬U) — are formalized in subsequent files of this development.
-/

end CCH
