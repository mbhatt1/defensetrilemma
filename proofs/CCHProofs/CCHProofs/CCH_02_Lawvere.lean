/-
# CCH_02_Lawvere

**Lawvere's fixed-point theorem (Set version, 1969).**

This is the unifying engine behind Cantor's theorem, Russell's paradox,
Gödel's incompleteness, Tarski's undefinability, the halting problem,
Rice's theorem, and the CCH (Capability–Control–Honesty) trilemma.

The Set version: if `f : A → A → Y` is surjective, then every endomap
`t : Y → Y` has a fixed point.  Equivalently, a fixed-point-free `t`
rules out any "universal" indexing of `A → Y` by `A`.

The proof is the classical Cantor diagonal argument: form
`g a := t (f a a)`, find `a₀` with `f a₀ = g`, then `f a₀ a₀ = g a₀ =
t (f a₀ a₀)`.

This file is self-contained and depends only on Mathlib.
-/

import Mathlib

namespace CCH

/-! ## Lawvere's fixed-point theorem -/

/-- **Lawvere's fixed-point theorem (Set version).**
    If `f : A → A → Y` is surjective, then every endomap `t : Y → Y`
    has a fixed point.

    This is the diagonal argument that subsumes Cantor, Russell, Gödel,
    Tarski, halting, Rice, and the CCH trilemma. -/
theorem lawvere_fixed_point {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ y, t y = y := by
  -- Diagonal: the function `a ↦ t (f a a)`.
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  -- Witness the fixed point at `f a₀ a₀`.
  refine ⟨f a₀ a₀, ?_⟩
  -- Apply both sides of `ha₀ : f a₀ = (fun a => t (f a a))` at `a₀`.
  have h := congrFun ha₀ a₀
  -- `h : f a₀ a₀ = t (f a₀ a₀)`, so `t (f a₀ a₀) = f a₀ a₀`.
  exact h.symm

/-! ## Contrapositive forms -/

/-- **Lawvere contrapositive.** If `t : Y → Y` has *no* fixed point,
    then no `f : A → A → Y` can be surjective.

    This is the form actually used to derive Cantor, Russell, Gödel,
    Tarski, halting, Rice, and the CCH corners downstream. -/
theorem no_surjection_of_no_fixed_point {A Y : Type*}
    (t : Y → Y) (ht : ∀ y, t y ≠ y) :
    ¬ ∃ f : A → A → Y, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨y, hy⟩ := lawvere_fixed_point f hf t
  exact ht y hy

/-- A *universal* system (i.e. one whose self-application `f : A → A → Y`
    is surjective) cannot tolerate a fixed-point-free endomap. -/
theorem universal_implies_fixed_point {A Y : Type*}
    {f : A → A → Y} (hf : Function.Surjective f)
    (t : Y → Y) : ∃ y, t y = y :=
  lawvere_fixed_point f hf t

/-- Equivalently: a fixed-point-free `t : Y → Y` rules out any universal
    system, i.e. there is no surjective `f : A → A → Y`. -/
theorem fixed_point_free_rules_out_universal {A Y : Type*}
    (t : Y → Y) (ht : ∀ y, t y ≠ y)
    (f : A → A → Y) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨y, hy⟩ := lawvere_fixed_point f hf t
  exact ht y hy

/-! ## The diagonal element explicitly -/

/-- The diagonal element produced by Lawvere: given a surjective
    `f : A → A → Y` and an endomap `t : Y → Y`, this is a value
    `y : Y` with `t y = y`.

    Concretely, `y = f a₀ a₀` where `a₀` is any pre-image of the
    diagonal `a ↦ t (f a a)` under `f`.  We use classical choice to
    extract such an `a₀`, hence the `noncomputable` marker. -/
noncomputable def lawvereFixedPoint {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f) (t : Y → Y) : Y :=
  (lawvere_fixed_point f hf t).choose

/-- The defining property of `lawvereFixedPoint`: it is a fixed point of `t`. -/
theorem lawvereFixedPoint_spec {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f) (t : Y → Y) :
    t (lawvereFixedPoint f hf t) = lawvereFixedPoint f hf t :=
  (lawvere_fixed_point f hf t).choose_spec

/-! ## Section / retract variant

The categorical statement of Lawvere's theorem only requires a section
`sec : (A → Y) → A` of `f` (i.e. `f ∘ sec = id`) rather than full
surjectivity.  This is the form that generalizes verbatim to any
cartesian closed category. -/

/-- **Lawvere via section.** If there is a section `sec : (A → Y) → A`
    with `f (sec g) = g` for every `g : A → Y`, then every `t : Y → Y`
    has a fixed point.

    This is a slight strengthening of the surjectivity hypothesis: any
    section gives surjectivity, and in `Type*` (with classical choice)
    the converse also holds. -/
theorem lawvere_via_section {A Y : Type*}
    (f : A → A → Y) (sec : (A → Y) → A)
    (hsec : ∀ g, f (sec g) = g)
    (t : Y → Y) : ∃ y, t y = y := by
  -- Apply `f ∘ sec = id` to the diagonal `a ↦ t (f a a)`.
  set g : A → Y := fun a => t (f a a) with hg
  set a₀ : A := sec g with ha₀
  refine ⟨f a₀ a₀, ?_⟩
  have hfix : f a₀ = g := hsec g
  have h := congrFun hfix a₀
  -- `h : f a₀ a₀ = g a₀ = t (f a₀ a₀)`.
  exact h.symm

/-- A section `sec : (A → Y) → A` of `f : A → A → Y` yields surjectivity. -/
theorem surjective_of_section {A Y : Type*}
    (f : A → A → Y) (sec : (A → Y) → A)
    (hsec : ∀ g, f (sec g) = g) :
    Function.Surjective f :=
  fun g => ⟨sec g, hsec g⟩

/-! ## Iff packaging

It is sometimes convenient to package the contrapositive as an `Iff`:
"`f` is non-surjective iff there exists a fixed-point-free endomap" is
*not* what Lawvere says (the right-to-left direction is the theorem;
the left-to-right direction would require constructing a witness from
non-surjectivity, which is not what Lawvere provides).  Instead we
package the working form: "`f` surjective ⇒ every `t` has a fixed
point". -/

/-- Lawvere as an implication packaged for rewriting:
    surjectivity of `f` implies the universal fixed-point property of `Y`. -/
theorem lawvere_universal_fixed_point {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f) :
    ∀ t : Y → Y, ∃ y, t y = y :=
  fun t => lawvere_fixed_point f hf t

/-! ## File summary

This file proves the following, using only Mathlib:

* `lawvere_fixed_point` — Lawvere's fixed-point theorem (Set version):
  surjective `f : A → A → Y` ⇒ every `t : Y → Y` has a fixed point.
* `no_surjection_of_no_fixed_point` — the contrapositive: a
  fixed-point-free `t` rules out any surjection `A → A → Y`.
* `universal_implies_fixed_point` — alias of `lawvere_fixed_point`
  emphasizing the "universal system" reading.
* `fixed_point_free_rules_out_universal` — pointwise contrapositive
  used downstream to derive the three CCH corners.
* `lawvereFixedPoint` / `lawvereFixedPoint_spec` — the diagonal element
  as an explicit (noncomputable) term, with its defining property.
* `lawvere_via_section` — the section/retract form (categorical
  Lawvere), strictly stronger than the surjective form.
* `surjective_of_section` — sections give surjectivity.
* `lawvere_universal_fixed_point` — `Iff`-friendly packaging.

Downstream files (`CCH_03_Cantor`, `CCH_04_FixedPointFree`, the corner
files) instantiate `Y` and `t` to recover Cantor's theorem, Russell's
paradox, Gödel's incompleteness, Tarski's undefinability, the halting
problem, Rice's theorem, and the three corners of the CCH trilemma.
-/

end CCH
