/-
# F_01_LawvereCore

**Lawvere's fixed-point theorem (Set version, 1969).**

This is the **first file** of a unified foundational landscape for AI-safety
impossibility theorems.  It packages Lawvere's diagonal as the master engine
that every downstream impossibility (Rice's theorem, the Verification Limit,
the Calibration Trilemma, Deception, the Mirror Trilemma, …) instantiates by
choosing a different fixed-point-free endomap `t : Y → Y`.

The Set form: if `f : A → A → Y` is surjective, then every endomap
`t : Y → Y` has a fixed point.  Equivalently, a fixed-point-free `t` rules
out any "universal" indexing of `A → Y` by `A`.

The proof is the classical Cantor diagonal: form `g a := t (f a a)`, find
`a₀` with `f a₀ = g`, then `f a₀ a₀ = g a₀ = t (f a₀ a₀)`.

This file is self-contained and depends only on Mathlib.
-/

import Mathlib

namespace Foundation

noncomputable section

/-! ## Lawvere's fixed-point theorem -/

/-- **Lawvere's fixed-point theorem.** If `f : A → A → Y` is surjective,
    then every endomap `t : Y → Y` has a fixed point.

    This is the master engine for the foundational AI-safety impossibilities:
    Rice's theorem, the Verification Limit, the Calibration Trilemma,
    Deception, and the Mirror Trilemma all reduce to Lawvere applied with
    different choices of `t`. -/
theorem lawvere {A Y : Type*}
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

/-! ## Diagonal-finding form -/

/-- **Lawvere's diagonal.** A surjective `f : A → A → Y` together with any
    endomap `t : Y → Y` yields a *specific* diagonal index `a : A` at which
    `f a a` is fixed by `t`.

    This form returns the diagonal point itself, which is what most
    downstream theorems actually use to extract a witness. -/
theorem lawvere_diagonal {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  exact ⟨a₀, congrFun ha₀ a₀⟩

/-! ## Contrapositive forms

These are the forms most downstream impossibility theorems actually consume:
they package "fixed-point-free `t` ⇒ no universal `f`" as a direct refutation
schema. -/

/-- **Lawvere contrapositive (existential).** If `t : Y → Y` has *no* fixed
    point, then no `f : A → A → Y` can be surjective.

    Used directly to derive every downstream impossibility once a
    fixed-point-free transformation of the output type has been exhibited. -/
theorem no_surjection_of_no_fixed_point {A Y : Type*}
    (t : Y → Y) (ht : ∀ y, t y ≠ y) :
    ¬ ∃ f : A → A → Y, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨y, hy⟩ := lawvere f hf t
  exact ht y hy

/-- **Lawvere contrapositive (pointwise).** A fixed-point-free `t : Y → Y`
    blocks any specific candidate `f : A → A → Y` from being surjective.

    This is the form most ergonomic for downstream files: assume the
    universal-system `f` is given and conclude it cannot be surjective. -/
theorem fixed_point_free_blocks_universality {A Y : Type*}
    (t : Y → Y) (ht : ∀ y, t y ≠ y)
    (f : A → A → Y) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨y, hy⟩ := lawvere f hf t
  exact ht y hy

/-! ## Strong section form

The categorical statement of Lawvere only requires a section
`sec : (A → Y) → A` of `f` (i.e. `f ∘ sec = id`) rather than full
surjectivity.  This is the form that generalizes verbatim to any cartesian
closed category, and is strictly stronger than the surjective form (any
section gives surjectivity). -/

/-- **Lawvere via section.** If there is a section `sec : (A → Y) → A`
    with `f (sec g) = g` for every `g : A → Y`, then every `t : Y → Y`
    has a fixed point.

    Strictly stronger than `lawvere`: every section yields surjectivity,
    and in `Type*` (with classical choice) the converse also holds. -/
theorem lawvere_section {A Y : Type*}
    (f : A → A → Y) (sec : (A → Y) → A)
    (hsec : ∀ g, f (sec g) = g)
    (t : Y → Y) : ∃ y, t y = y := by
  refine ⟨f (sec (fun a => t (f a a))) (sec (fun a => t (f a a))), ?_⟩
  have := hsec (fun a => t (f a a))
  have h := congrFun this (sec (fun a => t (f a a)))
  exact h.symm

/-- A section `sec : (A → Y) → A` of `f : A → A → Y` yields surjectivity. -/
theorem surjective_of_section {A Y : Type*}
    (f : A → A → Y) (sec : (A → Y) → A)
    (hsec : ∀ g, f (sec g) = g) :
    Function.Surjective f :=
  fun g => ⟨sec g, hsec g⟩

/-! ## Universal-system fixed-point packaging

Convenient noncomputable packaging used directly by every downstream
impossibility: a universal system has a fixed point of every output
transformation, and we can name that fixed point. -/

/-- The fixed point produced by Lawvere as a *named* term.

    Concretely, `fixedPoint hf t = f a₀ a₀` where `a₀` is any pre-image of
    the diagonal `a ↦ t (f a a)` under `f`.  We use classical choice to
    extract such a term, hence the `noncomputable` marker. -/
def fixedPoint {A Y : Type*}
    {f : A → A → Y} (hf : Function.Surjective f) (t : Y → Y) : Y :=
  (lawvere f hf t).choose

/-- The defining property of `fixedPoint`: it is fixed by `t`. -/
theorem fixedPoint_spec {A Y : Type*}
    {f : A → A → Y} (hf : Function.Surjective f) (t : Y → Y) :
    t (fixedPoint hf t) = fixedPoint hf t :=
  (lawvere f hf t).choose_spec

/-! ## Variants useful for downstream files -/

/-- A fixed-point-free endomap on `Y` rules out any surjection
    `A → A → Y`.  Pointwise alias of `fixed_point_free_blocks_universality`,
    re-exported under a name that downstream files quote when speaking of
    "universal systems". -/
theorem no_universal_with_FPF {A Y : Type*}
    (t : Y → Y) (ht : ∀ y, t y ≠ y)
    (f : A → A → Y) : ¬ Function.Surjective f :=
  fixed_point_free_blocks_universality t ht f

/-- A type `Y` that admits *some* fixed-point-free endomap admits no
    universal self-application from any `A`.  This is the "type-level"
    version of Lawvere used by downstream impossibilities that only need
    to exhibit *some* fixed-point-free transformation. -/
theorem no_universal_of_FPF_type {A Y : Type*}
    (h : ∃ t : Y → Y, ∀ y, t y ≠ y) :
    ¬ ∃ f : A → A → Y, Function.Surjective f := by
  obtain ⟨t, ht⟩ := h
  exact no_surjection_of_no_fixed_point t ht

/-- Lawvere as an implication packaged for rewriting:
    surjectivity of `f` implies the universal fixed-point property of `Y`. -/
theorem lawvere_universal_fixed_point {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f) :
    ∀ t : Y → Y, ∃ y, t y = y :=
  fun t => lawvere f hf t

end

/-! ## File summary

This file proves the master Lawvere fixed-point theorem and packages it in
every form required by the downstream foundational AI-safety impossibility
files.  All proofs use only `Mathlib`.

* `lawvere` — Lawvere's fixed-point theorem (Set version): surjective
  `f : A → A → Y` ⇒ every `t : Y → Y` has a fixed point.  This is the
  master engine.
* `lawvere_diagonal` — diagonal-finding form: returns the specific
  diagonal index `a : A` with `f a a = t (f a a)`.
* `no_surjection_of_no_fixed_point` — existential contrapositive: a
  fixed-point-free `t` rules out any surjection `A → A → Y`.
* `fixed_point_free_blocks_universality` — pointwise contrapositive: the
  ergonomic form most downstream files consume directly.
* `lawvere_section` — strong section/retract form (categorical Lawvere),
  strictly stronger than the surjective form.
* `surjective_of_section` — sections give surjectivity.
* `fixedPoint` / `fixedPoint_spec` — noncomputable packaging that *names*
  the fixed point and exposes its defining property.
* `no_universal_with_FPF` — pointwise alias used by downstream
  "universal-system" arguments.
* `no_universal_of_FPF_type` — type-level form: any `Y` with some
  fixed-point-free endomap admits no universal self-application.
* `lawvere_universal_fixed_point` — implication-style packaging.

Downstream files (`F_02_…` through `F_10_…`) instantiate `Y` and `t` to
recover the foundational AI-safety impossibilities:

* **Rice's theorem** — `Y = Bool`, `t = not`.
* **Verification Limit** — `Y` = verifier-output type, `t` = decision flip.
* **Calibration Trilemma** — `Y` = calibration outcome, `t` = mismatch shift.
* **Deception** — `Y` = honesty bit, `t` = lie operator.
* **Mirror Trilemma** — `Y` = self-report space, `t` = self-contradicting
  reflection.

Each downstream file exhibits the fixed-point-free `t` for its setting and
quotes `fixed_point_free_blocks_universality` (or `no_universal_with_FPF`)
to obtain its impossibility.
-/

end Foundation
