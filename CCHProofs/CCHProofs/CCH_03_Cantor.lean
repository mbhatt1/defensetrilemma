import Mathlib

/-
  CCH_03_Cantor.lean

  Part 3 of the "Capability Containment Hierarchy" (CCH) formalization.

  **Core result: Cantor's theorem as a Lawvere instance.**

  Cantor's theorem says there is no surjection from a set `A` to its
  powerset.  In Lawvere's fixed-point form this becomes:

    `Bool` admits the fixed-point-free endomap `not`, hence no
    surjection `A → (A → Bool)` can exist (otherwise Lawvere's lemma
    would manufacture a fixed point of `not`).

  This file is *self-contained*: rather than importing `CCH_02_Lawvere`
  we re-prove the small piece of Lawvere's lemma we need locally.

  Contents:

    1. `lawvere_local` (private) — the diagonal fixed-point lemma:
       any surjection `f : A → A → Y` together with `t : Y → Y`
       produces a fixed point of `t`.
    2. `bool_not_no_fixed_point` — `!b ≠ b` for every `b : Bool`.
    3. `cantor_no_surjection` — Cantor's theorem in Lawvere form:
       no `f : A → A → Bool` is surjective.
    4. `cantor_no_surjection_set` — Cantor's theorem in classical
       set-theoretic form: no `f : A → Set A` is surjective.
    5. `no_universal_bool_system` — CCH-flavoured corollary phrasing
       the same obstruction in terms of safety-judgement systems.
-/

namespace CCH

/-! ## 1. Local Lawvere Fixed-Point Lemma

    A standalone re-statement of Lawvere's diagonal argument, kept
    `private` so it does not pollute the public CCH namespace.  We
    re-prove it here so this file does not depend on
    `CCH_02_Lawvere.lean`.

    **Statement.**  If `f : A → A → Y` is surjective and `t : Y → Y`
    is *any* endomap, then `t` has a fixed point.

    **Proof.**  Surjectivity supplies an `a₀` with
    `f a₀ = fun a => t (f a a)`.  Specialising at `a = a₀` gives
    `f a₀ a₀ = t (f a₀ a₀)`. -/
private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ y, t y = y := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨f a₀ a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  simpa using h.symm

/-! ## 2. `Bool.not` is Fixed-Point Free

    The two-element type `Bool` carries a canonical fixed-point-free
    endomap, namely Boolean negation.  This is the *witness* that
    feeds Lawvere's lemma to derive Cantor's theorem.
-/

/-- **`Bool.not` has no fixed point.** For every `b : Bool`, `!b ≠ b`. -/
theorem bool_not_no_fixed_point : ∀ b : Bool, !b ≠ b := by
  intro b
  cases b <;> simp

/-! ## 3. Cantor's Theorem (Lawvere Form)

    Combining the local Lawvere lemma with the fact that `Bool.not`
    has no fixed point yields Cantor's theorem in the form most
    convenient for the CCH project.
-/

/--
**Cantor's theorem.**  No function `A → (A → Bool)` is surjective.

If `f : A → A → Bool` were surjective, applying `lawvere_local`
with `t = Bool.not` would produce a `b : Bool` with `!b = b`,
contradicting `bool_not_no_fixed_point`.
-/
theorem cantor_no_surjection {A : Type*} :
    ¬ ∃ f : A → A → Bool, Function.Surjective f := by
  rintro ⟨f, hf⟩
  -- Pick the diagonal-flipping function
  obtain ⟨a₀, ha₀⟩ := hf (fun a => !(f a a))
  have h : f a₀ a₀ = !(f a₀ a₀) := congrFun ha₀ a₀
  -- Case on the value at the diagonal; both cases are absurd.
  cases hb : f a₀ a₀ <;> rw [hb] at h <;> simp at h

/-! ## 4. Cantor's Theorem (Set Form)

    The classical statement: there is no surjection from a set onto
    its powerset.  We give a *direct* Russell-style diagonal proof
    rather than going through `Bool`, since the `Set`-level proof is
    notationally cleaner and emphasises the diagonal pattern.
-/

/--
**Cantor's theorem (set form).**  No function `A → Set A` is
surjective.

The proof is Russell's diagonal: if `f` were surjective, the set
`D = {x | x ∉ f x}` would have a preimage `a`, but then `a ∈ D ↔
a ∉ f a ↔ a ∉ D`, a contradiction.
-/
theorem cantor_no_surjection_set {A : Type*} :
    ¬ ∃ f : A → Set A, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf {x | x ∉ f x}
  -- `ha : f a = {x | x ∉ f x}`, so membership in `f a` is equivalent
  -- to non-membership in `f a`, a direct contradiction.
  have key : a ∈ f a ↔ a ∉ f a := by
    have h₁ : a ∈ f a ↔ a ∈ ({x | x ∉ f x} : Set A) := by rw [ha]
    simpa [Set.mem_setOf_eq] using h₁
  by_cases h : a ∈ f a
  · exact key.mp h h
  · exact h (key.mpr h)

/-! ## 5. CCH-Flavoured Corollary

    A direct restatement of Cantor's theorem in language closer to
    the CCH project: any system whose only outputs are Boolean
    "safe / unsafe" judgements cannot universally express its own
    judgements about every input it might face.
-/

/--
**CCH applied to Boolean outputs.**  No system `s : A → A → Bool`
can be surjective.

Equivalently: any LLM (or evaluator) that answers a yes/no question
about pairs of "prompts" cannot universally express *every*
Boolean-valued judgement on `A`.  This is just `cantor_no_surjection`
re-named to fit the CCH narrative.
-/
theorem no_universal_bool_system {A : Type*} :
    ¬ ∃ s : A → A → Bool, Function.Surjective s := cantor_no_surjection

/-! ## Summary

| # | Statement                                | Status  |
|---|------------------------------------------|---------|
| 1 | `lawvere_local` (private fixed-point)    | Proved  |
| 2 | `bool_not_no_fixed_point`                | Proved  |
| 3 | `cantor_no_surjection` (Lawvere form)    | Proved  |
| 4 | `cantor_no_surjection_set` (Set form)    | Proved  |
| 5 | `no_universal_bool_system` (CCH form)    | Proved  |

All results are sorry-free.  The Lawvere form (`cantor_no_surjection`)
is the workhorse used downstream in the CCH trilemma: it provides the
*diagonal* obstruction complementing the topological obstruction
formalised in the `HoF` files.  The `Set`-form proof is given via a
direct Russell diagonal for notational clarity, while the
`Bool`-output corollary is the form actually quoted in the CCH
narrative about safety-judgement systems.
-/

end CCH
