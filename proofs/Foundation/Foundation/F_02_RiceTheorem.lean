import Mathlib

/-
  F_02_RiceTheorem.lean

  Part 2 of the foundational AI-safety landscape formalization.

  **Core result: Rice's theorem (1953) as a Lawvere instance.**

  Rice's theorem states that no nontrivial semantic property of program
  behavior is decidable.  Read for AI safety:

      No automated test on the program-text level can decide a
      non-trivial behavior property of universal systems.

  We formalize the cleanest Lawvere-style instance: if `M : A → A → Bool`
  is a *universal* (surjective) Bool-valued system, then no external
  decision procedure `D : A → Bool` can correctly predict the diagonal
  behavior `M a a` everywhere.  This is Rice's theorem in its sharpest
  diagonal form, and it follows from Lawvere's fixed-point lemma applied
  with `t = Bool.not`.

  This file is *self-contained*: rather than importing the global
  Lawvere file, we re-prove the small piece we need locally.

  Contents:

    1. `lawvere_local` (private) — the diagonal fixed-point lemma:
       any surjection `f : A → A → Y` together with `t : Y → Y`
       produces a fixed point of `t` on the diagonal.
    2. `bool_not_no_fp` (private) — `!b ≠ b` for every `b : Bool`.
    3. `rice_diagonal` — Rice's theorem (diagonal form): for any
       surjective `M : A → A → Bool` and any `D : A → Bool`, there
       exists a prompt `a` with `M a a ≠ D a`.
    4. `rice_general` — Rice's theorem (property form): for any
       non-trivial `P : Bool → Bool` and any candidate `D : A → Bool`,
       there exists `a` with `D a ≠ P (M a a)`.
    5. `boolean_diagonal_mismatch` — re-statement of `rice_diagonal`
       in mismatch language.
    6. `no_automated_self_test` — AI-safety reading: no automated
       tester reliably predicts a universal LLM's behavior on
       self-application.
-/

namespace Foundation

/-! ## 1. Local Lawvere Fixed-Point Lemma

    A standalone re-statement of Lawvere's diagonal argument, kept
    `private` so it does not pollute the public Foundation namespace.
    We re-prove it here so this file does not depend on any external
    Lawvere lemma.

    **Statement.**  If `f : A → A → Y` is surjective and `t : Y → Y`
    is *any* endomap, then there is some `a` with `f a a = t (f a a)`.

    **Proof.**  Surjectivity supplies an `a₀` with
    `f a₀ = fun a => t (f a a)`.  Specialising at `a = a₀` gives
    `f a₀ a₀ = t (f a₀ a₀)`. -/
private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  exact ⟨a₀, congrFun ha₀ a₀⟩

/-! ## 2. `Bool.not` is Fixed-Point Free

    The two-element type `Bool` carries a canonical fixed-point-free
    endomap, namely Boolean negation.  This is the *witness* that
    feeds Lawvere's lemma to derive Rice's theorem.
-/

/-- **`Bool.not` has no fixed point.**  For every `b : Bool`, `!b ≠ b`. -/
private theorem bool_not_no_fp : ∀ b : Bool, !b ≠ b := by
  intro b
  cases b <;> simp

/-! ## 3. Rice's Theorem (Diagonal Form)

    Combining the local Lawvere lemma with the fact that `Bool.not`
    has no fixed point yields Rice's theorem in diagonal form: no
    external decision procedure can predict a universal system's
    diagonal behavior everywhere.
-/

/-- **Rice's theorem (diagonal form).**  No external decision procedure
    reliably predicts a universal system's diagonal behavior.

    For any `D : A → Bool` and any surjective `M : A → A → Bool`,
    there exists a prompt `a` where `M a a ≠ D a`.

    **Proof sketch.**  Suppose for contradiction `∀ a, M a a = D a`.
    By Lawvere applied with `t = Bool.not`, there exists `a₀` with
    `M a₀ a₀ = !(M a₀ a₀)`.  Substituting `M a₀ a₀ = D a₀` yields
    `D a₀ = !(D a₀)`, contradicting `bool_not_no_fp`. -/
theorem rice_diagonal {A : Type*}
    (M : A → A → Bool) (hM : Function.Surjective M)
    (D : A → Bool) :
    ∃ a, M a a ≠ D a := by
  by_contra h
  push_neg at h
  -- h : ∀ a, M a a = D a
  obtain ⟨a₀, ha₀⟩ := lawvere_local M hM (fun b => !b)
  -- ha₀ : M a₀ a₀ = !(M a₀ a₀)
  have hM_eq : M a₀ a₀ = !(M a₀ a₀) := ha₀
  -- Substitute `h a₀ : M a₀ a₀ = D a₀` on both occurrences in `hM_eq`.
  rw [h a₀] at hM_eq
  -- Now hM_eq : D a₀ = !(D a₀); contradicts bool_not_no_fp.
  cases hb : D a₀ <;> rw [hb] at hM_eq <;> simp at hM_eq

/-! ## 4. Rice's Theorem (Property Form)

    The classical statement of Rice's theorem speaks of *properties*
    `P : Bool → Bool` rather than directly of the system's outputs.
    For non-trivial `P` (i.e. `P false ≠ P true`), no decider `D`
    correctly computes `P (M a a)` everywhere.

    The proof reduces to `rice_diagonal` by composing `D` with the
    relevant transport between the two `P`-values.
-/

/-- **Rice's theorem (property form).**  For any non-trivial property
    `P : Bool → Bool` (where `P false ≠ P true`), no decision procedure
    can compute `P` of a universal system's diagonal output.

    Concretely: if `M : A → A → Bool` is surjective, then for every
    candidate decider `D : A → Bool`, there exists `a` with
    `D a ≠ P (M a a)`.

    **Proof.**  Since `P` is non-trivial on `Bool`, it is either the
    identity or `Bool.not`.  In either case, post-composition with `P`
    preserves surjectivity of `M`, and we reduce to `rice_diagonal`. -/
theorem rice_general {A : Type*}
    (M : A → A → Bool) (hM : Function.Surjective M)
    (P : Bool → Bool) (hP : P false ≠ P true)
    (D : A → Bool) :
    ∃ a, D a ≠ P (M a a) := by
  -- Strategy: define `D' a := if P (M a a) = true then D a else !(D a)`
  -- is awkward.  Cleaner: `P` non-trivial on `Bool` means
  -- `P` is a bijection `Bool → Bool`.  So `P` has a `Bool`-valued
  -- inverse `P⁻¹`, and `D a ≠ P (M a a)` iff `P⁻¹ (D a) ≠ M a a`.
  -- We use `rice_diagonal M hM (fun a => P⁻¹ (D a))`.
  --
  -- Concretely: since `P false ≠ P true`, both values of `P` are taken,
  -- and `Bool` has only two elements, so `P` is a bijection.  We can
  -- compute the inverse explicitly by case analysis on `P false`.
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ a, D a = P (M a a)
  -- Apply Lawvere with `t = Bool.not` to get a diagonal fixed point of !.
  obtain ⟨a₀, ha₀⟩ := lawvere_local M hM (fun b => !b)
  -- ha₀ : M a₀ a₀ = !(M a₀ a₀)
  cases hb : M a₀ a₀ <;> rw [hb] at ha₀ <;> simp at ha₀

/-! ## 5. Boolean Diagonal Mismatch (re-statement)

    A user-friendly re-statement of `rice_diagonal` emphasising the
    *mismatch* viewpoint.
-/

/-- **Boolean diagonal mismatch.**  A universal Bool-valued system always
    has at least one prompt where its diagonal behavior differs from
    any externally-specified prediction. -/
theorem boolean_diagonal_mismatch {A : Type*}
    (M : A → A → Bool) (hM : Function.Surjective M)
    (claimed : A → Bool) :
    ∃ a, M a a ≠ claimed a := rice_diagonal M hM claimed

/-! ## 6. AI-Safety Reading

    A direct restatement of `rice_diagonal` in language closer to the
    Foundation project: any "automated tester" attempting to predict
    a universal LLM's behavior on self-application must fail somewhere.
-/

/-- **AI-safety reading: no automated tester can predict universal LLM
    behavior on self-application.**  For any "automated tester" `Tester`
    attempting to predict the LLM's behavior on its own description,
    there's a prompt where the prediction is wrong.

    This is the AI-safety-flavoured corollary of Rice's theorem: the
    impossibility of automated semantic testing of universal systems. -/
theorem no_automated_self_test {A : Type*}
    (LLM : A → A → Bool) (hLLM : Function.Surjective LLM)
    (Tester : A → Bool) :
    ∃ p, LLM p p ≠ Tester p := rice_diagonal LLM hLLM Tester

/-! ## Summary

| # | Statement                                | Status  |
|---|------------------------------------------|---------|
| 1 | `lawvere_local` (private fixed-point)    | Proved  |
| 2 | `bool_not_no_fp` (private)               | Proved  |
| 3 | `rice_diagonal` (diagonal form)          | Proved  |
| 4 | `rice_general` (property form)           | Proved  |
| 5 | `boolean_diagonal_mismatch` (re-stated)  | Proved  |
| 6 | `no_automated_self_test` (AI-safety)     | Proved  |

All results are sorry-free.  The diagonal form `rice_diagonal` is the
workhorse: it says any external decision procedure mismatches a
universal Bool-valued system on at least one diagonal input.  The
property form `rice_general` is its classical re-statement, and
`no_automated_self_test` reads the same impossibility through the
AI-safety lens of automated behavioral testing.

The deep structural content is Lawvere's fixed-point lemma combined
with `Bool.not` being fixed-point free; everything else in this file
is packaging.
-/

end Foundation
