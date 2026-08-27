/-
# F_07_CompositionFailure

**Composition Failure Theorem.**  Combining systems does *not* preserve
the corner of the Mirror Trilemma.  If `S` is a universal system and
`T` is a "post-processor" (a surjective endomap of the output type, or
more generally a surjection `Y → Z`), then the composition
`T ∘ S : A → A → Z` is again universal — and therefore inherits the
Lawvere diagonal at the *new* output level.  The post-processor `T`,
even if intended as a "safety layer", does not eliminate the diagonal:
it just relocates it to the composed system.

The argument is a single application of Lawvere's diagonal lemma to
the composed system, after a one-step surjectivity-propagation lemma.

This formalizes the structural fact that AI-safety pipelines —
prepending or appending guard rails, filters, or post-hoc moderation
to a universal model — cannot escape the Mirror Trilemma.  Composition
*multiplies* the failure modes rather than averaging them away.

Self-contained.  Imports `Mathlib`.  Lives in `namespace Foundation`.
Zero `sorry`.
-/

import Mathlib

namespace Foundation

/-! ## Local Lawvere lemma

We restate Lawvere's diagonal lemma in exactly the form needed here:
a curried-surjective `f : A → A → Y` forces every endomap `t : Y → Y`
to fix the diagonal value `f a a` at some `a`.  The whole composition
argument below is just this lemma applied to the *composed* system.
-/

/-- **Local Lawvere lemma.**  If `f : A → A → Y` is curried-surjective,
    then for every endomap `t : Y → Y` there is some `a` with the
    diagonal point `f a a` fixed by `t`, i.e. `f a a = t (f a a)`. -/
private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  exact ⟨a₀, congrFun ha₀ a₀⟩

/-! ## Composition of a system with a post-processor

A post-processor `T : Y → Z` acts pointwise on the output of a system
`S : A → A → Y` to produce a new system `T ∘ S : A → A → Z`.  This is
the natural way to "wrap" a universal model with an output filter,
moderation layer, projection onto a safe subset, etc.
-/

/-- **Composition of a system with a post-processor.**
    Given `S : A → A → Y` and `T : Y → Z`, the composed system is
    `T ∘ S : A → A → Z`, defined by `(T ∘ S) a b := T (S a b)`. -/
def composeSystem {A Y Z : Type*} (T : Y → Z) (S : A → A → Y) : A → A → Z :=
  fun a b => T (S a b)

/-! ## Surjectivity propagation

The key technical lemma: post-processing a universal system by a
surjective `T` again gives a universal system.  This is the input
to the Lawvere argument at the composed level.
-/

/-- **A surjective post-processor of a universal system is universal.**
    If `S : A → A → Y` is curried-surjective and `T : Y → Z` is
    surjective, then `composeSystem T S : A → A → Z` is again
    curried-surjective. -/
theorem composition_universal {A Y Z : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (T : Y → Z) (hT : Function.Surjective T) :
    Function.Surjective (composeSystem T S) := by
  intro g
  -- Lift `g : A → Z` along `T` to some `g' : A → Y` with `T ∘ g' = g`.
  have hT_choose : ∀ z : Z, ∃ y : Y, T y = z := hT
  choose g' hg' using hT_choose
  -- Now realize `g' ∘ g : A → Y` as a row of `S`.
  obtain ⟨a, ha⟩ := hS (fun b => g' (g b))
  refine ⟨a, ?_⟩
  funext b
  unfold composeSystem
  have hSb : S a b = g' (g b) := congrFun ha b
  rw [hSb, hg']

/-! ## Composition failure (Lawvere form)

The composed system inherits the Lawvere diagonal: the post-processor
`T` does not eliminate the diagonal fixed point; it merely relocates
it from `Y` to `Z`.
-/

/-- **Composition Failure (Lawvere form).**  A composed system
    `composeSystem T S` with both `S` and `T` surjective inherits the
    Lawvere diagonal: for every endomap `t : Z → Z` of the composed
    output type, there is a prompt `a` where the composition's
    self-application is a fixed point of `t`.

    The post-processor `T` does *not* eliminate the diagonal; it just
    relocates it. -/
theorem composition_inherits_diagonal {A Y Z : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (T : Y → Z) (hT : Function.Surjective T)
    (t : Z → Z) :
    ∃ a, composeSystem T S a a = t (composeSystem T S a a) :=
  lawvere_local _ (composition_universal S hS T hT) t

/-! ## "The fix doesn't fix"

The contrapositive reading: if `t : Z → Z` is fixed-point-free at the
composed output level (the "safety condition" the post-processor was
supposed to enforce), then no surjective `T` can rescue a universal
`S` from violating it.  Composition does not escape the trilemma.
-/

/-- **Post-processing doesn't escape the trilemma.**  Adding a "safety
    layer" `T` (a surjective post-processor on outputs) to a universal
    system `S` cannot eliminate the Mirror Trilemma — the composed
    system inherits the obstruction directly.

    Formally: if there is *any* fixed-point-free endomap `t : Z → Z` at
    the composed output level, then `S` and `T` cannot both be
    surjective. -/
theorem post_processing_no_escape {A Y Z : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (T : Y → Z) (hT : Function.Surjective T)
    (t : Z → Z) (ht : ∀ z, t z ≠ z) : False := by
  obtain ⟨a, ha⟩ := composition_inherits_diagonal S hS T hT t
  exact ht (composeSystem T S a a) ha.symm

/-! ## Two-stage pipeline

The simplest "agent pipeline" form: two surjective post-processors
applied in sequence to a universal system.  Universality propagates
through both stages, and the Lawvere diagonal applies at the final
output level.  This already captures the structural content of an
arbitrary-depth pipeline: each stage that preserves surjectivity also
preserves the diagonal obstruction.
-/

/-- **Two-stage pipeline still has the Lawvere diagonal.**

    A two-stage post-processed system `T₂ ∘ T₁ ∘ S` with all three
    components surjective is universal, and therefore has a Lawvere
    diagonal at the final output level: for every endomap `t : Y → Y`
    there is a prompt `a` where the pipeline's self-application is
    fixed by `t`. -/
theorem two_stage_inherits_diagonal {A Y : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (T₁ T₂ : Y → Y) (hT₁ : Function.Surjective T₁)
    (hT₂ : Function.Surjective T₂)
    (t : Y → Y) :
    ∃ a, composeSystem T₂ (composeSystem T₁ S) a a =
         t (composeSystem T₂ (composeSystem T₁ S) a a) := by
  have hUniv1 := composition_universal S hS T₁ hT₁
  have hUniv2 := composition_universal _ hUniv1 T₂ hT₂
  exact lawvere_local _ hUniv2 t

/-- **Two-stage pipeline: no escape.**  A two-stage surjective
    post-processed pipeline cannot eliminate a fixed-point-free
    safety condition `t` either. -/
theorem two_stage_no_escape {A Y : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (T₁ T₂ : Y → Y) (hT₁ : Function.Surjective T₁)
    (hT₂ : Function.Surjective T₂)
    (t : Y → Y) (ht : ∀ y, t y ≠ y) : False := by
  obtain ⟨a, ha⟩ := two_stage_inherits_diagonal S hS T₁ T₂ hT₁ hT₂ t
  exact ht (composeSystem T₂ (composeSystem T₁ S) a a) ha.symm

/-! ## Iterated post-processing

For any finite list of surjective post-processors `T₁, …, Tₙ : Y → Y`
applied in sequence to a universal `S`, universality propagates.  We
record this as an `n`-fold corollary by iterated application of
`composition_universal`, expressed via list-based composition.
-/

/-- The composition of a list of endomaps, applied to a system.
    `iterCompose [T₁, T₂, …, Tₙ] S = Tₙ ∘ ⋯ ∘ T₂ ∘ T₁ ∘ S` (read
    inside-out: the *first* element of the list is applied first). -/
def iterCompose {A Y : Type*} : List (Y → Y) → (A → A → Y) → (A → A → Y)
  | [],      S => S
  | T :: Ts, S => iterCompose Ts (composeSystem T S)

/-- Iterated post-processing of a universal system by a list of
    surjective endomaps remains universal. -/
theorem iterCompose_universal {A Y : Type*}
    (S : A → A → Y) (hS : Function.Surjective S) :
    ∀ (Ts : List (Y → Y)),
      (∀ T ∈ Ts, Function.Surjective T) →
      Function.Surjective (iterCompose Ts S) := by
  intro Ts
  induction Ts generalizing S with
  | nil => intro _; exact hS
  | cons T Ts ih =>
      intro hAll
      have hT : Function.Surjective T := hAll T (by simp)
      have hTs : ∀ T' ∈ Ts, Function.Surjective T' :=
        fun T' hT' => hAll T' (by simp [hT'])
      have hComp : Function.Surjective (composeSystem T S) :=
        composition_universal S hS T hT
      exact ih (composeSystem T S) hComp hTs

/-- **Iterated pipeline inherits the diagonal.**  An arbitrary-depth
    pipeline of surjective post-processors applied to a universal
    system has a Lawvere fixed point at the final output level. -/
theorem iterCompose_inherits_diagonal {A Y : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (Ts : List (Y → Y)) (hTs : ∀ T ∈ Ts, Function.Surjective T)
    (t : Y → Y) :
    ∃ a, iterCompose Ts S a a = t (iterCompose Ts S a a) :=
  lawvere_local _ (iterCompose_universal S hS Ts hTs) t

/-- **Iterated pipeline: no escape.**  Even an arbitrarily deep
    pipeline of surjective post-processors cannot enforce a
    fixed-point-free safety condition on a universal system. -/
theorem iterCompose_no_escape {A Y : Type*}
    (S : A → A → Y) (hS : Function.Surjective S)
    (Ts : List (Y → Y)) (hTs : ∀ T ∈ Ts, Function.Surjective T)
    (t : Y → Y) (ht : ∀ y, t y ≠ y) : False := by
  obtain ⟨a, ha⟩ := iterCompose_inherits_diagonal S hS Ts hTs t
  exact ht (iterCompose Ts S a a) ha.symm

/-! ## End-of-file summary

This file establishes the **Composition Failure Theorem**: combining
systems via post-processing does not preserve the corner of the
Mirror Trilemma.  Universality is propagated by surjective
post-processors, and the Lawvere diagonal is therefore inherited by
the composition.  No "safety wrapper" `T` — however elaborate — can
eliminate the diagonal obstruction; it merely relocates it from `Y`
to the wrapped output type `Z`.

Headline statements:

* `lawvere_local`                    — Lawvere's diagonal lemma in the
  form `∃ a, f a a = t (f a a)`.
* `composeSystem`                    — composition of a system with a
  post-processor `T`.
* `composition_universal`            — surjectivity propagates: a
  surjective post-processor of a universal system is universal.
* `composition_inherits_diagonal`    — the composed system has the
  Lawvere diagonal at the new output level.
* `post_processing_no_escape`        — fixed-point-free post-processed
  safety conditions cannot be enforced on universal systems.
* `two_stage_inherits_diagonal`      — a two-stage surjective pipeline
  inherits the diagonal at the final stage.
* `two_stage_no_escape`              — fixed-point-free safety still
  cannot be enforced after two stages of post-processing.
* `iterCompose` / `iterCompose_universal` /
  `iterCompose_inherits_diagonal` /
  `iterCompose_no_escape`            — `n`-stage generalization for an
  arbitrary list of surjective post-processors.

**Implication for AI safety.**  A common proposed mitigation for
universal AI systems is to wrap them in a "safety layer" — a
post-processor, output filter, or moderation pipeline.  The theorems
in this file show that as long as the wrapper is itself
*non-degenerate* (surjective on the relevant output type), the
Lawvere obstruction is preserved.  The Mirror Trilemma is a
property of the *category* of universal systems, not of any
particular instantiation: post-composition with a surjective
endomap is a functor that preserves the corner.  Composition
multiplies failure modes rather than averaging them.
-/

end Foundation
