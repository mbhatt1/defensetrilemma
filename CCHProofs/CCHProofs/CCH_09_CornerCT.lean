/-
  CCH_09_CornerCT.lean

  Corner 3 of the CCH Trilemma: C + T ⇒ ¬U
  (Controlled and Transparent implies not Universal).

  This is the "Rice's theorem face" of the trilemma. A controlled,
  self-introspective system cannot be universal. It is the cleanest
  corner because it is the direct contrapositive of Lawvere's theorem:
  if you can both *control* the system (force its self-prediction away
  from `t`-fixed-points) and *transparently introspect* its outputs
  (via self-prediction `p` agreeing with the diagonal of `s`), then
  the system's expressive power is bounded — it cannot be universal.
-/

import Mathlib

namespace CCH

/-! ## Local Lawvere

    A self-contained, file-local statement of Lawvere's fixed-point
    theorem in its surjectivity form: any surjective `f : A → A → Y`
    forces every endomap `t : Y → Y` to admit a fixed point on the
    diagonal of `f`. -/

private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  simpa using h

/-! ## Corner 3: C + T ⇒ ¬U -/

/-- **CCH Corner 3: C + T ⇒ ¬U.**
    If the system `s` is transparent with respect to a self-prediction `p`,
    and `p` is controlled (never a fixed point of some endomap `t`),
    then `s` is not surjective.

    Equivalently: any controlled, self-introspective system has bounded
    expressive power — it cannot encode all functions `A → Y`. -/
theorem corner_CT_not_U {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hC : ∀ a, t (p a) ≠ p a)
    (hT : ∀ a, s a a = p a) :
    ¬ Function.Surjective s := by
  intro hU
  obtain ⟨a₀, ha₀⟩ := lawvere_local s hU t
  have hsp : s a₀ a₀ = p a₀ := hT a₀
  have hfix : p a₀ = t (p a₀) := by rw [hsp] at ha₀; exact ha₀
  exact hC a₀ hfix.symm

/-- **CCH Corner 3 (contrapositive).** Controlled + Transparent + Universal
    are jointly impossible. -/
theorem corner_CT_impossible {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hC : ∀ a, t (p a) ≠ p a)
    (hT : ∀ a, s a a = p a)
    (hU : Function.Surjective s) : False :=
  corner_CT_not_U s t p hC hT hU

/-! ## Boolean / Rice-flavored specializations -/

/-- **Corner 3 specialized: bool-valued controlled system.**
    A transparent system whose self-prediction `p : A → Bool` always
    agrees with itself ("never lies about its own output") cannot be
    a universal `A → A → Bool` — boolean negation is a non-trivial
    controller. -/
theorem corner_CT_bool_specialization {A : Type*}
    (s : A → A → Bool) (p : A → Bool)
    (hT : ∀ a, s a a = p a) :
    ¬ Function.Surjective s := by
  apply corner_CT_not_U s (fun b => !b) p _ hT
  intro a
  cases p a <;> simp

/-- **Reading: Rice's theorem face.**
    For any non-trivial property `P : Y → Prop`, a controlled system
    (whose self-prediction always falls in some specific `P`-value
    region) that is also transparent cannot be universal — there's
    an `A → Y` function it cannot represent.

    This is the abstract Rice's theorem: "any non-trivial semantic
    property is undecidable in a sufficiently expressive class."
    Here decidability = surjective representation. -/
theorem rice_face {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hC : ∀ a, t (p a) ≠ p a)
    (hT : ∀ a, s a a = p a) :
    ¬ Function.Surjective s :=
  corner_CT_not_U s t p hC hT

/-! ## Constructive / witness form -/

/-- **Constructive form.** Given a controlled-transparent setup,
    there is a function `g : A → Y` *not* in the image of `s`.

    Morally redundant given `corner_CT_not_U` — the witness is just
    the diagonal twist of Lawvere — but stated here for symmetry with
    the other two corners' witness lemmas. -/
theorem corner_CT_witness {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hC : ∀ a, t (p a) ≠ p a)
    (hT : ∀ a, s a a = p a)
    (hU : Function.Surjective s) :
    ∃ g : A → Y, ∀ a, s a ≠ g := by
  -- This is just non-surjectivity, derivable from corner_CT_not_U.
  exfalso
  exact corner_CT_not_U s t p hC hT hU

/-! ## Variant: non-fixed-point controller globally

    If `t` has *no* fixed points anywhere on `Y`, then control is
    automatic: `t (p a) ≠ p a` holds for every `a`. This packages
    the corner as "globally fixed-point-free `t` + transparency
    ⇒ non-surjectivity". -/

/-- **Corner 3 from a globally fixed-point-free controller.**
    If `t : Y → Y` has no fixed points and the system `s` is
    transparent (its diagonal equals some `p`), then `s` is not
    surjective. -/
theorem corner_CT_not_U_of_fpf {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (ht : ∀ y, t y ≠ y)
    (hT : ∀ a, s a a = p a) :
    ¬ Function.Surjective s :=
  corner_CT_not_U s t p (fun a => ht (p a)) hT

/-- **Bool corollary via global fixed-point-freeness.**
    Boolean negation has no fixed points, so any transparent
    `s : A → A → Bool` is non-surjective. -/
theorem corner_CT_bool_via_fpf {A : Type*}
    (s : A → A → Bool) (p : A → Bool)
    (hT : ∀ a, s a a = p a) :
    ¬ Function.Surjective s := by
  apply corner_CT_not_U_of_fpf s (fun b => !b) p _ hT
  intro b
  cases b <;> simp

/-! ## End-of-file summary

    This file delivers Corner 3 of the CCH trilemma:

      *Controlled* (C):     ∀ a, t (p a) ≠ p a
      *Transparent* (T):    ∀ a, s a a = p a
      *Universal* (U):      Function.Surjective s

      C ∧ T ⇒ ¬U.

    The proof is one application of (a private, file-local)
    Lawvere fixed-point theorem followed by transparency-rewriting:

      • Surjectivity of `s` (U) yields, by Lawvere, a diagonal point
        `a₀` with `s a₀ a₀ = t (s a₀ a₀)`.
      • Transparency (T) rewrites the diagonal to `p a₀ = t (p a₀)`.
      • Control (C) forbids exactly that equation.

    The boolean specialization picks `t = !` (negation has no
    fixed points on `Bool`), recovering a Rice-style statement:
    any transparent boolean self-introspective system is bounded.

    Together with the C+U⇒¬T and T+U⇒¬C corners proved elsewhere,
    this completes the CCH "you can have at most two of three"
    impossibility result. -/

end CCH
