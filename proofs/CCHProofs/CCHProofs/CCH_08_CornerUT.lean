/-
# CCH_08_CornerUT

**Corner 2 of the CCH trilemma: U + T ⇒ ¬C.**

A *universal*, *self-honest* (transparent) system cannot also be
*controlled* in the sense that its self-prediction is forbidden from
ever taking the value of a fixed point of an external endomap.

Concretely: if `s : A → A → Y` is surjective, `p : A → Y` is its
diagonal (transparency: `s a a = p a`), and `t : Y → Y` is a
"controller" demanding `t (p a) ≠ p a` for every `a`, then a
contradiction follows.  The proof is Lawvere's diagonal argument: the
Lawvere construction produces an `a₀` with `s a₀ a₀ = t (s a₀ a₀)`,
and transparency rewrites this as `p a₀ = t (p a₀)`, contradicting
the controller hypothesis.

This is structurally the same proof as Corner 1 (U + C ⇒ ¬T) but
read with a different "active" hypothesis: in Corner 1 transparency
is the property forced to fail; here it is controlledness.  The
diagonal argument is symmetric across this re-labeling — see
`cornerUT_eq_cornerUC_proof` for the documentation lemma.

This file is self-contained and depends only on Mathlib.
-/

import Mathlib

namespace CCH

/-! ## Local Lawvere fixed-point lemma

A pointwise restatement of Lawvere's theorem suitable for the
diagonal-argument proofs in this file.  See `CCH_02_Lawvere` for the
primary statement and `CCH_06_Transparency` for the consequence used
in Corner 1. -/

/-- **Local Lawvere.**  For a surjective `f : A → A → Y` and any
    endomap `t : Y → Y`, the diagonal `a ↦ f a a` hits a `t`-fixed
    point: there exists `a` with `f a a = t (f a a)`. -/
private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  simpa using h

/-! ## Corner 2: the U + T face of the trilemma -/

/-- **CCH Corner 2: U + T ⇒ ¬C.**

    If a system `s` is universal AND transparent with respect to its
    self-prediction `p`, then `p` cannot be controlled away from any
    fixed point of an arbitrary endomap `t`.

    Equivalently: a universal self-honest system cannot have its
    self-prediction restricted by an external controller — the
    diagonal argument forces the prediction to hit a "forbidden"
    value somewhere. -/
theorem corner_UT_not_C {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hT : ∀ a, s a a = p a) :
    ¬ (∀ a, t (p a) ≠ p a) := by
  intro hC
  obtain ⟨a₀, ha₀⟩ := lawvere_local s hU t
  have hsp : s a₀ a₀ = p a₀ := hT a₀
  -- ha₀ : s a₀ a₀ = t (s a₀ a₀)
  -- hsp : s a₀ a₀ = p a₀
  -- So p a₀ = t (p a₀), contradicting hC.
  have hfix : p a₀ = t (p a₀) := by
    rw [← hsp]
    exact ha₀
  exact hC a₀ hfix.symm

/-- **CCH Corner 2 (contrapositive form).**

    Universal + Transparent + Controlled is jointly impossible.  This
    is the literal "any two of three" reading of the CCH trilemma at
    the U+T face: assume all three hypotheses, derive `False`. -/
theorem corner_UT_impossible {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hT : ∀ a, s a a = p a)
    (hC : ∀ a, t (p a) ≠ p a) : False :=
  corner_UT_not_C s t p hU hT hC

/-! ## Hallucination-trilemma reading -/

/-- **Reading: the Hallucination Trilemma face.**

    Interpreting `Y` as confidence/answer values and `t` as the
    "controller's forbidden value rule" (no fixed point of `t` = the
    controller insists on avoiding some output), the universal
    transparent system *must* hit that forbidden value via its
    diagonal — contradicting the controller.

    This is the precise content of the Hallucination Trilemma face of
    CCH: a universal calibrated honest predictor cannot be steered
    away from a target answer by any external rule, because Lawvere's
    diagonal forces every endomap to have a fixed point reached by
    the diagonal `s a a = p a`. -/
theorem hallucination_trilemma_face {A Y : Type*}
    (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : Function.Surjective s)
    (hT : ∀ a, s a a = p a)
    (hC : ∀ a, t (p a) ≠ p a) : False :=
  corner_UT_impossible s t p hU hT hC

/-! ## Symmetry with Corner 1 -/

/-- The U+T corner has the same proof structure as the U+C corner
    (`CCH_07_CornerUC`), differing only in which hypothesis is read
    as the "active" constraint and which as the "violated" conclusion.

    In Corner 1, transparency is the property forced to fail given
    universality and a fixed-point-free controller.  In Corner 2,
    controlledness (the controller hypothesis `∀ a, t (p a) ≠ p a`)
    is the property forced to fail given universality and
    transparency.  The Lawvere diagonal construction is symmetric in
    this regard — both readings extract the same fixed-point witness
    `a₀` with `s a₀ a₀ = t (s a₀ a₀)`.

    This is purely a documentation lemma. -/
theorem cornerUT_eq_cornerUC_proof : True := trivial

/-! ## Sanity-check witnesses -/

/-- The U+T corner is non-vacuous: there exist instantiations of
    `(A, Y, s, t, p)` with `hU` and `hT` satisfied but `hC` violated.
    Take `A := Unit`, `Y := Unit`, `s := fun _ _ => ()`, `p := id`,
    `t := id`.  Then `s` is surjective (the only function `Unit → Unit`
    is the constant one), `p = diag s`, and `t (p ()) = () = p ()` —
    the controller has fixed points everywhere, so `hC` fails as
    Corner 2 demands. -/
theorem corner_UT_witness_identity :
    let s : Unit → Unit → Unit := fun _ _ => ()
    let p : Unit → Unit := id
    let t : Unit → Unit := id
    Function.Surjective s ∧ (∀ a, s a a = p a) ∧ ¬ (∀ a, t (p a) ≠ p a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g
    refine ⟨(), ?_⟩
    funext u
    exact Subsingleton.elim _ _
  · intro _; exact Subsingleton.elim _ _
  · intro h; exact h () rfl

/-- The U+T corner says nothing about non-universal systems: drop
    universality and the conclusion fails.  With `A := Unit`,
    `Y := Bool`, `s := fun _ _ => false`, `p := fun _ => false`,
    `t := not`: `s` is *not* surjective, transparency holds, and the
    controller `t = not` has no fixed point on `Bool`, so all three
    of (T, C, ¬U) coexist. -/
theorem corner_UT_needs_universality :
    (∀ a : Unit, (fun _ _ : Unit => false) a a = (fun _ : Unit => false) a) ∧
    (∀ a : Unit, (not : Bool → Bool) ((fun _ : Unit => false) a) ≠
                  (fun _ : Unit => false) a) ∧
    ¬ Function.Surjective (fun _ _ : Unit => false : Unit → Unit → Bool) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _; rfl
  · intro _; simp
  · intro hs
    obtain ⟨_, h⟩ := hs (fun _ => true)
    have hbool : (false : Bool) = true := by
      have := congrFun h ()
      simpa using this
    exact Bool.false_ne_true hbool

/-! ## File summary

This file establishes the **U + T ⇒ ¬C** corner of the CCH trilemma.

The hypotheses play the following roles:

* **`hU : Function.Surjective s`** — *Universality.*  The system can
  produce, on some self-description, every output in `Y`.  This is
  what powers Lawvere's diagonal construction: surjectivity of the
  curried `s : A → A → Y` lets us realize `a ↦ t (s a a)` as `s a₀`
  for some `a₀`, which (specialized at `a₀`) yields the Lawvere
  fixed-point equation `s a₀ a₀ = t (s a₀ a₀)`.

* **`hT : ∀ a, s a a = p a`** — *Transparency.*  The self-prediction
  `p` honestly reports the system's diagonal.  This is what lets us
  rewrite the Lawvere fixed-point equation in terms of `p`:
  `p a₀ = s a₀ a₀ = t (s a₀ a₀) = t (p a₀)`.

* **`hC : ∀ a, t (p a) ≠ p a`** — *Controlledness.*  The controller
  `t` is "non-trivial along the prediction": it never agrees with
  `p` at any input.  This is the hypothesis that finally fails — the
  Lawvere fixed-point produced by `hU` and rewritten by `hT` is
  exactly an `a₀` with `t (p a₀) = p a₀`, contradicting `hC`.

The main results:

* `lawvere_local` — local restatement of Lawvere's theorem yielding
  the explicit fixed-point witness `a` such that `f a a = t (f a a)`.
* `corner_UT_not_C` — the headline implication: under universality
  and transparency, the controller hypothesis `hC` must fail.
* `corner_UT_impossible` — contrapositive form: U + T + C ⇒ False.
* `hallucination_trilemma_face` — the Hallucination-Trilemma reading
  of the corner.
* `cornerUT_eq_cornerUC_proof` — documentation lemma noting the
  structural identity of Corners 1 and 2 up to re-labeling.
* `corner_UT_witness_identity` — non-vacuity check: U + T can hold
  while `hC` fails.
* `corner_UT_needs_universality` — universality is necessary: T + C
  alone is consistent.

Together with `CCH_06_Transparency` (the operational form) and
`CCH_07_CornerUC` (the U + C ⇒ ¬T face), this file completes the
"two-out-of-three" structure of the CCH trilemma: any two of
{Capability/Universality, Honesty/Transparency, Control/non-trivial
endomap} preclude the third.
-/

end CCH
