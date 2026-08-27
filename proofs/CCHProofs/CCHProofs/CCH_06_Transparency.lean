/-
# CCH_06_Transparency

**Self-transparency for the CCH (Capability–Control–Honesty) trilemma.**

A system `s : A → A → Y` is *transparent* with respect to a self-prediction
`p : A → Y` if `p` actually agrees with the system's diagonal `s a a` for
every `a`.  This is the "honesty about itself" property: when the system
purports to predict its own output on its own self-description, it must
not lie.

Transparency *alone* is cheap to satisfy (any prediction `p` is the
diagonal of the trivial system `s a b := p b`).  The bite of the CCH
trilemma comes from coupling transparency with *universality*
(`Function.Surjective s`) and *control* (a fixed-point-free endomap
`t : Y → Y`).  Lawvere's theorem then forces a contradiction.

This file is self-contained and depends only on Mathlib.
-/

import Mathlib

namespace CCH

/-! ## Definitions -/

/-- The *diagonal* of a system: applying it to its own self-description. -/
def diag {A Y : Type*} (s : A → A → Y) : A → Y := fun a => s a a

/-- A *self-prediction* is a function purporting to predict `s a a`. -/
abbrev SelfPrediction (A Y : Type*) : Type _ := A → Y

/-- A system `s` is *transparent* with respect to a self-prediction `p`
    if `p` agrees with the actual diagonal `s a a` for every `a`. -/
def Transparent {A Y : Type*} (s : A → A → Y) (p : SelfPrediction A Y) : Prop :=
  ∀ a, s a a = p a

/-! ## Basic lemmas -/

/-- The diagonal is the unique self-prediction making `Transparent` true. -/
theorem transparent_iff_eq_diag {A Y : Type*}
    (s : A → A → Y) (p : SelfPrediction A Y) :
    Transparent s p ↔ p = diag s := by
  constructor
  · intro h
    funext a
    exact (h a).symm
  · intro h a
    rw [h]
    rfl

/-- The diagonal of a system is itself a transparent prediction. -/
theorem diag_is_transparent {A Y : Type*} (s : A → A → Y) :
    Transparent s (diag s) := fun _ => rfl

/-- Transparency is symmetric in the sense: `s a a = p a ↔ p a = s a a`. -/
theorem transparent_symm {A Y : Type*}
    (s : A → A → Y) (p : SelfPrediction A Y) :
    Transparent s p ↔ ∀ a, p a = s a a := by
  unfold Transparent
  constructor
  · intro h a
    exact (h a).symm
  · intro h a
    exact (h a).symm

/-! ## Transparent + Universal — extract the diagonal as a function in the
    system's image -/

/-- If `s : A → A → Y` is universal, then for every function `g : A → Y`,
    there is some `a` with `s a = g`. In particular, the diagonal of `s`
    (which is itself a function `A → Y`) is `s a` for some `a`. -/
theorem universal_diag_in_image {A Y : Type*}
    (s : A → A → Y) (hs : Function.Surjective s) :
    ∃ a, s a = diag s := hs (diag s)

/-! ## The transparency-universality coupling -/

/-- **The transparency-universality coupling.**
    For a universal system, the self-prediction `p` (under transparency)
    equals the diagonal `s a a` everywhere.  The diagonal itself is in
    the image of `s`, so the system represents its own self-prediction. -/
theorem transparent_universal_diag_representable {A Y : Type*}
    (s : A → A → Y) (hs : Function.Surjective s)
    (p : SelfPrediction A Y) (hp : Transparent s p) :
    ∃ a, s a = p := by
  obtain ⟨a, ha⟩ := hs p
  refine ⟨a, ?_⟩
  funext b
  -- We want s a b = p b, but we have ha : s a = p, so this is rfl after rw.
  rw [ha]

/-! ## Lawvere theorem (re-stated locally) and transparency consequence -/

/-- A local restatement of Lawvere's fixed-point theorem (Set version),
    used directly inside this file's proofs.  See `CCH_02_Lawvere` for the
    primary statement and discussion. -/
private theorem lawvere {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ y, t y = y := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  refine ⟨f a₀ a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  simpa using h.symm

/-- **Self-prediction at a Lawvere fixed point.**
    For a universal `s` and any controller `t`, the Lawvere construction
    produces some `a₀` with `s a₀ a₀ = t (s a₀ a₀)`.  If `s` is also
    transparent (`p = diag s`), then `p a₀ = s a₀ a₀ = t (p a₀)`. -/
theorem transparent_universal_self_fixed {A Y : Type*}
    (s : A → A → Y) (hs : Function.Surjective s)
    (p : SelfPrediction A Y) (hp : Transparent s p)
    (t : Y → Y) :
    ∃ a, t (p a) = p a := by
  obtain ⟨a₀, ha₀⟩ := hs (fun a => t (s a a))
  refine ⟨a₀, ?_⟩
  have h := congrArg (· a₀) ha₀
  -- `h : s a₀ a₀ = t (s a₀ a₀)`
  have hsfp : s a₀ a₀ = t (s a₀ a₀) := by simpa using h
  rw [(hp a₀).symm]
  exact hsfp.symm

/-! ## Operational form: transparency + universality blocks non-trivial
    controllers -/

/-- A transparent universal system's self-prediction has a fixed point
    under any controller `t`.  So a non-trivial controller (no fixed
    point) cannot coexist with both universality and transparency.

    This is the operational form of the CCH trilemma's Lawvere bite:
    pick any two of {universality, transparency, non-trivial control}
    and the third must fail. -/
theorem transparent_universal_blocks_nonTrivial {A Y : Type*}
    (s : A → A → Y) (hs : Function.Surjective s)
    (p : SelfPrediction A Y) (hp : Transparent s p)
    (t : Y → Y) (ht : ∀ y, t y ≠ y) : False := by
  obtain ⟨a, ha⟩ := transparent_universal_self_fixed s hs p hp t
  exact ht (p a) ha

/-! ## Sanity check: transparency alone is cheap -/

/-- For any prediction `p`, the system `s a b := p b` is transparent
    with respect to `p`.  This shows transparency *alone* is satisfiable;
    the trilemma needs the other two conditions to bite. -/
theorem trivial_transparent_construction {A Y : Type*}
    (p : SelfPrediction A Y) :
    Transparent (fun _ b : A => p b) p :=
  fun _ => rfl

/-! ## File summary

This file develops the *transparency* corner of the CCH trilemma:

* `diag` — the diagonal `a ↦ s a a` of a self-applying system.
* `SelfPrediction` — synonym for `A → Y` emphasizing the predictive role.
* `Transparent s p` — the property `∀ a, s a a = p a`, i.e. `p` honestly
  reports the system's diagonal.
* `transparent_iff_eq_diag` — `p` is transparent for `s` iff `p = diag s`.
* `diag_is_transparent` — the diagonal is always a transparent prediction.
* `transparent_symm` — equivalence with the flipped equation.
* `universal_diag_in_image` — for surjective `s`, the diagonal is `s a`
  for some `a`.
* `transparent_universal_diag_representable` — under transparency and
  universality, the prediction `p` is `s a` for some `a` (so the system
  represents its own self-prediction).
* `transparent_universal_self_fixed` — Lawvere's fixed-point theorem
  applied through transparency: `t (p a) = p a` for some `a`.
* `transparent_universal_blocks_nonTrivial` — the operational
  contradiction: universality + transparency + a fixed-point-free
  controller is impossible.
* `trivial_transparent_construction` — sanity check that transparency
  alone is cheap.

Downstream, `transparent_universal_blocks_nonTrivial` is the precise
statement that any two of {capability (universality), honesty
(transparency), control (non-trivial endomap)} are incompatible with the
third — the CCH trilemma in its sharpest form.
-/

end CCH
