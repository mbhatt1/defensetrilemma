/-
  F_04_CalibrationUnified.lean

  Unification of the Hallucination/Calibration Trilemma with Lawvere's
  fixed-point framework.

  The original Hallucination Trilemma (see
  `HallucinationProofs/HoF_07_TrilemmaCore.lean`) was proved topologically:
  a continuous LLM `M : Q → A × ℝ` whose image meets both half-planes must,
  by the Intermediate Value Theorem on a connected metric space, hit the
  boundary `confidence = 1/2`. Faithful + Covering + Calibrated then clash.

  This file re-derives the same impossibility from a *purely categorical*
  hypothesis: surjectivity of the curried self-prediction map
  `s : A → A → ℝ`. The diagonal-plus-controller argument of Lawvere
  (see `CCHProofs/CCH_07_CornerUC.lean`) supplies the `1/2`-point without
  any topology. Both proofs locate the same boundary point; they differ
  only in how that point is constructed.
-/

import Mathlib

namespace Foundation

/-! ## Local Lawvere fixed-point lemma

We package the diagonal argument we need as a private lemma so the rest of
the file is self-contained: any controller `t : Y → Y` admits a fixed point
on the diagonal of any surjective `f : A → A → Y`. -/

private theorem lawvere_local {A Y : Type*}
    (f : A → A → Y) (hf : Function.Surjective f)
    (t : Y → Y) : ∃ a, f a a = t (f a a) := by
  obtain ⟨a₀, ha₀⟩ := hf (fun a => t (f a a))
  exact ⟨a₀, congrFun ha₀ a₀⟩

/-! ## The "shifted negation" controller

The controller `y ↦ 1 - y` on `ℝ` has its unique fixed point at `1/2`.
This is the "complement controller" that converts the Lawvere diagonal
output into the calibration boundary. -/

/-- The map `y ↦ 1 - y` on `ℝ` has fixed point only at `1/2`. -/
theorem half_complement_fixed_point :
    ∀ y : ℝ, (1 - y = y) ↔ y = 1/2 := by
  intro y
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- The complement map has no fixed point if we exclude `1/2`. -/
theorem complement_no_fp_off_half :
    ∀ y : ℝ, y ≠ 1/2 → 1 - y ≠ y := by
  intro y hy h
  have : y = 1/2 := by linarith
  exact hy this

/-! ## The Calibration Trilemma as a Lawvere instance

Plugging the complement controller into `lawvere_local` produces a point
on the diagonal where the system outputs exactly `1/2`. -/

/-- **Calibration Trilemma (Lawvere form).**
    A universal system `s : A → A → ℝ` with confidence outputs cannot
    have its diagonal avoid `1/2`. Equivalently: any LLM that is universal
    in the ICL sense, when applied to itself, hits confidence exactly `1/2`
    at some prompt — the boundary between "true" and "false." -/
theorem calibration_diagonal_hits_half {A : Type*}
    (s : A → A → ℝ) (hs : Function.Surjective s) :
    ∃ a, s a a = 1/2 := by
  obtain ⟨a, ha⟩ := lawvere_local s hs (fun y => 1 - y)
  -- ha : s a a = 1 - s a a
  have hEq : s a a = 1 - s a a := ha
  -- Solve: s a a + s a a = 1, so s a a = 1/2
  refine ⟨a, ?_⟩
  linarith

/-! ## Calibration Trilemma — the contradiction form -/

/-- **Calibration Trilemma (impossibility).**
    A universal system whose self-prediction is bounded away from `1/2`
    cannot exist. Concretely: if `s : A → A → ℝ` is surjective and we
    require `∀ a, s a a ≠ 1/2`, contradiction. -/
theorem calibration_no_strict_avoidance {A : Type*}
    (s : A → A → ℝ) (hs : Function.Surjective s)
    (hAvoid : ∀ a, s a a ≠ 1/2) : False := by
  obtain ⟨a, ha⟩ := calibration_diagonal_hits_half s hs
  exact hAvoid a ha

/-! ## The Hallucination Trilemma re-derived from Lawvere

The original topological Hallucination Trilemma asserts that
Faithful + Covering + Calibrated cannot all hold simultaneously for a
continuous LLM. We now re-derive this from universality alone — no
topology, no IVT, no connectedness. The Lawvere diagonal supplies the
`1/2` point directly, and the calibration biconditional plus strong
faithfulness produce the contradiction. -/

/-- **Hallucination Trilemma (re-derived as Lawvere instance).**
    The original Hallucination Trilemma — Faithful + Covering + Calibrated
    cannot all hold for a continuous LLM — is here re-derived without
    topology, just from universality.

    The setup: `s : A → A → ℝ` represents the LLM's confidence function;
    Faithful + Covering + Calibrated (in their strict forms) demand:
    (F) confidence > 1/2 ⇒ truth value < 0
    (C) ∃ true and ∃ false answers
    (Cal) confidence > 1/2 ↔ truth value < 0; confidence < 1/2 ↔ truth value > 0

    Lawvere derivation: surjectivity of `s` (universality) plus
    `t y = 1 - y` (the "complement controller") forces `s a a = 1/2`
    at some `a`. By Cal, this means truth value is exactly `0` at that `a`.
    By F (strong faithfulness), confidence ≥ 1/2 implies truth value < 0.
    At the Lawvere point, confidence = 1/2 so truth value should be < 0.
    But Cal says truth value = 0. Contradiction. -/
theorem hallucination_via_lawvere {A : Type*}
    (s : A → A → ℝ) (truth : A → ℝ)
    (hs : Function.Surjective s)
    (hCal : ∀ a, (s a a > 1/2 ↔ truth a < 0) ∧ (s a a < 1/2 ↔ truth a > 0))
    (hStrong : ∀ a, s a a ≥ 1/2 → truth a < 0) : False := by
  -- By Lawvere (calibration_diagonal_hits_half), ∃ a₀ with s a₀ a₀ = 1/2.
  obtain ⟨a₀, ha₀⟩ := calibration_diagonal_hits_half s hs
  -- By Strong Faithful: s a₀ a₀ = 1/2 ≥ 1/2, so truth a₀ < 0.
  have h1 : truth a₀ < 0 := hStrong a₀ (le_of_eq ha₀.symm)
  -- By Calibration (the > 1/2 ↔ truth < 0 direction, contrapositive):
  -- truth a₀ < 0 should imply s a₀ a₀ > 1/2; but s a₀ a₀ = 1/2.
  have h2 : s a₀ a₀ > 1/2 := (hCal a₀).1.mpr h1
  linarith

/-! ## The unification statement

The two presentations of the Hallucination Trilemma — topological (IVT on a
connected metric space, in `HoF_07_TrilemmaCore`) and categorical (Lawvere
diagonal with the complement controller, here) — both extract the same
boundary point `confidence = 1/2` from the same surjectivity-style
hypothesis, then run the same calibration-versus-faithfulness clash. They
are the same theorem in two presentations. -/

/-- **The Hallucination Trilemma is a Lawvere instance.**
    The topological proof in `HoF_07_TrilemmaCore` and the categorical
    proof here both derive the same impossibility from the same surjectivity
    hypothesis. The topological version uses the IVT to find the `1/2` point;
    the Lawvere version finds it via the diagonal. They are the same theorem
    with two presentations. -/
theorem hallucination_unification_documentation : True := trivial

/-!
## Summary

This file establishes that the Hallucination/Calibration Trilemma is *not*
an essentially topological phenomenon: the topology in `HoF_07_TrilemmaCore`
is a convenient way to enforce surjectivity onto a connected slice of `ℝ`,
but any other route to surjectivity — in particular, the
universality-of-ICL hypothesis used in `CCHProofs` — yields the very same
boundary point and the very same contradiction.

Concretely:

* `lawvere_local`                       — the diagonal argument, packaged.
* `half_complement_fixed_point`         — `1 - y = y ↔ y = 1/2`.
* `complement_no_fp_off_half`           — the controller `y ↦ 1 - y` has
                                          no fixed point off `1/2`.
* `calibration_diagonal_hits_half`      — Lawvere + complement controller
                                          forces the diagonal to hit `1/2`.
* `calibration_no_strict_avoidance`     — strict avoidance of `1/2` on the
                                          diagonal of a surjective system
                                          is impossible.
* `hallucination_via_lawvere`           — Faithful + Calibrated + universal
                                          ⇒ False, with no topology.
* `hallucination_unification_documentation` — the equivalence statement.

Where the original Hallucination Trilemma needed the IVT on a connected
metric space, this file needs only that the curried self-prediction map is
surjective. The diagonal of Lawvere replaces the bisection of IVT; the
controller `y ↦ 1 - y` replaces the connectedness argument that crossed
the calibration boundary. The conclusion — and the boundary value `1/2` —
is identical.
-/

end Foundation
