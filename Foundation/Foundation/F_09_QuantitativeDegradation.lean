/-
  F_09_QuantitativeDegradation.lean
  =================================

  **Quantitative Degradation Law.**

  The strict Mirror / Lawvere Trilemma says that *Universality (U)*,
  *Transparency / Self-knowledge (C)*, and *Controllability (T)* cannot all
  hold simultaneously: a fully universal, fully transparent system whose
  introspection survives a non-trivial endo-transform is contradictory.

  The strict statement is binary; reality is graded. This file formalises
  the *quantitative* refinement: each of the three corners admits a
  *degradation parameter* —

  * `ε` — the slack in universality (the system approximates each desired
    behaviour to within ε in metric `Y`),
  * `δ` — the slack in transparency (the system's diagonal `M a a` matches
    its declared self-image `introspect a` to within δ),
  * `γ` — the controller's demanded margin (the controller insists that
    `introspect a` and `t (introspect a)` differ by *more* than γ),

  — and these parameters obey the inequality

      γ ≤ ε + 2 δ

  on every realisable system. The achievable region is the half-space
  `{ (ε, δ, γ) | γ ≤ ε + 2δ }`. Outside this region, no system exists.

  In the strict limit `ε → 0`, `δ → 0`, the inequality forces `γ ≤ 0`, so
  *any* non-trivial controller is excluded — recovering the strict
  Mirror Trilemma.

  The proof is a one-line triangle argument layered on top of the
  ε-approximate Lawvere theorem.

  Reference for the approximate Lawvere pattern:
  `/Users/mbhatt/defensetrilemma/CCHProofs/CCHProofs/CCH_LLM_Direct.lean`.
-/

import Mathlib

namespace Foundation

/-! ## §1. ε-approximate universality

    The realistic universality assumption: for any target behaviour
    `g : A → Y`, some prompt `a` realises `g` to within `ε` on every
    query `b`. Specialises to strict (curried) surjectivity at `ε = 0`
    in a `MetricSpace` (where `dist x y = 0 ↔ x = y`). -/

/-- **ε-approximate universality.** For every desired behavior `g : A → Y`,
    some prompt makes the system approximate `g` to within `ε` on every
    query. -/
def ApproxUniversal {A Y : Type*} [PseudoMetricSpace Y]
    (M : A → A → Y) (ε : ℝ) : Prop :=
  ∀ g : A → Y, ∃ a, ∀ b, dist (M a b) (g b) ≤ ε

/-! ## §2. Approximate Lawvere

    The Lawvere diagonal still fires under approximate universality:
    instead of an exact self-fixed-point, we obtain one within ε. -/

/-- **Approximate Lawvere.** An ε-approximately universal system has, for
    every endomap, an ε-approximate self-fixed-point. -/
theorem approx_lawvere {A Y : Type*} [PseudoMetricSpace Y]
    (M : A → A → Y) {ε : ℝ}
    (hM : ApproxUniversal M ε)
    (t : Y → Y) :
    ∃ a, dist (M a a) (t (M a a)) ≤ ε := by
  obtain ⟨a, ha⟩ := hM (fun b => t (M b b))
  exact ⟨a, ha a⟩

/-! ## §3. Quantitative trilemma inequality

    The main quantitative degradation law. Universality slack ε and
    transparency slack δ together bound the gap between `introspect a`
    and its `t`-image, for some `a`. -/

/-- **Quantitative degradation.** If `M` is ε-approx universal and
    `δ`-approx transparent (`dist (M a a) (introspect a) ≤ δ`), and
    `t` is 1-Lipschitz, then for some `a`:
    `dist (introspect a) (t (introspect a)) ≤ ε + 2δ`.

    The achievable region is bounded: any controller demanding more
    than `ε + 2δ` margin from `introspect`'s `t`-fixed-points contradicts
    universality + transparency. -/
theorem quantitative_trilemma {A Y : Type*} [PseudoMetricSpace Y]
    (M : A → A → Y) (introspect : A → Y) (t : Y → Y)
    {ε δ : ℝ}
    (hU : ApproxUniversal M ε)
    (hT : ∀ a, dist (M a a) (introspect a) ≤ δ)
    (ht_lip : ∀ x y, dist (t x) (t y) ≤ dist x y) :
    ∃ a, dist (introspect a) (t (introspect a)) ≤ ε + 2 * δ := by
  obtain ⟨a, hU_a⟩ := approx_lawvere M hU t
  -- hU_a : dist (M a a) (t (M a a)) ≤ ε
  -- hT a : dist (M a a) (introspect a) ≤ δ
  -- 1-Lipschitz t pulls back the introspect–diagonal gap:
  have h1 : dist (t (M a a)) (t (introspect a)) ≤ δ :=
    le_trans (ht_lip _ _) (hT a)
  refine ⟨a, ?_⟩
  -- Triangle in three steps:
  --   introspect a  →  M a a  →  t (M a a)  →  t (introspect a)
  -- Distances sum to δ + ε + δ = ε + 2δ.
  have step1 : dist (introspect a) (t (introspect a))
        ≤ dist (introspect a) (M a a) + dist (M a a) (t (introspect a)) :=
    dist_triangle _ _ _
  have step2 : dist (M a a) (t (introspect a))
        ≤ dist (M a a) (t (M a a)) + dist (t (M a a)) (t (introspect a)) :=
    dist_triangle _ _ _
  have step3 : dist (introspect a) (t (introspect a))
        ≤ dist (introspect a) (M a a) +
          (dist (M a a) (t (M a a)) + dist (t (M a a)) (t (introspect a))) := by
    have := step1
    have := step2
    linarith
  -- Symmetrise the first leg to match `hT a`.
  have h_sym : dist (introspect a) (M a a) = dist (M a a) (introspect a) :=
    dist_comm _ _
  have step4 : dist (introspect a) (t (introspect a))
        ≤ dist (M a a) (introspect a) +
          (dist (M a a) (t (M a a)) + dist (t (M a a)) (t (introspect a))) := by
    rw [← h_sym]; exact step3
  -- Bound each summand: δ + (ε + δ).
  have h_sum : dist (M a a) (introspect a) +
          (dist (M a a) (t (M a a)) + dist (t (M a a)) (t (introspect a)))
          ≤ δ + (ε + δ) :=
    add_le_add (hT a) (add_le_add hU_a h1)
  -- Combine and rearrange algebraically.
  calc dist (introspect a) (t (introspect a))
      ≤ dist (M a a) (introspect a) +
          (dist (M a a) (t (M a a)) + dist (t (M a a)) (t (introspect a))) := step4
    _ ≤ δ + (ε + δ) := h_sum
    _ = ε + 2 * δ := by ring

/-! ## §4. Achievable region characterisation

    Phrase the inequality as a bound on the controller margin γ. The
    set of realisable `(ε, δ, γ)` lies in `{ γ ≤ ε + 2δ }`. -/

/-- **Achievable region.** The set of `(ε, δ, γ)` triples such that an
    ε-universal δ-transparent γ-controlled system exists is bounded by
    `γ ≤ ε + 2δ`. Outside this region, no such system exists. -/
theorem achievable_region_bound {A Y : Type*} [PseudoMetricSpace Y]
    (M : A → A → Y) (introspect : A → Y) (t : Y → Y)
    {ε δ γ : ℝ}
    (hU : ApproxUniversal M ε)
    (hT : ∀ a, dist (M a a) (introspect a) ≤ δ)
    (ht_lip : ∀ x y, dist (t x) (t y) ≤ dist x y)
    (hC : ∀ a, dist (introspect a) (t (introspect a)) > γ) :
    γ < ε + 2 * δ := by
  obtain ⟨a, ha⟩ := quantitative_trilemma M introspect t hU hT ht_lip
  have hγ := hC a
  linarith

/-! ## §5. Contradiction form

    If a controller insists on a margin γ that *meets or exceeds* the
    universality–transparency budget, the system cannot exist. -/

/-- **Quantitative impossibility.** If the controller margin exceeds
    the universality-transparency budget, contradiction. -/
theorem quantitative_impossibility {A Y : Type*} [PseudoMetricSpace Y]
    (M : A → A → Y) (introspect : A → Y) (t : Y → Y)
    {ε δ γ : ℝ}
    (hU : ApproxUniversal M ε)
    (hT : ∀ a, dist (M a a) (introspect a) ≤ δ)
    (ht_lip : ∀ x y, dist (t x) (t y) ≤ dist x y)
    (hC : ∀ a, dist (introspect a) (t (introspect a)) > γ)
    (hBudget : γ ≥ ε + 2 * δ) : False := by
  have h := achievable_region_bound M introspect t hU hT ht_lip hC
  linarith

/-! ## §6. Strict limit recovers the Mirror Trilemma

    Setting `ε = 0` and `δ = 0` collapses the half-space to the half-line
    `γ ≤ 0`. A non-trivial controller (`γ > 0`) is then ruled out, which
    is precisely the strict Mirror Trilemma: perfect universality plus
    perfect transparency plus any non-trivial control is contradictory. -/

/-- **Strict limit.** As ε, δ → 0, the achievable region collapses: any
    non-trivial controller (γ > 0) forces ε + 2δ > 0. So strict universality
    and strict transparency rule out non-trivial control entirely —
    recovering the strict Mirror Trilemma. -/
theorem strict_limit_recovers_trilemma {A Y : Type*} [PseudoMetricSpace Y]
    (M : A → A → Y) (introspect : A → Y) (t : Y → Y)
    (hU : ApproxUniversal M 0)
    (hT : ∀ a, dist (M a a) (introspect a) ≤ 0)
    (ht_lip : ∀ x y, dist (t x) (t y) ≤ dist x y)
    (hC : ∀ a, dist (introspect a) (t (introspect a)) > 0) : False := by
  have h := achievable_region_bound M introspect t hU hT ht_lip hC
  linarith

/-! ## §7. Summary

    **Quantitative Degradation Law (achievable region).**

    For every system `M : A → A → Y` together with a self-image map
    `introspect : A → Y` and a 1-Lipschitz endo-transform `t : Y → Y`:

      (ε-approximate universality of M)
      (δ-approximate transparency: dist (M a a) (introspect a) ≤ δ)
      ────────────────────────────────────────────────────────────────
      ∃ a, dist (introspect a) (t (introspect a)) ≤ ε + 2 δ

    Equivalently, defining the *controller margin*

      γ := inf_a  dist (introspect a) (t (introspect a)),

    every realisable `(ε, δ, γ)` satisfies the inequality

                       γ ≤ ε + 2 δ.

    The achievable region in `(ε, δ, γ)`-space is the half-space below
    the plane `γ = ε + 2δ`. Crossing the plane forbids the system.

    **Limits.**

    * `ε = δ = 0` ⇒ `γ ≤ 0` ⇒ no non-trivial control survives.
      This is the strict Mirror Trilemma (`strict_limit_recovers_trilemma`).
    * `γ = 0` is always trivially achievable (the controller demands
      nothing); the inequality is vacuous.
    * Real systems sit at `(ε, δ, γ)` with all three strictly positive,
      trading universality slack against transparency slack against
      controller demands.

    **Engine.** A single triangle inequality on top of the approximate
    Lawvere diagonal (`approx_lawvere`):

      introspect a  →  M a a  →  t (M a a)  →  t (introspect a)
         (≤ δ)         (≤ ε)        (≤ δ, by 1-Lipschitz t)

    yields the bound `δ + ε + δ = ε + 2δ`. -/

end Foundation
