import Mathlib
import HallucinationProofs.HoF_12_Approximate

/-!
# Hallucination Trilemma — Part 13: Boundary Coupling

The convention-independent headline theorem. If a continuous model on a
connected space covers both truth signs and its confidence separates
true answers from false ones at threshold `c`, then some query is
forced to sit exactly on the truth boundary with confidence exactly
`c`. No faithfulness hypothesis appears, so the statement does not
depend on whether a guarantee includes or excludes its threshold.

The corollary taxonomy then reads off consequences per policy.

1. `boundary_coupling` — the headline. `∃ q₀, conf(q₀) = c ∧ δ(q₀) = 0`.
2. `closed_guarantee_impossible` — a threshold-inclusive guarantee
   (`conf ≥ c → δ < 0`) is contradictory (the trilemma).
3. `open_guarantee_silent` — a threshold-exclusive guarantee
   (`conf > c → δ < 0`) is not contradicted, but its antecedent fails
   at the forced point. The guarantee is silent exactly there.
4. `slack_must_be_positive` — any model satisfying band separation,
   band coverage, and a threshold-inclusive guarantee must carry
   strictly positive slack `ε`. Zero slack is infeasible.

Separation here is the one-way pair at zero slack,
`EpsCalibrated M δ c 0`, namely `δ < 0 → conf > c` and
`δ > 0 → conf < c`. The strict biconditional (`StrictCalibrated`)
implies it at `c = 1/2` (`strictCalibrated_to_epsCalibrated_zero_half`).

All proofs are sorry-free.
-/

open Set

noncomputable section

namespace HoF

/-! ## 1. The headline: boundary coupling -/

/--
**Boundary Coupling.**

Connected space, continuous confidence, two-sided coverage, and
one-way truth separation at threshold `c`. Then some query carries
confidence exactly `c` and truth-distance exactly `0`.

No faithfulness hypothesis. The theorem is independent of any
threshold convention in a guarantee.
-/
theorem boundary_coupling
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c : ℝ)
    (hconf : Continuous (fun q => (M q).2))
    (hcov : EpsCovering M δ 0)
    (hcal : EpsCalibrated M δ c 0) :
    ∃ q₀, (M q₀).2 = c ∧ δ (q₀, (M q₀).1) = 0 := by
  obtain ⟨⟨qt, ht⟩, ⟨qf, hf⟩⟩ := hcov
  -- Separation converts coverage witnesses into confidence witnesses.
  have hct : (M qt).2 > c + 0 := hcal.1 qt ht
  have hcf : (M qf).2 < c - 0 := hcal.2 qf hf
  have hct' : (M qt).2 > c := by linarith
  have hcf' : (M qf).2 < c := by linarith
  -- IVT on the confidence field.
  obtain ⟨q₀, _, hq₀⟩ :=
    isPreconnected_univ.intermediate_value₂
      (mem_univ qf) (mem_univ qt)
      hconf.continuousOn continuous_const.continuousOn
      (le_of_lt hcf') (le_of_lt hct')
  refine ⟨q₀, hq₀, ?_⟩
  -- At conf = c, separation excludes both signs of the truth field.
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hδ : δ (q₀, (M q₀).1) < -0 := by simpa using hlt
    have := hcal.1 q₀ hδ
    linarith
  · have := hcal.2 q₀ hgt
    linarith

/-! ## 2. Corollary taxonomy -/

/--
**Closed-threshold guarantee is impossible.**

Add a guarantee that covers its own threshold, `conf ≥ c → δ < 0`.
The coupled point has `conf = c`, so the guarantee applies there and
demands `δ < 0`, contradicting `δ = 0`. This is the trilemma.
-/
theorem closed_guarantee_impossible
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c : ℝ)
    (hconf : Continuous (fun q => (M q).2))
    (hcov : EpsCovering M δ 0)
    (hcal : EpsCalibrated M δ c 0)
    (hfaith : ∀ q, (M q).2 ≥ c → δ (q, (M q).1) < 0) :
    False := by
  obtain ⟨q₀, hc, hd⟩ := boundary_coupling M δ c hconf hcov hcal
  have := hfaith q₀ (ge_of_eq hc)
  linarith

/--
**Open-threshold guarantee is silent at the forced point.**

A guarantee that excludes its threshold, `conf > c → δ < 0`, is not
contradicted. Instead its antecedent fails at the coupled point. The
model owns a query about which the guarantee says nothing, and that
query sits exactly on the truth boundary.
-/
theorem open_guarantee_silent
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c : ℝ)
    (hconf : Continuous (fun q => (M q).2))
    (hcov : EpsCovering M δ 0)
    (hcal : EpsCalibrated M δ c 0) :
    ∃ q₀, (M q₀).2 = c ∧ δ (q₀, (M q₀).1) = 0 ∧ ¬ ((M q₀).2 > c) := by
  obtain ⟨q₀, hc, hd⟩ := boundary_coupling M δ c hconf hcov hcal
  exact ⟨q₀, hc, hd, by simp [hc]⟩

/--
**Slack must be positive.**

Suppose a model satisfies band coverage, band separation at slack
`ε ≥ 0`, and a threshold-inclusive guarantee. Then `ε > 0`. The
infimum of feasible slack values is therefore bounded away from the
idealized endpoint `ε = 0`, which is infeasible.
-/
theorem slack_must_be_positive
    {Q A : Type*} [TopologicalSpace Q] [ConnectedSpace Q] [TopologicalSpace A]
    (M : Q → A × ℝ) (δ : Q × A → ℝ) (c ε : ℝ) (hε : 0 ≤ ε)
    (hconf : Continuous (fun q => (M q).2))
    (hcov : EpsCovering M δ ε)
    (hcal : EpsCalibrated M δ c ε)
    (hfaith : ∀ q, (M q).2 ≥ c → δ (q, (M q).1) < 0) :
    0 < ε := by
  rcases hε.lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    exact exact_from_approx M δ c hconf hcov hcal hfaith

/-! ## 3. Axiom audit -/

#print axioms boundary_coupling
#print axioms closed_guarantee_impossible
#print axioms open_guarantee_silent
#print axioms slack_must_be_positive

end HoF

end
