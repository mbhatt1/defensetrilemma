# Foundation — Structural Impossibility Theorems for AI Safety

A unified family of foundational impossibility results, each an instance of
**Lawvere's diagonal** applied with a different parameter. Together they form
the structural ceiling that bounds what is jointly achievable for any
sufficiently expressive AI system.

This is the Gödel/Turing/Cook-Levin–level foundation: not one impossibility,
but a coordinated family, each load-bearing for a different axis of safety
desiderata.

## Quick start

```bash
# Requires Lean 4.28.0 + Mathlib v4.28.0 (via elan/lake)
lake build
```

## The ten foundational results

| File | Result | Says |
|------|--------|------|
| `F_01_LawvereCore` | Lawvere's diagonal | Master fixed-point engine |
| `F_02_RiceTheorem` | Rice's theorem | No nontrivial property of universal systems is decidable |
| `F_03_VerificationLimit` | Verification limit | Bounded verifiers cannot decide universal systems |
| `F_04_CalibrationUnified` | Calibration Trilemma (unified) | Hallucination Trilemma as Lawvere instance |
| `F_05_DeceptionTheorem` | Deception | Universal + control implies divergent self-prediction |
| `F_06_OversightHierarchy` | Oversight hierarchy | Each level inherits the trilemma |
| `F_07_CompositionFailure` | Composition theorem | Combining corner-systems fails to preserve corners |
| `F_08_SpecificationBound` | Specification bound | Finite specs cover measure-zero of behavior space |
| `F_09_QuantitativeDegradation` | Quantitative ε-trilemma | Achievable region as inequality, not just corner |
| `F_10_MasterFoundation` | Unifying meta-theorem | Every impossibility above is a Lawvere instance |

## What this is

A claim that AI safety has a **single underlying mathematical engine** —
Lawvere's diagonal — that produces, with different parameter choices, every
specific impossibility we currently recognize. The engine is universal in
the sense that any property phrased as a "no-fixed-point endomap" yields its
own impossibility corner.

## What this isn't

A claim that this list is exhaustive. Other axes (computational complexity
classes, measure-theoretic specification limits, quantum-mechanical bounds)
may add further structural constraints not subsumed by Lawvere. The current
list is the result of mapping known AI-safety obstructions to their nearest
Lawvere instance; new safety properties may require new structural arguments.

## Verification

- **Lean 4.28.0** + **Mathlib v4.28.0**
- Each file imports only `Mathlib`; the entry-point imports them all.
- All headline theorems should reduce to `[propext, Classical.choice, Quot.sound]`
  or fewer.
