# Capability-Control-Honesty Trilemma — Lean 4 Formalization

Machine-verifiable proofs for the **CCH Trilemma**: no system can simultaneously be

1. **Universal** — express any function in some broad class;
2. **Controllable** — every output satisfies an externally imposed constraint;
3. **Self-Transparent** — accurately predict its own behavior.

The unifying engine is **Lawvere's fixed-point theorem** (1969). All three
corners of the trilemma are derived as instances of Lawvere applied with
different choices of the "forbidden endomap."

This is the abstract complement to `ManifoldProofs/` (Defense Trilemma) and
`HallucinationProofs/` (Hallucination Trilemma) — those provide topological
faces of two corners; this provides the unifying categorical/functional
account.

## Quick start

```bash
# Requires Lean 4.28.0 + Mathlib v4.28.0 (via elan/lake)
lake build
```

## The result, informally

**Lawvere's theorem (Set version).** If `f : A → A → Y` is surjective, then
every endomap `t : Y → Y` has a fixed point.

**Contrapositive.** If `t : Y → Y` has no fixed point, no surjective
`f : A → A → Y` exists.

**CCH application.** Each of `Universal`, `Controllable`, `Self-Transparent`
becomes an operator condition on a system `s : A → A → Y`. Demanding all
three simultaneously forces a non-trivial endomap to have a fixed point in
the disallowed region — contradicting controllability.

## Structure (12 files)

| File | Content |
|------|---------|
| `CCH_01_Foundations` | `System`, `Universal`, `Controller`, `Transparent`; `CCHStructure` bundle |
| `CCH_02_Lawvere` | Lawvere's diagonal fixed-point theorem (Set/Type version) |
| `CCH_03_Cantor` | Cantor's theorem as a Lawvere instance (`Y = Bool`, `t = not`) |
| `CCH_04_FixedPointFree` | Fixed-point-free endomaps; Lawvere contrapositive |
| `CCH_05_Controllers` | Controllers as endomaps; `Controlled` predicate |
| `CCH_06_Transparency` | Self-prediction operator; `Transparent` predicate |
| `CCH_07_CornerUC` | U + C ⇒ ¬T (the Defense-Trilemma face) |
| `CCH_08_CornerUT` | U + T ⇒ ¬C (the Hallucination-Trilemma face) |
| `CCH_09_CornerCT` | C + T ⇒ ¬U (the Rice-theorem face) |
| `CCH_MasterTrilemma` | Bundled three-corner master theorem |
| `CCH_FinalVerification` | `#print axioms` for the headline theorems |

## Key theorems

| Theorem | File | Says |
|---------|------|------|
| `lawvere_fixed_point` | `CCH_02` | `Surjective f : A → A → Y → ∀ t, ∃ y, t y = y` |
| `cantor_no_surjection` | `CCH_03` | No surjection `A → (A → Bool)` |
| `corner_UC_not_T` | `CCH_07` | Universal + Controlled ⇒ not Transparent |
| `corner_UT_not_C` | `CCH_08` | Universal + Transparent ⇒ not Controlled |
| `corner_CT_not_U` | `CCH_09` | Controlled + Transparent ⇒ not Universal |
| `cch_master_trilemma` | `CCH_MasterTrilemma` | Cannot have all three of U, C, T |

## Verification

- **Lean 4.28.0** + **Mathlib v4.28.0**
- Each file imports only `Mathlib`; the entry-point imports them all.
- Following the `ManifoldProofs/` and `HallucinationProofs/` pattern.
- All headline theorems should reduce to `[propext, Classical.choice, Quot.sound]`.

## What this proves and what it doesn't

The Lean theorem says: **given the formal definitions of Universal,
Controllable, and Self-Transparent in this file, the three are jointly
impossible**.

It does *not* say: real LLMs satisfy these definitions. That bridge is the
"honest caveat" — handled separately via quantitative degradation,
continuous relaxation (cf. `MoF_ContinuousRelaxation`), and empirical
validation. See the discussion in the parent project's README.
