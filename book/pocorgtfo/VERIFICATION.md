# Verification log — AI ‖ PoC ‖ GTFO, Issue 0x01

This records an actual `lake build` + axiom audit of the companion Lean corpus,
run on this machine for this printing. It substantiates the book's central claim:
the proofs are machine-checked, sorry-free, and the axiom profile is exactly as
stated.

## Build result

Toolchain: `leanprover/lean4:v4.28.0` (via elan), Mathlib vendored and cached.

| Package | `lake build` exit |
|---------|-------------------|
| `proofs/Foundation` | 0 |
| `proofs/CCHProofs` | 0 |
| `proofs/HallucinationProofs` | 0 |
| `ManifoldProofs` | 0 |
| **Overall** | **0** |

- Zero `error:` lines across all four builds.
- Authored sources are `sorry`-free (the only `sorry` tokens in the tree are inside
  the vendored Mathlib tactic docs, not in authored proofs).
- The geometry package alone completed 8072 build jobs.

## Axiom audit (from each package's `*_FinalVerification` file)

**Axiom-free — the combinatorial core (depends on *no* axioms):**
- `Foundation.no_reflective_verdict`
- `Foundation.trilemmata_unified` (the three trilemmata as one proof term)
- `Foundation.coupling_trilemma_godel`
- `Foundation.hallucination_trilemma_godel`, `Foundation.hallucination_liar_query`,
  `Foundation.tarski_liar`
- `Foundation.defense_trilemma_godel`, `Foundation.defense_liar_query`,
  `Foundation.reflective_verdict_impossible`
- `Foundation.jspace_readout_impossible`, `Foundation.jspace_coupled_activation`
- `Foundation.master_foundation_theorem`, `Foundation.unification_statement`
- `CCH.cch_master_trilemma`, `CCH.cch_corner_UC/UT/CT`, `CCH.cch_at_most_two`

**Classically clean — the analytic results (depend on exactly
`propext, Classical.choice, Quot.sound`):**
- `HoF.boundary_coupling`
- `HoF.hallucination_trilemma`, `HoF.hallucination_trilemma_strict`,
  `HoF.hallucination_trilemma_three_clause`
- `HoF.antipodal_hallucination_trilemma`
- `HoF.two_slack_approx_coupling`
- `HoF.stochastic_dichotomy`, `HoF.stochastic_coupling_expected`
- `Foundation.hallucination_via_lawvere`, `Foundation.defense_trilemma_lawvere`
- `MoF.defense_incompleteness`, `MoF.defense_cost_exponential`,
  `MoF.hit_probability_tends_to_one`

This is exactly the two-tier creed the book preaches: the diagonal engine is
unconditional, and the analysis rests only on the three standard kernel axioms
that all of Mathlib uses.

## Reproduce
```sh
export PATH="$HOME/.elan/bin:$PATH"
for p in proofs/Foundation proofs/CCHProofs proofs/HallucinationProofs ManifoldProofs; do
  ( cd "$p" && lake build )
done
```
The `*_FinalVerification.lean` files end with `#print axioms` on the headline
theorems, so the audit above prints during the build.
