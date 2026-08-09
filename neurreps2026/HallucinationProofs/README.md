# Supplementary Material: Lean 4 Formalization

Machine-checked proofs for the submission *"Truth Has a Boundary. A
Machine-Verified Topological Law for Models That Separate Truth from
Falsehood"* (NeurReps 2026, Proceedings Track).

Every theorem and proposition stated in the paper is formalized here.
The project is self-contained mathematics. No datasets, models, or
experiments.

## Requirements

- [elan](https://github.com/leanprover/elan) (Lean toolchain manager)
- Lean `4.28.0` (pinned in `lean-toolchain`; elan installs it automatically)
- Mathlib `v4.28.0` (pinned in `lakefile.toml` / `lake-manifest.json`)

## Build and verify

```bash
lake build
```

Expected result: the build completes with **zero errors** and the
sources contain **no `sorry`**. Axiom audits (`#print axioms`) run in
`HoF_FinalVerification.lean`, `HoF_08_BorsukUlam.lean`, `HoF_11_MultiTurnProbabilistic.lean`,
`HoF_12_Approximate.lean`, `HoF_13_BoundaryCoupling.lean`, and
`HoF_14_QuantitativeGeometry.lean`; each headline theorem reduces to
exactly

```
[propext, Classical.choice, Quot.sound]
```

the three standard Lean kernel axioms.

## Paper-to-Lean map (Table 1 of the paper)

| Paper result | Lean identifier | File |
|---|---|---|
| Thm. Boundary existence | `model_truth_boundary_nonempty` | `HoF_03_BoundaryCrossing` |
| Thm. Boundary coupling (headline) | `boundary_coupling` | `HoF_13_BoundaryCoupling` |
| Cor. Inclusive guarantees impossible | `closed_guarantee_impossible`, `hallucination_trilemma` | `HoF_13`, `HoF_07` |
| Cor. Exclusive guarantees go silent | `open_guarantee_silent` | `HoF_13_BoundaryCoupling` |
| Thm. Boundary is closed | `model_truth_boundary_isClosed` | `HoF_03_BoundaryCrossing` |
| Thm. Every path crosses | `path_crosses_truth_boundary` | `HoF_03_BoundaryCrossing` |
| Thm. Linear probe hyperplane | `linear_probe_boundary_coset`, `linear_probe_boundary_dim` | `HoF_14_QuantitativeGeometry` |
| Thm. Corridor width | `confidence_gap_width` | `HoF_14_QuantitativeGeometry` |
| Thm. Ambiguity tube | `ambiguity_tube`, `truth_margin_tube` | `HoF_14_QuantitativeGeometry` |
| Thm. Approximate coupling | `two_slack_approx_coupling`, `exact_from_approx` | `HoF_12_Approximate` |
| Thm. Truth slack must be positive | `truth_slack_must_be_positive` | `HoF_12_Approximate` |
| Upper-band exclusion | `no_boundary_in_upper_band_two_slack` | `HoF_12_Approximate` |
| Thm. Odd fields vanish | `antipodal_odd_has_zero` | `HoF_08_BorsukUlam` |
| Thm. Approximately odd fields nearly vanish | `approx_odd_near_zero` | `HoF_08_BorsukUlam` |
| Thm. Sphere instantiation | `sphere_odd_has_zero` | `HoF_08_BorsukUlam` |
| Thm. Antipodal coupling | `antipodal_hallucination_trilemma` | `HoF_08_BorsukUlam` |
| Thm. Discrete impossibility | `boundary_question_impossible`, `faithful_iff_boundary_free` | `HoF_10_PureDiscrete` |
| Prop. Discrete sign change | `discrete_sign_change` | `HoF_09_Discrete` |
| Multi-turn | `multi_turn_history_dependent` | `HoF_11_MultiTurnProbabilistic` |
| Stochastic expected-value coupling | `stochastic_coupling_expected` | `HoF_11_MultiTurnProbabilistic` |
| Thm. Stochastic dichotomy | `stochastic_dichotomy` | `HoF_11_MultiTurnProbabilistic` |
| Two-slack separation (definition) | `TwoSlackSeparating`, `epsCalibrated_iff_twoSlack` | `HoF_12_Approximate` |
| Two-slack band bridge | `two_slack_band_bridge` | `HoF_12_Approximate` |
| Bundled master theorem | `hallucination_master_theorem` | `HoF_MasterTheorem` |

## Layout

Seventeen source files under `HallucinationProofs/`:

- `HoF_01`--`HoF_06`: vocabulary (spaces, truth-distance, the
  conditions `TrilemmaFaithful`, `TrilemmaCovering`,
  `StrictCalibrated`, and the band conditions `EpsCalibrated`,
  `EpsCovering`).
- `HoF_03_BoundaryCrossing`: boundary existence, closedness, path
  crossing (paper Sections 4 and 5).
- `HoF_07_TrilemmaCore`: the fixed-threshold trilemma.
- `HoF_08_BorsukUlam`: symmetry obstruction (Section 7).
- `HoF_09_Discrete`, `HoF_10_PureDiscrete`: discrete results (Section 8).
- `HoF_11_MultiTurnProbabilistic`: multi-turn and stochastic
  extensions (Section 9).
- `HoF_12_Approximate`: band separation and approximate coupling
  (Section 6).
- `HoF_13_BoundaryCoupling`: the convention-independent headline law
  and its corollary taxonomy (Section 4).
- `HoF_14_QuantitativeGeometry`: corridor width, ambiguity tube, and
  linear-probe hyperplane results (Sections 5 and 6).
- `HoF_Instantiation_PromptSpace`: Euclidean instantiation.
- `HoF_MasterTheorem`, `HoF_FinalVerification`: bundled statement and
  axiom audit.

Note on identifiers: some retain historical names using the words
"hallucination" and "calibrated" where the paper now says coupling
and separation. The formal statements are what they are, and the
paper claims nothing beyond them.

Note on imports: most files import only `Mathlib`; `HoF_10`, `HoF_11`,
`HoF_12`, and `HoF_13` additionally import earlier HoF modules, and
the verification files import the modules they check.

This artifact is anonymized for double-blind review.
