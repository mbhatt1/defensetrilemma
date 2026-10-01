# Truth Has a Boundary — TMLR revision plan and evidence record

Source manuscript: `defensetrilemma/papers/truth-boundary/neurreps2026/neurreps_truth_boundary.tex` at commit `dfb3705`.
Rewritten manuscript: `main.tex` / `main.pdf` in this folder.

## RESEARCH_PACKET

- **question:** If a truth readout and a confidence signal are continuous fields on a connected representation space, what must hold of them jointly?
- **primary_archetype:** C. Theory. The empirical part only measures the premises.
- **candidate_contribution:**
  - the boundary coupling theorem and its guarantee taxonomy;
  - the relaxations, all mechanized in Lean 4;
  - a premise-level measurement in 5 small LMs.
- **evidence_available:**
  - Lean project: 18 files, Lean/Mathlib v4.28.0, no sorry/admit/axiom/native_decide;
  - experiment scripts plus results JSON/npz for 5 models (cities, plus sp_en);
  - bootstrap, nulls, oddness, MLP probes, a layer sweep (Phi), an adversarial run.
- **evidence_missing:**
  - a build log showing the `#print axioms` output;
  - nulls matched to the endogenous experiment;
  - nulls and bootstrap for sp_en;
  - multi-seed training;
  - pinned package versions, hardware and runtime;
  - a Lean definition of the exclusive guarantee, or a consistency witness (now given as a paper proof).
- **closest_prior_work:**
  - Defense Trilemma (same continuity technique, safety wrappers);
  - Kalai & Vempala 2024; Xu et al. 2024; Karbasi et al. 2025;
  - Marks & Tegmark 2024; Bürger et al. 2024;
  - Farquhar et al. 2023; Levinstein & Herrmann.
- **known_negative_results:**
  - confidence at the crossing is bimodal: only 5–21% of paths have c in [0.4, 0.6];
  - the endogenous coupling fails in Pythia, GPT-2 and Phi;
  - the adversarial run violates the guarantee premise, so it cannot test Thm 7;
  - the oddness defect is large (p90 0.41–0.91);
  - "different seed" was inert (lbfgs).
- **likely_reviewer_objections:**
  - the theorem is a direct IVT corollary;
  - the premises are unrealistic (exact separation, connectedness);
  - the experiments don't test the theorem;
  - novelty relative to the Defense Trilemma;
  - n = 5 models.

## CONTRIBUTION_CONTRACT

- **C1.** Under (T), (C), (Cov₀) and (Sep₀,₀), ∃x₀ with c(x₀)=τ ∧ δ_F(x₀)=0. An inclusive guarantee is inconsistent with these; an exclusive guarantee is consistent but silent at x₀.
  - *Falsifiable by:* a counterexample to the Lean statement.
- **C2.** The relaxations (slack, Lipschitz tube, hyperplane geometry, symmetry, discrete) are mechanized; Table 1 marks paper-only parts.
  - *Falsifiable by:* the Lean build failing, or a statement mismatch.
- **C3.** In 5 models on cities, the median crossing gap between independently trained readouts orders inversely with probe accuracy (0.313 → 0.050). With the model's own p(true), small gaps appear only where endpoint separation holds on ≥93% of paths (both Qwens).
  - *Falsifiable by:* a reseed or retrain that breaks the ordering, or a separated model with a null-level gap.

**NOT_CLAIMING:**
- error rates;
- that deployed models are continuous, or that their reachable sets are connected;
- that probes track semantic truth;
- that the experiments test the theorem;
- any scale or causal effect;
- coupling in all five models;
- a slack floor from the adversarial run;
- use of Borsuk–Ulam;
- "first" priority.

## TECHNICAL_DELTA

Prior inevitability results bound hallucination *rates* statistically or computationally. The Defense Trilemma applies IVT on a connected prompt space to safety wrappers. We apply IVT to the *confidence* field under pointwise separation, which locates a query where the threshold and the truth boundary coincide. We then derive the guarantee taxonomy, the priced relaxations, and premise measurements in LMs.

## CLAIM–EVIDENCE GRAPH (central claims)

| ID | Claim | Centrality | Evidence | Conditions | Threat | Status |
|---|---|---|---|---|---|---|
| T1 | Boundary coupling | central | `boundary_coupling` (HoF_13:52) | (T), continuous conf, EpsCovering 0, EpsCalibrated c 0 | trivial-IVT objection | VERIFIED (source read; not compiled here) |
| T2 | Inclusive guarantee inconsistent | central | `closed_guarantee_impossible` (HoF_13:90) | as T1 plus hfaith | — | VERIFIED |
| T3 | Exclusive guarantee silent at x₀ | central | `open_guarantee_silent` (HoF_13:110) | as T1 | — | VERIFIED |
| T4 | Exclusive guarantee consistent | central | Example 1 (paper proof) | — | not mechanized | VERIFIED (paper), PARTIAL (mechanization) |
| T5 | ε > 0 forced | supporting | `truth_slack_must_be_positive` (HoF_12:290) | inclusive guarantee, εcovering, two-slack separation | over-reading as a "floor" | VERIFIED; prose now scoped |
| T6 | Corridor/tube | supporting | HoF_14:43/62/81 | Lipschitz, pseudometric | — | VERIFIED |
| T7 | Hyperplane | supporting | HoF_14:108/122; nonemptiness on paper | finite-dim, f ≠ 0 | nonemptiness unmechanized | VERIFIED / PARTIAL |
| T8 | Nonlinear first order | supporting | HoF_15:80/135/163 | HasFDerivAt, L ≠ 0 | — | VERIFIED |
| T9 | Symmetry results | supporting | HoF_08:88/204/264/163 | free involution; odd | oddness empirically weak | VERIFIED (math) |
| T10 | Discrete | supporting | HoF_10:120/196; HoF_09:271 | none | — | VERIFIED |
| T11 | Multi-turn | peripheral | HoF_11:61 | ½ biconditional only | earlier prose said "verbatim" | VERIFIED as scoped |
| T12 | Expected-field coupling | peripheral | HoF_11:105 | fields assumed | no measure link | VERIFIED as scoped |
| T13 | Dichotomy | supporting | HoF_11:177 | integrable d, mean 0 | instantiation not formal | VERIFIED |
| T14 | Three-axiom kernel | supporting | `#print axioms` commands exist | — | no build log | UNSUPPORTED, so marked [EVIDENCE NEEDED] |
| E1 | Gap orders inversely with probe accuracy | central | results.json `median_alpha_gap`, `probe_test_acc` | 5 models, 1 seed, cities | n = 5; single seed | VERIFIED (as rank order) |
| E2 | Trained gap below nulls | central | results_endogenous.json `nulls` | 20 seeds each | GPT-2/Phi inside the random range | VERIFIED (as scoped) |
| E3 | Endogenous coupling only in the Qwens | central | results_endogenous.json | final block, template | no matched nulls | PARTIAL, so marked [EVIDENCE NEEDED] |
| E4 | MLP replication | supporting | results_nonlinear.json, results_bootstrap.json mlp | — | — | VERIFIED |
| E5 | sp_en replication | supporting | results_gaps.json sp_en | layers fixed | no nulls, few paths | PARTIAL, so marked [EVIDENCE NEEDED] |
| E6 | Confidence at crossing ≈ 0.5 (old claim) | — | results_crossing_conf.json | — | bimodal | CONTRADICTED as stated; replaced with the bimodality report |
| E7 | Adversarial slack floor (old claim) | — | results_adversarial.json | 60 Adam steps, guarantee violated | premises fail | CONTRADICTED as a test; demoted to an appendix "exploratory" note |
| E8 | "Coupling observed in five models" (old abstract) | — | Table 3 | — | fails in 3 of 5 endogenous | CONTRADICTED; removed |

## What changed from the NeurReps version (substantive)

1. The abstract and introduction now state all four premises; "impossible" is always conditioned on them.
2. The "machine-check every statement" and "prose claims nothing beyond the formal statements" claims are replaced by Table 1, which carries a mechanized/paper status column.
3. The exclusive-guarantee consistency is now proved (Example 1, paper).
4. Multi-turn and stochastic claims are scoped to what Lean proves.
5. "Borsuk–Ulam" is clarified: only IVT is used.
6. The LayerNorm/sphere framing is labelled interpretation.
7. The experiments are reframed as premise measurement. The positional gap is the primary statistic, and the bimodality of confidence at the crossing is disclosed.
8. The layer-selection rule is disclosed (3 candidates), and the inert "different seed" claim is removed.
9. GPT-2's endogenous result is described accurately rather than as "at null"; the null mismatch is disclosed.
10. The sp_en "at null" claim is removed (no nulls were computed).
11. The adversarial run is demoted to an appendix and described accurately: 60 steps, guarantee violated, not a test.
12. The oddness p90 is reported, and the symmetry results are not claimed to apply empirically.
13. Citations:
    - the Kalai & Vempala description is corrected;
    - Cai et al. is moved from supporting (T) to evidence against it;
    - the negation-oddness motivation is re-sourced to Bürger et al.;
    - probe critiques are added (Farquhar 2023, Levinstein & Herrmann);
    - the Defense Trilemma is cited in the third person;
    - the "first machine-verified" claim is dropped;
    - the unused `ji2023survey` is left uncited (harmless with natbib).
14. Figures are regenerated with paper model names, a shared [0, 1] confidence axis, and the threshold label in data coordinates; the schematic caption says it is illustrative.
15. TMLR format: anonymous, Broader Impact Statement, no page limit (13 pp including appendices).

## Open items before submission (rendered in red in the PDF while `\showneededtrue`)

1. Attach the Lean build log with the `#print axioms` output for every Table 1 theorem. This needs a machine with Lean v4.28.0 and Mathlib.
2. Nulls on the endogenous final-block representation and paths.
3. Nulls plus bootstrap for sp_en.
4. Hardware, package versions, runtime, and a requirements file.
5. Verify the metadata of the 8 new BibTeX entries in `refs.bib` against the publisher pages. They were found via search snippets only.
6. Recommended, not required: multi-seed retraining of the probe and head (≥5 seeds) to show that the ordering in Table 2 is not a single-fit artifact.
