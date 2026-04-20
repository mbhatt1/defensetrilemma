# Paper Artifact Manifest

Complete inventory of every file produced by the five agents working
on the Defense Trilemma paper revision, cross-referenced to Hoque's
nine review issues. Paths are absolute; `<repo>` is
`/Users/mbhatt/stuff`.

Hoque issues (as summarized from the review threads; agent 1 owns the
final numbering in the paper):

1. **identity tautology** — the canonical identity-defense validation
   is mathematically forced (`ℓ = 0` collapses `S_pred` onto `S_act`)
   and therefore not evidence for Theorem 6.2.
2. **independent datasets** — single-source (MAP-Elites driven
   `rethinking-evals`) archives risk confirmation bias; the persistence
   check should replicate on independently collected surfaces.
3. **saturation of the grid** — a 25×25 grid at 14% / 9% coverage is
   too sparse for a genuine containment claim; the analysis needs a
   saturated (~80 filled) run.
4. **continuous vs discrete defense conflation** — the submitted draft
   tested `bounded_step`, which is not continuous, so Theorem 6.2's
   hypotheses do not apply.
5. **bootstrap / uncertainty** — no CIs on the four estimators
   `L, K, ℓ, G`.
6. **resolution sensitivity** — the 25×25 grid resolution is not
   varied; results may be artifacts of the grid.
7. **judge dependence** — alignment-deviation `f` is judge-scored; the
   surface shape depends on which judge is used. Robustness check
   missing.
8. **seed / replication** — one-shot run; no seed-level replication.
9. **GP kernel / bandwidth sensitivity** — the oblique GP defense's
   choice of RBF kernel and bandwidth is ad-hoc; sweep needed.

## Artifact table

| Hoque issue | Artifact | Path | Owner agent | Status |
|---|---|---|---|---|
| (1) identity tautology | Section 10.1.1 "Sanity check: identity defense" — reframed as a bookkeeping smoke test, not a theorem test | `<repo>/paper2_neurips.tex` §10.1.1 (lines 1067–1101) | Agent 1 (paper) | In tex |
| (1) identity tautology | `report.py::_is_identity_defense` + sanity-check annotation in `result.json` / `report.md` | `<repo>/trilemma_validator/src/trilemma_validator/report.py` | Agent 1/2 (validator) | Live |
| (1) identity tautology | `tab:smoketests` (LaTeX inline in paper) labeling sparse `D=id` runs as "Smoke tests (not a test of the theorem)" | `<repo>/paper2_neurips.tex` lines 1082–1101 | Agent 1 (paper) | In tex |
| (2) independent datasets | `tables/independent_dataset.tex` (LaTeX table; `\input{}`-ready) | `<repo>/tables/independent_dataset.tex` | Agent 3 (dataset) | Produced, **not yet `\input{}`-ed** into `paper2_neurips.tex` — flag for Agent 1 |
| (3) saturation | `live_runs/gpt35_turbo_t05_saturated/source_archive.json` — 400-eval saturated archive (82 filled, 66 unsafe, 10 boundary) | `<repo>/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json` | Agent 2 (live data) | Live |
| (3) saturation | `live_runs/gpt35_turbo_t05_saturated/result.json` + `report.md` + `validation.png` | `<repo>/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/` | Agent 2 | Live |
| (3) saturation | `live_runs/gpt35_turbo_t05_saturated/final_statistics.json`, `statistics_history.json` | same dir | Agent 2 | Live |
| (3) saturation | Figure 4 `figures/oblique_theory_vs_reality.pdf` | `<repo>/figures/oblique_theory_vs_reality.pdf` | Agent 2 / Agent 4 | Live |
| (3) saturation | `figures/bounded_step_theory_vs_reality.pdf` | `<repo>/figures/bounded_step_theory_vs_reality.pdf` | Agent 2 / Agent 4 | Live |
| (4) continuous vs discrete | `defenses.py::{smooth_nearest_safe, kernel_smoothed, softly_constrained_projection}` + `SmoothNearestSafeDefense` / `KernelSmoothedDefense` / `SoftlyConstrainedProjectionDefense` classes | `<repo>/trilemma_validator/src/trilemma_validator/defenses.py` | Agent 2 (validator) | Live |
| (4) continuous vs discrete | `sensitivity.py::oblique_target` + `run_sensitivity_cell` — oblique GP-smooth continuous defense | `<repo>/trilemma_validator/src/trilemma_validator/sensitivity.py` | Agent 4 (GP sweep) | Live |
| (4) continuous vs discrete | `csweep.py::run_continuous_sweep` — runs all 4 continuous defenses through the validator and emits `tables/continuous_sweep.tex` | `<repo>/trilemma_validator/src/trilemma_validator/csweep.py` | Agent 4 | Live |
| (4) continuous vs discrete | `tables/continuous_sweep.tex` | `<repo>/tables/continuous_sweep.tex` | Agent 4 | Live (wired into paper at line 1213) |
| (4) continuous vs discrete | Paper Section 10.1.3 "Non-vacuous validation: continuous defenses" (§sec:gp-instance) | `<repo>/paper2_neurips.tex` lines 1145–1251 | Agent 1 | In tex |
| (4) continuous vs discrete | Stress-test Section 10.1.4 "Stress test: discrete defenses" labelled "not a theorem check" | `<repo>/paper2_neurips.tex` lines 1269–1308 | Agent 1 | In tex |
| (5) bootstrap / CIs | `uncertainty.py::bootstrap_ci, bootstrap_estimator_cis` | `<repo>/trilemma_validator/src/trilemma_validator/uncertainty.py` | Agent 2 | Live |
| (5) bootstrap / CIs | `lipschitz.py::pairwise_L_ratios, pairwise_G_ratios, per_cell_ell_ratios, per_pair_K_ratios` (per-pair populations for resampling) | `<repo>/trilemma_validator/src/trilemma_validator/lipschitz.py` lines 311–406 | Agent 2 | Live |
| (5) bootstrap / CIs | `--bootstrap B` CLI flag writing `bootstrap` block into `result.json` | `<repo>/trilemma_validator/src/trilemma_validator/cli.py` lines 91–98, 134–171 | Agent 2 | Live |
| (5) bootstrap / CIs | `tables/ci.tex` | `<repo>/tables/ci.tex` | Agent 2 | Live (wired into paper at line 1266) |
| (6) resolution sensitivity | `resolution.py::run_resolution_sweep, subsample_heatmap` | `<repo>/trilemma_validator/src/trilemma_validator/resolution.py` | Agent 4 | Live |
| (6) resolution sensitivity | `live_runs/gpt35_turbo_t05_saturated/resolution/` — per-resolution `result.json` | `<repo>/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/resolution/` | Agent 4 | Live |
| (6) resolution sensitivity | `tables/resolution.tex` | `<repo>/tables/resolution.tex` | Agent 4 | Live (wired into paper at line 1233) |
| (7) judge dependence | `cli.py::_maybe_pending_judge_stub` + `--judge` flag on `experiment` / `pipeline` subcommands, propagating to `RETHINKING_JUDGE_MODEL` | `<repo>/trilemma_validator/src/trilemma_validator/cli.py` lines 277–327, 628–638, 665–675 | Agent 2 (validator) | Live |
| (7) judge dependence | `live_runs/judge_robustness_pending.md` — placeholder emitted when no API key | `<repo>/trilemma_validator/live_runs/judge_robustness_pending.md` | Agent 2 | Live (placeholder; real table TODO) |
| (7) judge dependence | Paper Appendix "Judge robustness" (`\label{app:judge-robustness}`) | `<repo>/paper2_neurips.tex` lines 1765–1779 | Agent 1 | In tex (placeholder prose; TODO comment in-text at line 1768) |
| (8) seed / replication | Headline claim "two runs … 0 interior false positives on either run" captured in `trilemma_validator/live_runs/README.md` | `<repo>/trilemma_validator/live_runs/README.md` | Agent 2 | Live |
| (8) seed / replication | Per-target replication archives `live_runs/gpt5_mini_t03/`, `live_runs/gpt35_turbo_t05/` | `<repo>/trilemma_validator/live_runs/gpt5_mini_t03/`, `<repo>/trilemma_validator/live_runs/gpt35_turbo_t05/` | Agent 2 | Live |
| (8) seed / replication | `tab:seed-replication` in paper | **NOT PRESENT** | Agent 1 | TODO — label promised in the reproducibility checklist; not referenced in `paper2_neurips.tex`. Either produce + wire, or drop from the checklist. |
| (9) GP kernel sensitivity | `kernels.py` — `rbf_kernel`, `matern32_kernel`, `matern52_kernel` + gradient variants + `get_kernel` factory | `<repo>/trilemma_validator/src/trilemma_validator/kernels.py` | Agent 4 | Live |
| (9) GP kernel sensitivity | `sensitivity.py::run_sensitivity_sweep, run_sensitivity_from_archive` — RBF × Matérn-3/2 × Matérn-5/2 crossed with σ ∈ {0.1, 0.2, 0.4} | `<repo>/trilemma_validator/src/trilemma_validator/sensitivity.py` lines 309–455 | Agent 4 | Live |
| (9) GP kernel sensitivity | `live_runs/gpt35_turbo_t05_saturated/sensitivity/` — per-cell `result.json` + `sensitivity.json` | `<repo>/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/sensitivity/` | Agent 4 | Live |
| (9) GP kernel sensitivity | `tables/gp_sensitivity.tex` | `<repo>/tables/gp_sensitivity.tex` | Agent 4 | Live (wired into paper at line 1224) |

## Cross-cutting artifacts (not tied to one Hoque issue)

| Artifact | Path | Owner | Purpose |
|---|---|---|---|
| `paper2_neurips.tex` (NeurIPS 2025 target) | `<repo>/paper2_neurips.tex` | Agent 1 | main submission source |
| `paper2_v2.tex` (draft target) | `<repo>/paper2_v2.tex` | Agent 1 | earlier-revision source |
| `paper2_defense_impossibility.tex` (preprint target) | `<repo>/paper2_defense_impossibility.tex` | Agent 1 | pre-NeurIPS standalone preprint |
| `neurips_2025.sty` | `<repo>/neurips_2025.sty` | (vendored from NeurIPS) | style file |
| Validator package `trilemma_validator/` | `<repo>/trilemma_validator/` | Agents 1–4 | code |
| Lean artifact | `<repo>/ManifoldProofs/` | Lean agent | 46-file Lean 4 / Mathlib formalization |
| REPRODUCIBILITY.md | `<repo>/trilemma_validator/REPRODUCIBILITY.md` | this agent | commands to reproduce every table / figure |
| Smoke tests | `<repo>/trilemma_validator/tests/test_smoke.py` | this agent | package smoke tests |
| NeurIPS compliance audit | `<repo>/outputs/neurips_compliance.md` | this agent | format audit |
| Code hygiene audit | `<repo>/outputs/code_hygiene.md` | this agent | static audit |
| This manifest | `<repo>/outputs/paper_artifact_manifest.md` | this agent | inventory |
| `outputs/field-gap-analysis.md` | `<repo>/outputs/field-gap-analysis.md` | prior research agent | gap analysis vs field |
| `outputs/textbook-plan.md` | `<repo>/outputs/textbook-plan.md` | prior research agent | textbook plan |
| `outputs/defense-trilemma-lean-audit-audit.md` | `<repo>/outputs/defense-trilemma-lean-audit-audit.md` | prior Lean agent | Lean audit |
| `outputs/typos.md` | `<repo>/outputs/typos.md` | prior review agent | typo list |
| `outputs/prediction-verification.md`, `additional-predictions.md`, `derived-predictions.md`, `vulnerability-landscape-article.md` | `<repo>/outputs/` | prior agents | preserved |

## Flags raised during this audit

- **`tab:seed-replication` promised but not wired.** The
  reproducibility inventory listed this table; `paper2_neurips.tex`
  does not reference it. Either Agent 1 adds a `\input{tables/seed_replication.tex}`
  with the corresponding label, or the item is dropped from the
  inventory.
- **`tab:independent-dataset` produced but not wired.** Agent 3
  produced `tables/independent_dataset.tex` but Agent 1's `.tex` does
  not contain `\input{tables/independent_dataset.tex}` or the
  `\label{tab:independent-dataset}`. One of the two agents owns the
  wire-in.
- **`tab:judge-robustness` pending live data.** Paper Appendix has a
  `% TODO: Agent 4 is wiring a --judge flag ...` comment at line 1768;
  once the two-judge archive lands, the `live_runs/judge_robustness_pending.md`
  stub should be replaced by real `result.json`s and a table.
- **CLI `NameError` for `--defense oblique_gp_smooth`.** `cli.py:422`
  references `_sweep_gp_smooth_oblique`, which is never defined. See
  `outputs/code_hygiene.md` §2.
- **Stale `paper2_neurips.pdf`.** The PDF at the repo root is dated
  2026-04-19 14:08 and predates the `.tex` addition of the four new
  tables and the continuous-defense section. Agent 1 should recompile.
