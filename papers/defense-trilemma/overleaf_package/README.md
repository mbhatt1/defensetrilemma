# Defense Trilemma — Overleaf Upload Package

Three versions of the paper plus all figures and tables they reference,
ready to upload to Overleaf as a single project.

## Contents

```
overleaf_package/
├── paper2_v3.tex            ← primary full version (most up-to-date)
├── paper2_v2.tex            ← older long-form version (pre-v3 structure)
├── paper2_neurips.tex       ← NeurIPS preprint flavor
├── neurips_2025.sty         ← NeurIPS 2025 style file (loaded by all three)
├── figures/
│   ├── oblique_theory_vs_reality.pdf          ← Figure 4 (continuous validation)
│   ├── bounded_step_theory_vs_reality.pdf     ← Figure 4 companion (discrete stress)
│   ├── theory_vs_reality_saturated.pdf        ← legacy filename, identical to oblique_*
│   ├── multi_turn_plot.pdf                    ← Theorem 9.1 (running-max monotonicity)
│   ├── stochastic_histogram.pdf               ← Theorem 9.2 (stochastic dichotomy)
│   ├── k_tradeoff.pdf                         ← Theorem 7.3 (K* regime split)
│   ├── tau_sweep.pdf                          ← τ-sensitivity
│   └── judge_scatter.pdf                      ← 4-judge pairwise scatter (real data)
├── tables/
│   ├── ci.tex                        ← bootstrap B=1000 CIs (L,K,ℓ,G)
│   ├── continuous_sweep.tex          ← 4 continuous defenses
│   ├── counterexample_ablation.tex   ← C.1/C.2/C.3 empirical ablation
│   ├── forced_collapse.tex           ← Theorem 8.3 mechanism demo
│   ├── gp_sensitivity.tex            ← 9-config kernel × σ sweep
│   ├── higher_dim_lipschitz.tex      ← 2D vs 768-d MPNet L,G
│   ├── independent_dataset.tex       ← cross-target (gpt-3.5 + gpt-4o-mini)
│   ├── judge_committee.tex           ← 3 committee aggregations vs canonical
│   ├── judge_robustness.tex          ← 4 judges on saturated archive
│   ├── llamaguard_demo.tex           ← Llama-Guard-3-1B under Theorem 8.3
│   ├── multi_turn.tex                ← Theorem 9.1 per-trajectory data
│   ├── pair_baseline.tex             ← PAIR-style attack w/ vs w/o wrapper
│   ├── paraphrase_unsafe.tex         ← 1/66 strict-unsafe paraphrase
│   ├── pipeline.tex                  ← Theorem 9.3 K-composition bound
│   ├── resolution.tex                ← 13/17/21/25 grid resolution sweep
│   ├── seed_replication.tex          ← multi-seed MAP-Elites replication
│   ├── stochastic.tex                ← Theorem 9.2 per-cell P(unsafe)
│   └── three_target_sweep.tex        ← gpt-3.5 + gpt-4o-mini + gpt-4o
└── README.md
```

## How to use on Overleaf

1. Upload this entire directory (or `defense_trilemma_overleaf.zip`) to a
   new Overleaf project.
2. Set the **Main document** to one of:
   - `paper2_v3.tex` — the current/primary version (23 pages including appendices)
   - `paper2_v2.tex` — older full-length version
   - `paper2_neurips.tex` — NeurIPS preprint flavor (stale relative to v3; lacks the late additions)
3. Set the TeX Live version to 2023 or later.
4. Recompile twice (for cross-references).

All three `.tex` files are self-contained — bibliography is inline
`\bibitem` entries, no external `.bib`. They `\input{tables/...}` for
every data table and `\includegraphics{figures/...}` for every figure;
all referenced artifacts are included.

## Reproducibility

Every numerical claim in the paper traces to a file under
`trilemma_validator/live_runs/` in the full source repository:
https://github.com/mbhatt1/stuff

The empirical pipeline is the `trilemma_validator/` Python package;
each table in `tables/` is auto-generated from a JSON artifact.
Regeneration commands are documented in `trilemma_validator/REPRODUCIBILITY.md`
and the per-experiment scripts under `trilemma_validator/scripts/`.

## Experiment provenance

| Table / figure                | Source script                                    | Type          |
|-------------------------------|--------------------------------------------------|---------------|
| `ci.tex`                      | `uncertainty.py` (bootstrap)                     | offline       |
| `continuous_sweep.tex`        | `trilemma csweep`                                | offline       |
| `counterexample_ablation.tex` | `counterexample_ablation.py`                     | offline       |
| `forced_collapse.tex`         | `demo_forced_collapse.py`                        | OpenAI        |
| `gp_sensitivity.tex`          | `trilemma sensitivity`                           | offline       |
| `higher_dim_lipschitz.tex`    | `higher_dim_lipschitz.py`                        | offline       |
| `independent_dataset.tex`     | `retarget_archive.py --target gpt-4o-mini`       | OpenAI        |
| `judge_committee.tex`         | `judge_committee.py`                             | offline       |
| `judge_robustness.tex`        | `rescore_with_judge.py` × 3 judges               | OpenAI        |
| `llamaguard_demo.tex`         | `llamaguard_probe.py`                            | local Ollama  |
| `multi_turn.tex`              | `multi_turn_demo.py`                             | OpenAI        |
| `pair_baseline.tex`           | `pair_baseline.py`                               | OpenAI        |
| `paraphrase_unsafe.tex`       | `paraphrase_completeness_check.py`               | OpenAI        |
| `pipeline.tex`                | `pipeline_demo.py`                               | offline       |
| `resolution.tex`              | `trilemma resolution`                            | offline       |
| `seed_replication.tex`        | full MAP-Elites pipeline, 2 independent runs     | OpenAI        |
| `stochastic.tex`              | `stochastic_demo.py`                             | OpenAI        |
| `three_target_sweep.tex`      | `retarget_archive.py` × 3 targets                | OpenAI        |
| `multi_turn_plot.pdf`         | `multi_turn_demo.py`                             | OpenAI        |
| `stochastic_histogram.pdf`    | `make_fig_stochastic_histogram.py`               | offline       |
| `k_tradeoff.pdf`              | `make_fig_ktradeoff.py`                          | offline       |
| `tau_sweep.pdf`               | `make_fig_tau_sweep.py`                          | offline       |
| `judge_scatter.pdf`           | `make_fig_judge_scatter_real.py`                 | offline (real data) |
| `oblique_theory_vs_reality.pdf` | `make_paper_figure.py`                         | offline       |
