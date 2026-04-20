# Defense Trilemma — Reproducibility Guide

Every number in `paper2_v3.tex` traces to a file under this repo. This
guide lists exact commands to reproduce each experiment, verify the
Lean artifact, and audit any paper claim against its source data.

## Prerequisites

| Component | Version | Install |
|---|---|---|
| Python | ≥ 3.10 | `brew install python@3.11` (macOS) |
| `openai` SDK | ≥ 2.21 | `pip install openai numpy matplotlib scipy pyyaml` |
| TinyTeX or TeX Live | 2023+ | https://tug.org/texlive/ |
| Lean 4.28.0 + Mathlib v4.28.0 | exact | https://leanprover-community.github.io (optional; verifies the 361 theorems) |

## One-command reproduction

```bash
export OPENAI_API_KEY=sk-...
make all       # tables + figures + paper + zip
```

## Step-by-step reproduction

```bash
make validate          # rerun saturated-archive validator (GP smooth, bootstrap CIs, sensitivity, csweep, resolution)
make tables figures    # regenerate every *.tex / *.pdf from live_runs/ JSON
make paper             # compile paper2_v3.pdf + paper2_v3_submission.pdf
make zip               # rebuild defense_trilemma_overleaf.zip
```

## Auditing any paper claim against source data

Every numerical claim in the paper comes from a persisted JSON. The
pattern to verify:

```bash
python3 -c "
import json
r = json.load(open('trilemma_validator/live_runs/gpt35_turbo_t05_saturated/gp_smooth_result_oblique.json'))
print('K_empirical:', r['K_empirical'])
print('ell_empirical:', r['ell_empirical'])
print('TP:', r['true_positives'])
print('FP_int:', r['false_positives_interior'])
"
```

Data layout by experiment:

| Paper element | Source file |
|---|---|
| Fig. 4 (theory vs reality) | `trilemma_validator/live_runs/gpt35_turbo_t05_saturated/gp_smooth_result_oblique.json` |
| Table: bootstrap CIs | `trilemma_validator/live_runs/gpt35_turbo_t05_saturated/bootstrap_ci.json` |
| Table: GP kernel sensitivity | `trilemma_validator/live_runs/gpt35_turbo_t05_saturated/sensitivity/sensitivity.json` |
| Table: continuous-defense sweep | `trilemma_validator/live_runs/gpt35_turbo_t05_saturated/continuous_sweep/sweep.json` |
| Table: resolution sweep | `trilemma_validator/live_runs/gpt35_turbo_t05_saturated/resolution/resolution.json` |
| Table: higher-dim Lipschitz | `trilemma_validator/live_runs/higher_dim_lipschitz.json` |
| Table: judge robustness | `trilemma_validator/live_runs/judge_robustness_deltas.json` |
| Table: judge committee | `trilemma_validator/live_runs/judge_committee/summary.json` |
| Table: seed replication | `trilemma_validator/live_runs/gpt35_turbo_t05_replicate/result.json` |
| Table: three-target sweep | `trilemma_validator/live_runs/gpt{4o,4o_mini}_retargeted/source_archive.json` |
| Table: Llama Guard demo | `trilemma_validator/live_runs/llamaguard_thm83/summary.json` |
| Table: multi-turn | `trilemma_validator/live_runs/multi_turn/summary.json` |
| Table: stochastic | `trilemma_validator/live_runs/stochastic/summary.json` |
| Table: pipeline | `trilemma_validator/live_runs/pipeline/summary.json` |
| Table: forced-collapse | `trilemma_validator/live_runs/forced_collapse/summary.json` |
| Table: paraphrase-unsafe | `trilemma_validator/live_runs/forced_collapse/paraphrase_summary.json` |
| Table: counterexamples | `trilemma_validator/live_runs/counterexamples/summary.json` |
| Table: PAIR baseline | `trilemma_validator/live_runs/pair_baseline/summary.json` |

## Verifying the Lean artifact

```bash
cd ManifoldProofs
lake build
# Expected: no `sorry`, no `admit`, 361 theorem/lemma/corollary declarations
```

The abstract claims "46 files, ∼360 theorems, three standard axioms" — reproduce:

```bash
ls ManifoldProofs/ManifoldProofs/*.lean ManifoldProofs/ManifoldProofs.lean | wc -l   # 46
grep -rE '^(theorem|lemma|corollary) ' ManifoldProofs/ManifoldProofs/*.lean ManifoldProofs/ManifoldProofs.lean | wc -l   # 361
grep -rE '^\s*sorry\s*$|:= sorry\b' ManifoldProofs/ManifoldProofs/*.lean   # 0
```

## Common failure modes

- **OpenAI rate limits during retarget / PAIR baseline**: scripts use 8-attempt exponential backoff (up to 60s). If a call still errors, rerun — the harness skips already-completed cells via idempotent output paths.
- **Lean-toolchain mismatch**: artifact is pinned to Lean 4.28.0 + Mathlib v4.28.0. Newer versions may break. `lean-toolchain` file pins this.
- **PYTHONPATH required for the figure script**: `make_paper_figure.py` imports `trilemma_validator.defenses`; prefix invocations with `PYTHONPATH=trilemma_validator/src`.
