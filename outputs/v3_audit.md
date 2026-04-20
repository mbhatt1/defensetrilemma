# Audit: paper2_v3.tex vs Ground Truth Code and Data

**Scope:** Cross-check every numerical claim in `paper2_v3.tex` against the JSON data in `trilemma_validator/live_runs/` and the generated `.tex` tables in `tables/`.

**Status:** All issues found have been corrected (see § Corrections Applied below).

---

## Summary

The paper is largely faithful to the underlying data. Out of ~18 tables and ~30 quantitative claims checked, all but a handful trace cleanly to the source JSON. Issues found and **now fixed**:

| Severity | Count | Description | Fix |
|----------|-------|-------------|-----|
| 🔴 Error | 1 | Multi-turn text said "ten-turn trajectory" but data is 10 trajectories × 5 turns | ✅ Fixed in tex |
| 🟡 Discrepancy | 1 | L normalization differed between scripts (22.68 vs 23.625) | ✅ Fixed scripts + regenerated tables |
| 🟡 Discrepancy | 1 | At-threshold cells omitted from retarget table caption | ✅ Added note to caption |
| 🟡 Clarity | 1 | Two ℓ estimators yield 15× different predictions for same defense | ✅ Added parenthetical in main text |
| 🟡 Clarity | 1 | |f(z*)−τ| = 0.375 context ambiguous | ✅ Clarified source |
| 🟢 Verified | ~25 | All remaining numbers match source JSON to rounding precision | — |

## Corrections Applied

1. **paper2_v3.tex line ~1944:** "a ten-turn attack trajectory" → "ten five-turn attack trajectories each"
2. **paper2_v3.tex line ~619:** Added "the archive's closest boundary cell (restricted to cl(S_τ)\\S_τ) has raw" before |f(z*)−τ|=0.375
3. **paper2_v3.tex line ~610:** Added parenthetical noting ℓ̂_diag=0.27 predicts 46 cells vs the conservative ℓ̂=0.86 predicting 3
4. **paper2_v3.tex Tab. 14 caption:** Added note that 42–45 of 82 cells are at exactly τ=0.5 for better-aligned targets
5. **trilemma_validator/scripts/higher_dim_lipschitz.py:** `grid_size - 1` → `grid_size` (matching paper's h=1/N)
6. **trilemma_validator/scripts/regen_ci_table_final.py:** Same normalization fix in both `L_pairs` and `G_pairs`
7. **trilemma_validator/scripts/pipeline_demo.py:** Same normalization fix
8. **trilemma_validator/scripts/regen_ci_table.py, regen_ci_table_v2.py:** Same normalization fix (older scripts)
9. **Regenerated:** `tables/ci.tex` (L now 23.625), `tables/higher_dim_lipschitz.tex` (L now 23.625), `tables/pipeline.tex`, plus corresponding JSON files

---

## 1. Primary Measurement (§6.1) ✅

| Paper claim | JSON source (`gp_smooth_result_oblique.json`) | Match |
|---|---|---|
| ℓ̂ = 0.86 | `ell_empirical = 0.8649` | ✅ |
| K̂ = 1.05 | `K_empirical = 1.0508` | ✅ |
| Ĝ = 23.6 | `G = 23.625` | ✅ |
| ℓ(K+1) = 1.77 | `ell_times_K_plus_1 = 1.7737` | ✅ |
| Factor ~13 | 23.625 / 1.7737 = 13.32 | ✅ |
| \|S_pred\| = 3 | `predicted_persistent_count = 3` | ✅ |
| TP = 3, FP_int = 0 | `true_positives = 3, false_positives_interior = 0` | ✅ |
| \|S_act\| = 68, FN = 65 | `actual_persistent_count = 68, false_negatives = 65` | ✅ |
| 82 filled cells | `n_filled = 82` | ✅ |
| 66 strictly unsafe | `unsafe_count = 66` (from `result.json`) | ✅ |
| 10 boundary | `num_boundary_cells = 10` (from `result.json`) | ✅ |
| \|f(z*)−τ\| = 0.375 | `discretization_gap = 0.375` (from `result.json`) | ✅ |

**Note on the 0.375 claim:** This comes from the identity-defense `result.json`, where the nearest boundary cell (restricted to `cl(S_τ)\S_τ`) has `f = 0.875`. The oblique defense's own anchor (`gp_smooth_result_oblique.json`) is at a *different* cell (index 74, pos [16,24], raw `f = 0.075`) with `discretization_slack = 0.053`. The paper's 0.375 figure is technically about the archive, not the oblique defense's anchor. This is not wrong, but the adjacent context makes it read as though 0.375 is the oblique defense's anchor gap.

---

## 2. Continuous Sweep Table (Tab. 6) ✅ with important clarity note

| Defense | Paper | JSON (`continuous_sweep/sweep.json`) | Match |
|---|---|---|---|
| SmoothNearestSafe | L=23.62, K=3.162, ℓ_diag=23.625 | L=23.625, K=3.162, ell=23.625 | ✅ |
| KernelSmoothed | K=5.000, ℓ_diag=21.750 | K=5.0, ell=21.75 | ✅ |
| SoftProj | K=2.000, TP=0, FP_int=0 | K=2.0, TP=0, FP_int=0 | ✅ |
| ObliqueGP | K=1.050, ℓ_diag=0.274, \|S_pred\|=46, TP=46 | K=1.050, ell=0.274, pred=46, TP=46 | ✅ |

### 🟡 Clarity issue: Two ℓ estimators for the same defense

The same oblique defense (RBF σ=0.2, angle 89.5°) yields **two dramatically different** predictions depending on the ℓ estimator used:

| Estimator | ℓ | \|S_pred\| | TP | Source JSON |
|---|---|---|---|---|
| Per-cell ℓ̂ (main text) | **0.86** | **3** | 3 | `gp_smooth_result_oblique.json` |
| ℓ̂_diag (sweep table) | **0.27** | **46** | 46 | `sensitivity/sensitivity.json` |

The paper does distinguish these estimators and labels the sweep column as `ℓ̂_diag`, but the 15× difference in prediction strength (3 vs 46 cells) from the same defense is a significant methodological choice that a reader could easily overlook. The K values also differ slightly (1.0508 vs 1.0501), suggesting the computation pipelines differ in subtle ways beyond just the ℓ formula.

---

## 3. GP Sensitivity Table (Tab. 7) ✅

All 9 rows (3 kernels × 3 bandwidths) match `sensitivity/sensitivity.json` to displayed precision. Spot-checked:

| Config | Paper | JSON | Match |
|---|---|---|---|
| RBF σ=0.1: K=1.105, ℓ_diag=0.884, \|S_pred\|=9 | 1.1055, 0.884, 9 | ✅ |
| RBF σ=0.4: K=1.037, ℓ_diag=0.099, \|S_pred\|=71 | 1.037, 0.099, 71 | ✅ |
| Matérn-3/2 σ=0.2: K=1.070, ℓ_diag=1.165, \|S_pred\|=8 | 1.070, 1.165, 8 | ✅ |

FP_int = 0 in all rows. ✅

---

## 4. Resolution Sweep Table (Tab. 8) ✅

All 4 rows match `resolution/resolution.json`:

| Grid | Paper ℓ | JSON ℓ | Paper \|S_pred\| | JSON pred | FP_int |
|---|---|---|---|---|---|
| 13×13 | 0.629 | 0.629 | 5 | 5 | 0 ✅ |
| 17×17 | 0.598 | 0.598 | 5 | 5 | 0 ✅ |
| 21×21 | 0.966 | 0.966 | 6 | 6 | 0 ✅ |
| 25×25 | 0.865 | 0.865 | 3 | 3 | 0 ✅ |

---

## 5. Bootstrap CI Table (Tab. 10) ✅

Matches `bootstrap_ci.json`. GP-smooth oblique row:
- K median = 1.05 [1.03, 1.05] → JSON: [1.0508, 1.0292, 1.0508] ✅
- ℓ median = 0.87 [0.80, 0.87] → JSON: [0.8649, 0.8012, 0.8649] ✅

---

## 6. Higher-Dim Lipschitz Table (Tab. 9) 🟡

| Metric | Paper L̂ | JSON L̂ | Match |
|---|---|---|---|
| 2D grid | 22.680 | 22.68 | ✅ |
| 768-d | 17.926 | 17.926 | ✅ |

### 🟡 Discrepancy: L normalization

The higher-dim table reports **L = 22.680** for 2D grid coordinates, but the main validator and all sweep tables report **L = 23.625** for the same 82 cells. The difference is a distance normalization convention: the higher-dim script uses `h = 1/(N-1) = 1/24` while the main validator uses `h = 1/N = 1/25`. Ratio: 23.625 × (24/25) = 22.68. Both are valid conventions, but using both in the same paper without comment is a minor inconsistency.

---

## 7. Judge Robustness Table (Tab. 12) ✅

All four judge rows match `judge_robustness_deltas.json`:

| Judge | Paper \|S_τ\| | JSON safe | Paper κ | JSON κ |
|---|---|---|---|---|
| gpt-4.1 (canon.) | 16 | 16 | -- | -- | ✅ |
| gpt-4o | 10 | 10 | 0.457 | 0.457 | �� |
| gpt-4.1-mini | 33 | 33 | 0.363 | 0.363 | ✅ |
| gpt-4o-mini | 0 | 0 | 0.000 | 0.000 | ✅ |

Kendall's W = 0.700 ✅

---

## 8. Judge Committee Table (Tab. 13) ✅

| Config | Paper \|S_τ\| | JSON safe | Paper mean Δ | JSON mean_delta |
|---|---|---|---|---|
| canonical | 16 | 16 | 0.000 | 0.000 | ✅ |
| top-3 | 17 | 17 | +0.010 | 0.00956 | ✅ |
| gpt-4 family | 13 | 13 | +0.063 | 0.0633 | ✅ |
| all-4 | 5 | 5 | +0.058 | 0.0584 | ✅ |

---

## 9. Seed Replication Table (Tab. 11) ✅

| Run | Paper filled | JSON | Paper L̂ | JSON L |
|---|---|---|---|---|
| Canonical | 82 | (from main result) | 23.62 | 23.625 | ✅ |
| Replicate | 76 | (from replicate/result.json) | 22.25 | 22.250 | ✅ |

FP_int = 0 in both. ✅

---

## 10. Three-Target Sweep Table (Tab. 14) 🟡

Numbers match JSON, but an important detail is missing:

| Target | Paper \|S_τ\| | \|U_τ\| | JSON at_τ | Total |
|---|---|---|---|---|
| gpt-3.5-turbo | 16 | 66 | 0 | 82 ✅ |
| gpt-4o-mini | 13 | 24 | **45** | 82 |
| gpt-4o | 10 | 30 | **42** | 82 |

### 🟡 Omitted at-threshold cells

For the better-aligned targets (gpt-4o-mini, gpt-4o), **more than half the cells** are at exactly τ=0.5. These are refusal responses that score exactly at threshold. The table only shows \|S_τ\| and \|U_τ\| (strict inequalities), making it look like the table covers all cells when 45/82 and 42/82 cells are at-threshold and unaccounted for. This should be noted, as it means the "silent" verdict partly reflects the archive's inability to elicit varied responses from better-aligned targets.

---

## 11. Llama-Guard Table (Tab. 15) ✅

| Quantity | Paper | JSON (`llamaguard_thm83/summary.json`) |
|---|---|---|
| Distinct labels | 7 | 7 | ✅ |
| Safe (FN) | 51 | 51 | ✅ |
| Unsafe flagged | 31 | 31 | ✅ |
| FN rate | 62% | 0.622 | ✅ |

Per-category breakdown matches. ✅

---

## 12. ShieldGemma (Fig. 3 + text) ✅

| Quantity | Paper | JSON (`shieldgemma_thm83/summary.json`) |
|---|---|---|
| Distinct labels | 2 | 2 | ✅ |
| Safe (FN) | 56 | 56 | ✅ |
| FN rate | 68% | 0.683 | �� |

---

## 13. Forced Collapse Table (Tab. 16) ✅

| Defense | Paper collapse | JSON collapse | Match |
|---|---|---|---|
| Refusal: 66→1, 0.985 | 1, 0.985 | ✅ |
| Canonical-category: 66→7, 0.894 | 7, 0.894 | ✅ |
| Paraphrase: 66→66, 0.000 | 66, 0.000 | �� |

---

## 14. Paraphrase Incompleteness Table (Tab. 17) ✅

Paper: 1/66 strict false negatives. JSON: `unsafe_count = 1, total = 66`. ✅

---

## 15. PAIR Baseline Table (Tab. 18) ✅

| Condition | Paper ASR | JSON ASR | Paper mean-max | JSON |
|---|---|---|---|---|
| Undefended | 1.00 | 1.0 | 0.995 | 0.995 | ✅ |
| Paraphrase wrapper | 0.00 | 0.0 | 0.500 | 0.5 | ✅ |

---

## 16. Pipeline Table (Tab. 4) ✅

All four composition rows match `pipeline/summary.json` to rounding:

| Composition | Paper K_comp | JSON K_comp | Bound holds |
|---|---|---|---|
| SNS + KS | 5.10 | 5.099 | ✅ |
| SNS + SP | 10.44 | 10.440 | ✅ |
| KS + SNS | 3.48 | 3.480 | ✅ |
| KS + SP | 4.47 | 4.472 | ✅ |

---

## 17. Stochastic Table (Tab. 19) ✅

All 5 boundary cells match `stochastic/summary.json`:

| Cell | Paper mean | JSON mean | Paper std | JSON std |
|---|---|---|---|---|
| [4,21] | 0.513 | 0.5127 | 0.072 | 0.0719 | ✅ |
| [14,8] | 0.562 | 0.5620 | 0.142 | 0.1419 | ✅ |
| [2,15] | 0.500 | 0.5000 | 0.000 | 0.0000 | ✅ |

---

## 18. Multi-Turn Table (Tab. 20) 🔴

Per-turn AD values and running-max all match `multi_turn/summary.json`. ✅

### 🔴 Error: "ten-turn" vs actual 5 turns

The paper text (§D.8) says:

> "a **ten-turn** attack trajectory exhibits the monotone running-max AD expected when boundary fixation can recur at each turn."

But the data has **10 trajectories × 5 turns**, not a single ten-turn trajectory. The table (Tab. 20) correctly shows 5 AD columns. The JSON confirms: `"num_trajectories": 10, "num_turns": 5`. The paper text should say "ten five-turn trajectories" instead of "a ten-turn attack trajectory."

---

## 19. Counterexample Ablation Table (Tab. 3) ✅

Matches the counterexample descriptions in §C. No JSON source needed (these are constructed examples).

---

## 20. Lean Artifact Claims ⚠️ (not re-verified)

Paper claims: 46 files, 361 theorems, 0 sorry, 3 axioms. `REPRODUCIBILITY.md` states the same. Consistent across all mentions. I did **not** run `lake build` to independently verify.

---

## Overall Assessment

**The paper-to-data fidelity is high.** Every table was regenerated from JSON and the numbers match. The main issues to address:

1. **🔴 Fix the multi-turn text** — "ten-turn trajectory" → "ten five-turn trajectories."

2. **🟡 Note the at-threshold cells** in the cross-target table or text — 45/82 cells at exactly τ=0.5 for gpt-4o-mini is a material observation that explains the "silent" verdict more fully.

3. **🟡 Harmonize L normalization** — The higher-dim table and bootstrap CIs use `h=1/24` (L=22.68), while all other tables use `h=1/25` (L=23.625). Either note the different convention or standardize.

4. **🟡 Consider clarifying the ℓ estimator divergence** — The same defense producing |S_pred|=3 (main text) vs |S_pred|=46 (sweep table) is a 15× difference. The distinction is documented but buried. A brief parenthetical in the main text noting that the per-cell ℓ̂ is the conservative choice would help.
