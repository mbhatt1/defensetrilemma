# Audit 5 — Table vs JSON Cross-Check

**Auditor:** Agent 5 of 10 (READ-ONLY)
**Scope:** `ci.tex`, `continuous_sweep.tex`, `gp_sensitivity.tex`, `resolution.tex`, `higher_dim_lipschitz.tex`, `seed_replication.tex`, `three_target_sweep.tex`, `independent_dataset.tex`
**Date:** 2026-04-19

Legend: OK = exact match (within stated rounding), WARN = rounding convention quirk, FAIL = value cannot be reproduced from the cited JSON.

Rounding conventions. Tables use 2, 3, or 5 fractional digits depending on column. Unless noted, rounding is "half-up" to the shown precision and all values within ±1 ulp of the displayed digit are marked OK.

Absolute paths:
- `/Users/mbhatt/stuff/tables/ci.tex`
- `/Users/mbhatt/stuff/tables/continuous_sweep.tex`
- `/Users/mbhatt/stuff/tables/gp_sensitivity.tex`
- `/Users/mbhatt/stuff/tables/resolution.tex`
- `/Users/mbhatt/stuff/tables/higher_dim_lipschitz.tex`
- `/Users/mbhatt/stuff/tables/seed_replication.tex`
- `/Users/mbhatt/stuff/tables/three_target_sweep.tex`
- `/Users/mbhatt/stuff/tables/independent_dataset.tex`

Primary JSON sources:
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/continuous_sweep/sweep.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/sensitivity/sensitivity.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/resolution/resolution.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/result.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/gp_smooth_result_oblique.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_replicate/result.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt4o_mini_retargeted/validate_gp.json/result.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt4o_retargeted/validate_gp.json/result.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/higher_dim_lipschitz.json`

---

## 1. `ci.tex` — bootstrap confidence intervals (B=1000, 95% percentile CI)

| Row | Cell | Table value | JSON reference | Status |
|---|---|---|---|---|
| identity | L_med | 22.88 | no stored bootstrap json; empirical max = 23.625 | ⚠️ cannot independently verify (no bootstrap JSON exists); plausible given L_max = 23.625 |
| identity | L CI | [21.00, 23.63] | same | ⚠️ plausible (upper ≤ L_max); not independently verifiable |
| identity | K_med | 1.000 | identity defense: targets=source, so all K ratios = 1.0 | ✅ correct by construction |
| identity | K CI | [1.000, 1.000] | same | ✅ correct by construction |
| identity | ℓ_med | 0.000 | identity moves no cells → `per_cell_ell_ratios` returns empty array → `bootstrap_ci` returns `(nan, nan, nan)` (see `uncertainty.py` lines 58–61) | ⚠️ code returns NaN, not 0; table reports 0. Convention substitution (not wrong, but undocumented). |
| identity | ℓ CI | [0.000, 0.000] | same | ⚠️ same NaN→0 convention note |
| identity | G_med | 22.88 | empirical G=23.625 | ⚠️ plausible; no stored bootstrap |
| identity | G CI | [21.00, 23.63] | same | ⚠️ plausible |
| GP-smooth oblique | L_med | 22.88 | same archive | ⚠️ plausible, not independently verifiable |
| GP-smooth oblique | L CI | [21.00, 23.63] | same | ⚠️ plausible |
| GP-smooth oblique | K_med | 1.050 | `gp_smooth_result_oblique.json` K_empirical = 1.0501173326701811 | ✅ median ≈ max (distribution very concentrated near 1.05) |
| GP-smooth oblique | K CI | [1.027, 1.098] | K_empirical max = 1.0501 | ⚠️ upper bound 1.098 > max 1.0501 — **IMPOSSIBLE** for a bootstrap percentile of `max(K_ratios)` which must satisfy CI ≤ population max. ❌ **FAIL** |
| GP-smooth oblique | ℓ_med | 0.928 | `gp_smooth_result_oblique.json` ell_empirical = 0.8648970604973426 (per-cell estimator, which is what `uncertainty.bootstrap_estimator_cis` uses per `per_cell_ell_ratios`) | ❌ **FAIL** — 0.928 > 0.8649 is impossible for median of bootstrap-max on a population with max 0.8649 |
| GP-smooth oblique | ℓ CI | [0.629, 1.760] | population max = 0.8649 | ❌ **FAIL** — upper CI 1.760 exceeds the population max 0.8649 by 2× |
| GP-smooth oblique | G_med | 22.88 | empirical G=23.625 (same archive) | ⚠️ plausible |
| GP-smooth oblique | G CI | [21.00, 23.63] | same | ⚠️ plausible |

**Verdict:** ❌ (the K and ℓ CIs for GP-smooth oblique are inconsistent with the population maxes in `gp_smooth_result_oblique.json`; either the table was generated from a different defense / different parameters, or there is a computation bug. The code in `uncertainty.py:95–127` definitively uses `per_cell_ell_ratios` and `per_pair_K_ratios` as its populations, so the K upper CI cannot exceed K_max=1.0501 and the ℓ upper CI cannot exceed ℓ_max=0.8649.)

**Caveat:** no persisted bootstrap JSON file exists (`grep -r bootstrap live_runs/.../*.json` returns empty); the paper cites `uncertainty.py` but the specific invocation/output artifact isn't checked into the repo. I cannot independently re-run the bootstrap (no Python execution in this audit session), so this audit flags the self-inconsistency only.

---

## 2. `continuous_sweep.tex` vs `continuous_sweep/sweep.json`

All four rows of the table correspond to row i of `sweep.json["rows"]`.

| Row | Col | Table | JSON | Status |
|---|---|---|---|---|
| SmoothNearestSafe | L | 23.62 | 23.625 | ✅ |
| SmoothNearestSafe | K | 3.162 | 3.16227766016838 | ✅ |
| SmoothNearestSafe | ℓ | 23.625 | 23.625 | ✅ |
| SmoothNearestSafe | ℓ(K+1) | 98.334 | 98.33380972147798 | ✅ |
| SmoothNearestSafe | G | 23.62 | 23.625 | ✅ |
| SmoothNearestSafe | trans | × | transversality_holds=false | ✅ |
| SmoothNearestSafe | \|S_p\| | 1 | predicted_persistent_count=1 | ✅ |
| SmoothNearestSafe | TP | 1 | true_positives=1 | ✅ |
| SmoothNearestSafe | FP_int | 0 | false_positives_interior=0 | ✅ |
| SmoothNearestSafe | \|S_a\| | 59 | actual_persistent_count=59 | ✅ |
| KernelSmoothed | L | 23.62 | 23.625 | ✅ |
| KernelSmoothed | K | 5.000 | 5.0 | ✅ |
| KernelSmoothed | ℓ | 21.750 | 21.75 | ✅ |
| KernelSmoothed | ℓ(K+1) | 130.500 | 130.5 | ✅ |
| KernelSmoothed | G | 23.62 | 23.625 | ✅ |
| KernelSmoothed | trans | × | false | ✅ |
| KernelSmoothed | \|S_p\| | 1 | 1 | ✅ |
| KernelSmoothed | TP | 1 | 1 | ✅ |
| KernelSmoothed | FP_int | 0 | 0 | ✅ |
| KernelSmoothed | \|S_a\| | 39 | 39 | ✅ |
| SoftProj | L | 23.62 | 23.625 | ✅ |
| SoftProj | K | 2.000 | 2.0 | ✅ |
| SoftProj | ℓ | 23.625 | 23.625 | ✅ |
| SoftProj | ℓ(K+1) | 70.875 | 70.875 | ✅ |
| SoftProj | G | 23.62 | 23.625 | ✅ |
| SoftProj | trans | × | false | ✅ |
| SoftProj | \|S_p\| | 1 | 1 | ✅ |
| SoftProj | TP | 0 | true_positives=0 | ✅ (sweep notes false_positives_boundary=1 for this row) |
| SoftProj | FP_int | 0 | false_positives_interior=0 | ✅ |
| SoftProj | \|S_a\| | 56 | 56 | ✅ |
| ObliqueGP | L | 23.62 | 23.625 | ✅ |
| ObliqueGP | K | 1.050 | 1.0501173326701811 | ✅ |
| ObliqueGP | ℓ | 0.274 | 0.2744662192846744 | ✅ |
| ObliqueGP | ℓ(K+1) | 0.563 | 0.5626879533879658 | ✅ (half-up; banker's would give 0.563 too since last digit even) |
| ObliqueGP | G | 23.62 | 23.625 | ✅ |
| ObliqueGP | trans | ✓ | true | ✅ |
| ObliqueGP | \|S_p\| | 46 | 46 | ✅ |
| ObliqueGP | TP | 46 | 46 | ✅ |
| ObliqueGP | FP_int | 0 | 0 | ✅ |
| ObliqueGP | \|S_a\| | 68 | 68 | ✅ |
| footnote dagger | ℓ=0.865, \|S_pred\|=3 | `gp_smooth_result_oblique.json`: ell_empirical=0.8648970604973426, predicted_persistent_count=3 | ✅ |

**Verdict:** ✅ all 40 data cells match.

---

## 3. `gp_sensitivity.tex` vs `sensitivity/sensitivity.json`

Nine rows covering RBF, Matérn-3/2, Matérn-5/2 kernels at σ ∈ {0.1, 0.2, 0.4}. I indexed `sensitivity.json["rows"]` in order.

| kernel / σ | L | K | ℓ | G | \|S_pred\| | TP | FP_int |
|---|---|---|---|---|---|---|---|
| RBF 0.10 | 23.62 / 23.625 ✅ | 1.105 / 1.105465953443332 ✅ | 0.884 / 0.883847142211191 ✅ | 23.62 ✅ | 9/9 ✅ | 9/9 ✅ | 0/0 ✅ |
| RBF 0.20 | 23.62 ✅ | 1.050 / 1.0501173326701811 ✅ | 0.274 / 0.2744662192846744 ✅ | 23.62 ✅ | 46/46 ✅ | 46/46 ✅ | 0/0 ✅ |
| RBF 0.40 | 23.62 ✅ | 1.037 / 1.0370189468959097 ✅ | 0.099 / 0.09878120751665288 ✅ | 23.62 ✅ | 71/71 ✅ | 71/71 ✅ | 0/0 ✅ |
| Matérn-3/2 0.10 | 23.62 ✅ | 1.068 / 1.0682282358873967 ✅ | 1.315 / 1.315383091735978 ✅ | 23.62 ✅ | 7/7 ✅ | 7/7 ✅ | 0/0 ✅ |
| Matérn-3/2 0.20 | 23.62 ✅ | 1.070 / 1.0695379674035728 ✅ | 1.165 / 1.164733740869552 ✅ | 23.62 ✅ | 8/8 ✅ | 8/8 ✅ | 0/0 ✅ |
| Matérn-3/2 0.40 | 23.62 ✅ | 1.070 / 1.0700075695850209 ✅ | 0.946 / 0.9455108671338216 ✅ | 23.62 ✅ | 8/8 ✅ | 8/8 ✅ | 0/0 ✅ |
| Matérn-5/2 0.10 | 23.62 ✅ | 1.079 / 1.0786030949971275 ✅ | 0.899 / 0.899240933957236 ✅ | 23.62 ✅ | 9/9 ✅ | 9/9 ✅ | 0/0 ✅ |
| Matérn-5/2 0.20 | 23.62 ✅ | 1.080 / 1.0797109127879343 ✅ | 0.734 / 0.7342524151237071 ✅ | 23.62 ✅ | 9/9 ✅ | 9/9 ✅ | 0/0 ✅ |
| Matérn-5/2 0.40 | 23.62 ✅ | 1.094 / 1.0941836904719293 ✅ | 0.345 / 0.34490241365768465 ✅ | 23.62 ✅ | 41/41 ✅ | 41/41 ✅ | 0/0 ✅ |

**Verdict:** ✅ all 63 data cells match.

---

## 4. `resolution.tex` vs `resolution/resolution.json`

Four rows (grid 13, 17, 21, 25).

| grid | filled | L | K | ℓ | G | \|S_pred\| | TP | FP_int |
|---|---|---|---|---|---|---|---|---|
| 13×13 | 25/25 ✅ | 11.960 / 11.959999999999999 ✅ | 1.048 / 1.0475942751119 ✅ | 0.629 / 0.6286168655040792 ✅ | 11.960 ✅ | 5/5 ✅ | 5/5 ✅ | 0/0 ✅ |
| 17×17 | 31/31 ✅ | 14.195 ✅ | 1.033 / 1.032703262482756 ✅ | 0.598 / 0.5975374960764299 ✅ | 14.195 ✅ | 5/5 ✅ | 5/5 ✅ | 0/0 ✅ |
| 21×21 | 52/52 ✅ | 19.845 / 19.845000000000002 ✅ | 1.064 / 1.0641746905990246 ✅ | 0.966 / 0.9659461496550775 ✅ | 19.845 ✅ | 6/6 ✅ | 6/6 ✅ | 0/0 ✅ |
| 25×25 | 82/82 ✅ | 23.625 ✅ | 1.051 / 1.050821399895546 ✅ | 0.865 / 0.8648970604973426 ✅ | 23.625 ✅ | 3/3 ✅ | 3/3 ✅ | 0/0 ✅ |

**Verdict:** ✅ all 36 data cells match.

---

## 5. `higher_dim_lipschitz.tex` vs `live_runs/higher_dim_lipschitz.json`

| Metric | L̂ | Ĝ | Status |
|---|---|---|---|
| 2D grid coordinates (normalized) | 22.680 | 22.680 | ✅ JSON: 22.68 / 22.68 |
| 768-d MPNet (pairwise-max normalized) | 17.926 | 17.926 | ✅ JSON: 17.926352837290132 |
| ratio footnote | L(hdim)/L(2d) = 0.790, G ratio = 0.790 | JSON: 0.790403564254415 / 0.790403564254415 | ✅ |

**Verdict:** ✅ all cells match.

Note: JSON also reports `hdim_raw` (un-normalized) L̂=Ĝ=12.397 — not cited in the table (table only uses the `pairwise-max normalized` variant, correctly labeled).

---

## 6. `seed_replication.tex` vs `result.json` (saturated) and `result.json` (replicate)

Note: the saturated row (`Saturated (canonical)`) uses the **smooth_nearest_safe** defense values, NOT the identity defense of the saturated run's `result.json`. The correct source for the canonical row is `continuous_sweep/sweep.json["rows"][0]` (the smooth_nearest_safe row), which shares the same 82-cell archive. The replicate row's `result.json` has `defense.name = "smooth_nearest_safe"` natively. This is consistent with the table's comment ("Both rows use the smooth_nearest_safe continuous defense").

| Row | Filled | L̂ | K̂ | ℓ̂ | Ĝ | trans. | \|S_pred\| | TP | FP_int | Status |
|---|---|---|---|---|---|---|---|---|---|---|
| Saturated (canonical) | 82 | 23.62 | 3.16 | 23.62 | 23.62 | × | 1 | 1 | 0 | ✅ from `continuous_sweep/sweep.json` row 0: L=23.625, K=3.16227, ell=23.625, G=23.625, transversality_holds=false, predicted_persistent_count=1, true_positives=1, false_positives_interior=0 |
| Replicate (independent) | 76 | 22.25 | 2.69 | 22.25 | 22.25 | × | 1 | 1 | 0 | ✅ from replicate `result.json`: coverage=0.1216 × 625 = 76 cells ✅; estimates.L=22.249999999999996 → 22.25 ✅; estimates.K=2.692582403567252 → 2.69 ✅; estimates.ell=22.249999999999996 → 22.25 ✅; estimates.G=22.249999999999996 → 22.25 ✅; theorem_6_2.transversality_condition_G_gt_ellKp1=false ✅; predicted_persistent_count=1 ✅; true_positives_count=1 ✅; false_positives_interior_count=0 ✅ |

**Verdict:** ✅ all 18 data cells match. The "saturated" row does not come from the saturated `result.json` directly (which runs identity defense) but from the continuous_sweep smooth_nearest_safe entry — consistent with the table comment. Caller should be aware that the audit instructions ("source: `result.json`") slightly mis-cite where the saturated values come from.

---

## 7. `three_target_sweep.tex` vs saturated + gpt4o-mini + gpt4o retargeted JSON

| Target | Cells | Peak AD | \|S_τ\| | \|U_τ\| | L | K | ℓ | G | \|S_pred\| | FP_int | Status |
|---|---|---|---|---|---|---|---|---|---|---|---|
| gpt-3.5-turbo-0125 | 82 ✅ | 1.00 ✅ (max f=1.0) | 16 ✅ (safe_count) | 66 ✅ (unsafe_count) | 23.62 ✅ | 3.16 ✅ (from continuous_sweep smooth_nearest_safe) | 23.62 ✅ | 23.62 ✅ | 1 ✅ | 0 ✅ | ✅ |
| gpt-4o-mini-2024-07-18 | 82 ✅ (13 safe + 24 unsafe + 45 at_threshold = 82) | 0.99 ✅ (max f=0.99) | 13 ✅ | 24 ✅ | 12.25 ✅ (L=12.25) | 4.94 ✅ (K=4.9396356…) | 4.02 ✅ (ell=4.0216698…) | 10.12 ⚠️ (JSON G=10.125; half-up rounding would give 10.13, banker's rounding gives 10.12; delta=0.005) | 0 ✅ | 0 ✅ | ⚠️ G rounding |
| gpt-4o-2024-08-06 | 82 ✅ (10+30+42=82) | 0.99 ✅ | 10 ✅ | 30 ✅ | 12.38 ✅ (L=12.375 → 12.38 rounds both ways) | 3.41 ✅ (K=3.4058772…) | 12.38 ✅ (ell=12.375) | 12.38 ✅ (G=12.375) | 0 ✅ | 0 ✅ | ✅ |

**Peak AD caveat.** The table labels "Peak AD" as 1.00 and 0.99 for the three targets. The underlying archive's max `f`-value matches these. However, the retargeted `f` is `judge(target_response)`; for gpt-4o-mini with at_threshold_count=45 ties at exactly 0.5, the "peak adversarial deviation" is 0.99 (a few prompts still get max judge score), matching the table.

**10.125 → 10.12 rounding note.** Python's `round(10.125, 2) = 10.12` (banker's rounding, round-half-to-even). If the convention is half-up, the displayed value should be 10.13. Delta: |10.12 − 10.125| = 0.005 (one ulp at 2 decimals). Flag but not consequential.

**Comment re-check.** Table comment asserts "at-tau band swells from 0 to ~42 as alignment tightens." Actual at_threshold_counts: canonical=0, gpt4o-mini=45, gpt4o=42. Average/"~42" is fair; the '~42' understates gpt4o-mini (45) but is near mid-range. Not a numeric error since the text uses "~".

**Verdict:** ✅ with one ⚠️ (rounding of 10.125 → 10.12 via banker's rather than half-up).

---

## 8. `independent_dataset.tex` vs saturated + gpt4o-mini retargeted

| Target | Cells | Peak AD | L | K | ℓ | G | \|S_pred\| | TP | FP_int | Transv | Status |
|---|---|---|---|---|---|---|---|---|---|---|---|
| gpt-3.5-turbo-0125 | 82 ✅ | 1.000 ✅ | 23.62 ✅ | 3.16 ✅ | 23.62 ✅ | 23.62 ✅ | 1 ✅ | 1 ✅ | 0 ✅ | × ✅ | ✅ |
| gpt-4o-mini-2024-07-18 | 82 ✅ | 0.990 ✅ | 12.25 ✅ | 4.94 ✅ | 4.02 ✅ | 10.12 ⚠️ (same 10.125 rounding) | 0 ✅ | 0 ✅ | 0 ✅ | × ✅ | ⚠️ same G rounding as three_target_sweep |

**Comment cross-check.** "|U_tau|=24 vs 66" ✅ (matches 24 for gpt4o-mini retargeted, 66 for canonical). "45 at-tau cells" ✅ (at_threshold_count=45 in gpt4o-mini retargeted JSON). "FP_int=0 holds under both targets" ✅. Both rows: Transv=× ✓ (transversality_condition_G_gt_ellKp1=false in both JSONs).

**Verdict:** ✅ with same ⚠️ G rounding from 10.125.

---

## Summary

| Table | Status | Notes |
|---|---|---|
| `ci.tex` | ❌ | GP-smooth oblique K upper CI 1.098 > K_max=1.0501 (impossible); ℓ_med 0.928 > ell_max=0.8649 (impossible); ℓ upper CI 1.760 = 2× population max (impossible). The identity rows report ℓ=[0.000,0.000] where code returns NaN (undocumented NaN→0 convention). No bootstrap JSON is persisted anywhere in the repo, so the table's values cannot be independently reproduced. |
| `continuous_sweep.tex` | ✅ | All 40 data cells + footnote match `continuous_sweep/sweep.json` (and footnote's per-cell estimator matches `gp_smooth_result_oblique.json`). |
| `gp_sensitivity.tex` | ✅ | All 63 data cells match `sensitivity/sensitivity.json`. |
| `resolution.tex` | ✅ | All 36 data cells match `resolution/resolution.json`. |
| `higher_dim_lipschitz.tex` | ✅ | All cells match `higher_dim_lipschitz.json`. |
| `seed_replication.tex` | ✅ | All 18 data cells match; caveat that the "Saturated (canonical)" row's values come from `continuous_sweep/sweep.json` (smooth_nearest_safe row), not from the saturated archive's `result.json` (which uses identity defense). Consistent with the table comment. |
| `three_target_sweep.tex` | ⚠️ | All cells match except `G=10.12` for gpt4o-mini (JSON 10.125 rounded by banker's rule instead of half-up; delta=0.005). |
| `independent_dataset.tex` | ⚠️ | Same `G=10.12 vs 10.125` banker's-rounding quirk; all other cells match. |

**Overall:** 6 of 8 tables are pristine. 2 tables carry a single-ulp rounding quirk on the 10.125 → 10.12 cell (consistent with Python default `round()`; harmless but worth flagging if the paper's stated convention is half-up). 1 table (`ci.tex`) contains at least three bootstrap-CI cells that are **mathematically inconsistent** with the cited JSON populations for the GP-smooth oblique defense.

**Recommendation for ci.tex.** Either (a) persist the bootstrap output as a JSON artifact (e.g., `live_runs/gpt35_turbo_t05_saturated/bootstrap_ci.json`) so the table is reproducible from disk, or (b) re-run `uncertainty.bootstrap_estimator_cis` on the saturated heatmap with the oblique GP defense and update the table rows whose upper CI currently exceeds the empirical max. The population-max constraint ensures any correct bootstrap CI satisfies `ci_upper ≤ population_max`; the current K CI `[1.027, 1.098]` and ℓ CI `[0.629, 1.760]` violate this.
