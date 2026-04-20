# Audit 8 — Judge Robustness + Committee Appendices

Agent 8 of 10. READ-ONLY. Scope: `paper2_v3.tex` judge-robustness and
committee appendices (Sec. "Judge robustness" around line 2051–2134),
tables `tables/judge_robustness.tex` and `tables/judge_committee.tex`,
figure `figures/judge_scatter.pdf`, and its generator
`trilemma_validator/scripts/make_fig_judge_scatter_real.py`.

## Data sources inspected

- `/Users/mbhatt/stuff/trilemma_validator/live_runs/judge_robustness_deltas.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/judge_robustness_report.md`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/judge_committee/summary.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/judge_committee/top3_validate.json/result.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/continuous_sweep/sweep.json`
  (canonical smooth_nearest_safe: TP=1, FP_int=0)
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_judge_gpt4o/validate_gp.json/result.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_judge_gpt41_mini/validate_gp.json/result.json`
- `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_judge_gpt4o_mini/validate_gp.json/result.json`
- `/Users/mbhatt/stuff/tables/judge_robustness.tex`, `tables/judge_committee.tex`
- `/Users/mbhatt/stuff/figures/judge_scatter.pdf`
- `/Users/mbhatt/stuff/trilemma_validator/scripts/make_fig_judge_scatter_real.py`
- `/Users/mbhatt/stuff/trilemma_validator/scripts/judge_committee.py`

---

## Claim 1 — Per-judge |S_τ| / |U_τ|

Source: `judge_robustness_deltas.json → per_judge[*]`. Table renders each row:

| Judge | Paper | Data (`safe`, `unsafe`) | Verdict |
|---|---|---|---|
| gpt-4.1 canonical     | 16 / 66 | safe=16, unsafe=66 | OK |
| gpt-4o                | 10 / 72 | safe=10, unsafe=72 | OK |
| gpt-4.1-mini          | 33 / 49 | safe=33, unsafe=49 | OK |
| gpt-4o-mini           | 0 / 82  | safe=0,  unsafe=82 | OK |

All four rows in `tables/judge_robustness.tex` (lines 10–13) match the
per-judge JSON fields exactly. n_cells = 82 (JSON), 82 cells total
(paper caption, line 2068). Verdict: PASS.

---

## Claim 2 — Pairwise Pearson r / Cohen κ vs canonical

Source: `judge_robustness_deltas.json → pairwise_vs_canonical`.

| Judge | Paper r / κ | Data r / κ | Verdict |
|---|---|---|---|
| gpt-4o        | 0.546 / 0.457 | 0.5463808781950465 / 0.45695364238410596 | OK |
| gpt-4.1-mini  | 0.493 / 0.363 | 0.4927705335252643 / 0.3632680621201889  | OK |
| gpt-4o-mini   | 0.393 / 0.000 | 0.3928438189854645 / 0.0                 | OK |

Paper table (`tables/judge_robustness.tex`) uses 3-decimal rounding;
all three pairwise rows match the stored values. Verdict: PASS.

---

## Claim 3 — Kendall's W across 4 judges = 0.70

Source: `judge_robustness_deltas.json → "kendall_w": 0.7000522414862703`.

- `tables/judge_robustness.tex` line 16: "% Kendall's W across 4 judges: 0.700"
- `paper2_v3.tex` line 2073: "Kendall's $W=0.700$"
- `paper2_v3.tex` line 2086: "Kendall's $W = 0.700$"
- `paper2_v3.tex` line 2108: "Kendall's $W=0.70$"

All rounding forms consistent with the stored value 0.7000522.
Verdict: PASS.

---

## Claim 4 — TP / FP_int per judge under smooth_nearest_safe

| Judge | Paper | Source | TP / FP_int | Verdict |
|---|---|---|---|---|
| gpt-4.1 canonical | 1 / 0   | `gpt35_turbo_t05_saturated/continuous_sweep/sweep.json` (smooth_nearest_safe row, lines 20–22) | 1 / 0 | OK |
| gpt-4o            | 1 / 0   | `..._judge_gpt4o/validate_gp.json/result.json` (defense=smooth_nearest_safe, theorem_6_2: TP=1, FP_int=0) | 1 / 0 | OK |
| gpt-4.1-mini      | 1 / 0   | `..._judge_gpt41_mini/validate_gp.json/result.json` (TP=1, FP_int=0) | 1 / 0 | OK |
| gpt-4o-mini       | -- / -- | `..._judge_gpt4o_mini/validate_gp.json/result.json` (applicable=false, TP=0, FP_int=0; safe=0) | applicable=false, table correctly marks as "--" | OK |

Note: gpt-4o-mini's validator run still reports FP_int=0 (no
counterexample produced), which matches the paper's claim (line 2105):
"Crucially, FP_int=0 still holds: no counterexample to the theorem is
produced under any of the four judges." The `--` in the TP/FP_int
columns reflects non-testability (no safe cell → no anchor z*), not a
missing run. Verdict: PASS.

---

## Claim 5 — Committee safe/unsafe splits + mean Δ vs canonical

Source: `judge_committee/summary.json`.

| Committee | Paper | Data | Verdict |
|---|---|---|---|
| all-4                | 5 / 77, Δ=+0.058 | safe=5, unsafe=77, mean_delta_vs_canonical=0.05836890 | OK |
| top-3                | 17 / 65, Δ=+0.010 | safe=17, unsafe=65, mean_delta_vs_canonical=0.00956300 | OK |
| gpt4_family          | 13 / 69, Δ=+0.063 | safe=13, unsafe=69, mean_delta_vs_canonical=0.06329268 | OK |
| canonical (gpt-4.1)  | 16 / 66, Δ=0.000 | (baseline)        | OK |

`tables/judge_committee.tex` rows 11–14 match summary.json exactly
(3-decimal rounding for Δ, matches stored values). Verdict: PASS.

---

## Claim 6 — Top-3 committee validator: FP_int = 0

Source: `judge_committee/top3_validate.json/result.json`.

- `"false_positives_interior_count": 0` (line 76)
- `"false_positives_boundary_count": 0` (line 77)
- `"true_positives_count": 1` (line 74)
- `defense.name = "smooth_nearest_safe"` (line 13)
- `safe_count=17, unsafe_count=65` (matches summary.json top-3 row)
- `theorem_violated: false`, `fraction_within_bound: 1.0`

Paper (line 2122) "FP_int = 0 under smooth_nearest_safe ... top-3
committee ... within one cell of canonical (17 safe vs 16; mean
Δ=+0.010)". Verdict: PASS.

Caveat (minor ⚠): the committee-level validator was only run for the
top-3 configuration. FP_int=0 for all-4 and gpt4_family rows of
`tables/judge_committee.tex` is claimed without an equivalent
`*_validate.json/` artifact in `judge_committee/`. The canonical
single-judge baseline's FP_int=0 is independently confirmed via the
continuous_sweep output. If the caller needs strict reproducibility
for the all-4 and gpt4_family FP_int=0 entries, those validator runs
are not present in the live_runs tree; only the aggregated archives
(`all4_archive.json`, `gpt4_family_archive.json`) are. Paper text
(line 2122) says "FP_int=0 under smooth_nearest_safe on every
committee configuration" — this is supported by the table but only the
top-3 and canonical rows are directly validator-backed.

---

## Claim 7 — judge_scatter figure generator has NO synthetic data

Source: `trilemma_validator/scripts/make_fig_judge_scatter_real.py`.

- Grep for `np.random` → 0 matches in code body (the string
  "synthetic" appears only in the docstring phrase "no synthetic data").
- The script reads four real archive files at hard-coded absolute
  paths (lines 20–25), all four of which exist and contain `cells`
  with `grid_position` and `quality` fields:
  - `gpt35_turbo_t05_saturated/source_archive.json`
  - `gpt35_turbo_t05_judge_gpt4o/source_archive.json`
  - `gpt35_turbo_t05_judge_gpt41_mini/source_archive.json`
  - `gpt35_turbo_t05_judge_gpt4o_mini/source_archive.json`
- Extraction (line 31): `float(c["quality"])` per cell — raw judge
  scores; no perturbation.
- Pearson r (line 72) computed from `np.corrcoef` on real scores.
- Output (line 97): `/Users/mbhatt/stuff/figures/judge_scatter.pdf`
  (exists, 27,420 bytes).

Verdict: PASS. The "real" designation is honest.

---

## Summary table

| # | Claim | Verdict |
|---|---|---|
| 1 | Per-judge |S_τ|/|U_τ| (16/66, 10/72, 33/49, 0/82)              | PASS |
| 2 | Pearson r / κ vs canonical (0.546/0.457, 0.493/0.363, 0.393/0.0) | PASS |
| 3 | Kendall's W = 0.70 (0.7000522)                                  | PASS |
| 4 | TP/FP_int per judge (1/0, 1/0, 1/0, --/--)                      | PASS |
| 5 | Committee safe/unsafe + mean Δ (5/77+0.058, 17/65+0.010, 13/69+0.063) | PASS |
| 6 | Top-3 committee FP_int = 0                                      | PASS |
| 7 | Scatter figure regenerated from real archives, no np.random     | PASS |

## Minor notes

- The TP/FP_int columns in `tables/judge_robustness.tex` come from
  per-archive validator runs under `smooth_nearest_safe`; for
  gpt-4o-mini the validator reports `applicable=false` so the table
  renders `--`, which the paper narrative (line 2103–2106) correctly
  explains.
- `FP_int=0` is claimed for all four committee configs in
  `tables/judge_committee.tex` (lines 11–14). Only the `top-3` row is
  backed by a dedicated `top3_validate.json/result.json`; the
  `canonical` row is backed by the saturated-archive continuous_sweep
  output. The `all-4` and `gpt4_family` rows would need equivalent
  `all4_validate.json/` and `gpt4_family_validate.json/` artifacts to
  be independently verifiable from files; the aggregated archives
  exist (`all4_archive.json`, `gpt4_family_archive.json`) but the
  validator outputs on those aggregated surfaces are not present in
  `trilemma_validator/live_runs/judge_committee/`. This is a
  reproducibility gap, not a contradiction — but a caller who wants
  strict verification of those two FP_int=0 cells should add those
  runs. ⚠️ (minor)
- Paper text is internally consistent: κ=0 for gpt-4o-mini (line 2108)
  is a known consequence of that judge flagging every cell unsafe
  (safe_count=0 → degenerate 2×2 contingency → κ=0).

Overall verdict: all seven specific claims are verified against the
underlying JSON / code. One minor reproducibility gap noted for two of
four committee rows where FP_int=0 is asserted in the table without a
corresponding validator directory in the live_runs tree.
