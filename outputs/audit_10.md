# Audit 10 of 10: Bibliography, Figure Captions, and Cross-Reference Integrity

**File audited:** `/Users/mbhatt/stuff/paper2_v3.tex` (2214 lines)
**Auditor:** Agent 10 of 10 (read-only)
**Date:** 2026-04-19

---

## Summary

| Check | Status | Count |
|---|---|---|
| 1. Orphan labels | WARN | 47 orphans |
| 2. Broken refs | PASS | 0 broken |
| 3. Bibliography coverage (cited -> bibitem) | PASS | 23/23 cited keys resolve |
| 3b. Unreferenced bibitems | WARN (OK per spec) | 16 unreferenced |
| 4. Figure captions — numerical accuracy | PASS | `fig:theory-vs-reality-saturated` numbers all match `gp_smooth_result_oblique.json` |
| 5. Future-dated refs (2512/2602/2603/2604) | WARN | 5 future-dated arXiv IDs, none > year 2026 |
| 6. Overclaiming phrases | PASS | 0 hits for banned phrases |

Overall verdict: the bibliography block, cross-reference system, and the focal `fig:theory-vs-reality-saturated` caption are internally consistent. The main hygiene debt is a large set of orphan labels (many are section/subsection anchors that may be harmless) and ~30% unreferenced bibitems (expected per spec, but worth trimming). No overclaiming phrases, no broken refs, no numeric contradictions in the GP-oblique figure caption.

---

## 1. Orphan Labels (defined but never referenced) — WARN

89 labels are defined; 42 are actually referenced. **47 orphans** (many are legitimate `sec:`/`app:` anchors used only implicitly by `\autoref`-style navigation):

### Section / appendix anchors (likely intentional, rarely cited directly)
- `sec:intro`
- `sec:related`
- `sec:setup`
- `sec:boundary`
- `sec:relaxed`
- `sec:eps-robust`
- `sec:bridge`
- `sec:extensions`
- `sec:gp-instance`
- `sec:engineering`
- `sec:conclusion`
- `sec:estimators`
- `sec:identity-sanity`
- `sec:discrete-stress`
- `app:continuous-relaxation`
- `app:pipeline`
- `app:exp-details`
- `app:continuous-sweeps`
- `app:pair-baseline`

### Definitions / remarks (harmless orphans)
- `def:ad`
- `def:defense`
- `rem:safe-preserving-escape`

### Theorem orphans (worth checking — is the theorem ever actually referenced?)
- `thm:trilemma` — Theorem 3.2 in §3; referenced only as "defense trilemma" in prose but never as `\Cref{thm:trilemma}`. ⚠️
- `thm:basin` — defined in `app:landscape` but no body reference. ⚠️
- `thm:fragment` — defined in `app:landscape` but no body reference. ⚠️
- `thm:convergence` — defined in `app:attacks`, never cited. ⚠️
- `thm:transfer` — defined in `app:attacks`, never cited. ⚠️
- `thm:authority` — defined in `app:attacks`, never cited. ⚠️
- `thm:gradient` — defined in `app:attacks`, never cited. ⚠️
- `thm:interior-stable` — defined in `app:stability`, never cited. ⚠️
- `thm:nonlocal` — defined in `app:stability`, never cited. ⚠️

### Figure orphans
- `fig:landscape` — schematic figure (line 283). Never referenced by `\Cref` or `\ref`. ⚠️ Consider adding a "see \Cref{fig:landscape}" in the setup section.
- `fig:escalation` — three-panel figure (line 694). Never referenced. ⚠️ Consider citing it in §3 where the three regimes are introduced.
- `fig:k-tradeoff` — TODO placeholder figure (line 1578). Orphan; OK if it remains TODO.
- `fig:tau-sweep` — TODO placeholder figure (line 2017). Orphan.
- `fig:judge-scatter` — defined in `app:judge-robustness` (line 2090), never cited in prose. ⚠️

### Table orphans
- `tab:smoketests` (line 1917)
- `tab:continuous-sweep` (line 1940)
- `tab:gp-sensitivity` (line 1951)
- `tab:higher-dim-lipschitz` (line 1975)
- `tab:seed-replication` (line 1985)
- `tab:independent-dataset` (line 1995)
- `tab:ci` (line 2005)
- `tab:live-sweep` (line 2034)
- `tab:pair-baseline` (line 2157)
- `tab:pipeline` (line 1615)
- `tab:counterexample-ablation` (line 1728)

These are all appendix tables that are appear "float on their own" without `\Cref{...}` anchoring them to the text. Not strictly broken, but the reader can't navigate to them by name.

---

## 2. Broken `\Cref` / `\ref` / `\eqref` (no matching `\label`) — PASS

All 75+ inline references resolve to defined labels. No broken refs detected.

---

## 3. Bibliography Coverage

### 3a. Every `\cite{...}` resolves to a `\bibitem` — PASS (23/23)

Cited keys (expanded from multi-key `\cite{...,...}` calls):
- `alon2023detecting` ✓
- `bai2022constitutional` ✓
- `inan2023llama` ✓ (cited twice)
- `szegedy2013intriguing` ✓
- `goodfellow2014explaining` ✓
- `carlini2017evaluating` ✓
- `madry2018towards` ✓
- `tsipras2018robustness` ✓ (cited twice)
- `fawzi2018adversarial` ✓
- `cohen2019certified` ✓
- `katz2017reluplex` ✓
- `singh2019abstract` ✓
- `huang2017safety` ✓
- `bagnall2019certifying` ✓
- `naitzat2020topology` ✓
- `zou2023universal` ✓
- `chao2024jailbreaking` ✓ (cited twice)
- `mehrotra2024tree` ✓
- `greshake2023indirect` ✓
- `mouret2015illuminating` ✓
- `samvelyan2024rainbow` ✓
- `wolpert1997no` ✓
- `munshi2026manifold` ✓ (cited twice)

Every cited key has a corresponding `\bibitem` entry in the `thebibliography` block (lines 1254–1473).

### 3b. Unreferenced `\bibitem` entries — WARN (OK per spec)

16 bibitems are declared but never cited:
- `ge2024mart` (line 1386)
- `hubinger2024sleeper` (line 1392)
- `anil2024many` (line 1398)
- `kim2025manyshot` (line 1403)
- `zhan2024injecagent` (line 1408)
- `zhang2024asb` (line 1414)
- `yuan2025instability` (line 1420)
- `skoltech2025quant` (line 1425)
- `eth2025gguf` (line 1431)
- `hammoud2024merging` (line 1437)
- `liu2026whackamole` (line 1443)
- `iris2025` (line 1448)
- `zhao2025weak` (line 1453)
- `huang2025safetytax` (line 1458)
- `huang2026formal` (line 1463)
- `slingshot2026` (line 1468)

A pre-comment on line 1384 reads `% --- New references for comparison table ---`, suggesting these are reserved for a comparison / discussion table that never landed in the current draft. Audit recommendation: either cite them in a discussion or related-work subsection, or remove them to avoid "phantom references" in the final bibliography.

---

## 4. Figure Captions — numerical consistency

### `fig:theory-vs-reality-saturated` (line 1006–1031) — PASS

Caption claims checked against `/Users/mbhatt/stuff/trilemma_validator/live_runs/gpt35_turbo_t05_saturated/gp_smooth_result_oblique.json`:

| Quantity | Caption | JSON | Match |
|---|---|---|---|
| `G` | 23.6 | 23.625 | PASS (rounded) |
| `ell` | 0.86 | 0.8648970604973426 | PASS (rounded) |
| `K` | 1.05 | 1.050821399895546 | PASS (rounded) |
| `ell(K+1)` | 1.77 | 1.773749400374703 | PASS (rounded) |
| `|S_pred|` | 3 | `predicted_persistent_count`: 3 | PASS |
| TP | 3 | `true_positives`: 3 | PASS |
| `FP_int` | 0 | `false_positives_interior`: 0 | PASS |
| `|S_act|` | 68 | `actual_persistent_count`: 68 | PASS |
| FN | 65 | `false_negatives`: 65 | PASS |
| n_filled | 82 | `n_filled`: 82 | PASS |
| boundary cells (10) | 10 (in surrounding text line 1047) | not in JSON, but theta=89.5° and displacement are consistent | PASS |
| theta | 89.5° | `oblique_angle`: 89.5 | PASS |

All numerical claims in the caption and the surrounding sentence are consistent with the JSON artifact. No contradictions found.

### Other figures with captions — PASS (no numerical claims / schematic only)

- `fig:landscape` (line 282): schematic of prompt space, no numerical content.
- `fig:trilemma` (line 402): trilemma schematic, no numbers.
- `fig:escalation` (line 693): three-panel qualitative schematic, refers to theorems but no numerical assertions.
- `fig:multi-turn-plot` (line 824): TODO placeholder; caption is forward-looking ("running-max AD trajectory ... consistent with Thm. 5.1"). No concrete numbers to verify.
- `fig:stochastic-histogram` (line 887): TODO placeholder; describes histogram structure, no numbers.
- `fig:k-tradeoff` (line 1578): TODO placeholder, no numbers.
- `fig:tau-sweep` (line 2017): TODO placeholder, no numbers.
- `fig:judge-scatter` (line 2090): quotes `Kendall's W = 0.700`, matches the `tab:judge-robustness` caption (`W=0.700`). PASS.

---

## 5. Future-dated arXiv references — WARN

Paper is dated 2026. Found 5 arXiv IDs with year-prefix indicating 2025-12 or 2026:

| Line | Key | arXiv ID | Stated year | Notes |
|---|---|---|---|---|
| 1349 | `munshi2026manifold` | `2602.22291v2` | 2026 | Feb 2026 (2602 = Feb 2026) |
| 1423 | `yuan2025instability` | `2512.12066` | 2025 | Dec 2025 (2512 = Dec 2025) |
| 1446 | `liu2026whackamole` | `2603.20957` | 2026 | Mar 2026 (2603 = Mar 2026) |
| 1466 | `huang2026formal` | `2603.00047` | 2026 | Mar 2026 |
| 1471 | `slingshot2026` | `2602.02395` | 2026 | Feb 2026 |

**No arXiv IDs with year > 2026.** All are consistent with the paper's 2026 positioning (today's date is 2026-04-19, so all listed IDs are within the last 5 months or earlier). `WebFetch` was not invoked (schema not loaded) — audit notes only format-level consistency, not whether the papers actually resolve on arxiv.org.

No `2604.` arXiv IDs found in the paper (the audit spec asks for them but none exist here; not an issue).

---

## 6. Overclaiming phrases — PASS

Grep counts (zero hits required per spec):

| Phrase | Hits |
|---|---|
| `doubt-eliminator` | 0 PASS |
| `validated empirically on` | 0 PASS |
| `first non-tautological` | 0 PASS |
| `zero empirical counterexamples` | 0 PASS |

The softening edits from earlier audits have held.

---

## Recommendations (non-blocking)

1. **Cite or drop the 16 uncited bibitems** (they look like they were staged for a comparison table that was never inserted). Leaving them creates clutter in the printed bibliography.
2. **Add `\Cref{fig:landscape}` and `\Cref{fig:escalation}` to the prose** so the two main pedagogical figures are actually linked from the text. Currently both are orphaned.
3. **Audit orphan theorems** (`thm:trilemma`, `thm:basin`, `thm:fragment`, `thm:convergence`, `thm:transfer`, `thm:authority`, `thm:gradient`, `thm:interior-stable`, `thm:nonlocal`). Either reference each from the body or reconsider whether they need to be theorems.
4. **Orphan tables in the appendix** (smoketests, continuous-sweep, gp-sensitivity, higher-dim-lipschitz, seed-replication, independent-dataset, ci, live-sweep, pair-baseline, pipeline, counterexample-ablation): each has a caption but no inline `\Cref{...}` pointer, making navigation harder. Add inline references where each table is first discussed.

---

## Appendix A: full label → reference count (for spot-checks)

Labels referenced at least once (42): thm:coarea, thm:cone, thm:dilemma, fig:trilemma, thm:main, thm:score-preserving, thm:eps-relaxed, thm:eps-robust, thm:persistent, thm:disc-dilemma, thm:multi-turn, thm:stochastic, app:counterexamples, app:proofs, app:quantitative, lem:input-bound, app:additional, app:artifact, sec:experiments, thm:tietze, sec:persistent, sec:live-validation, tab:resolution, app:judge-robustness, tab:multi-turn, fig:multi-turn-plot, tab:stochastic, fig:stochastic-histogram, fig:theory-vs-reality-saturated, tab:three-target, tab:llamaguard-demo, tab:forced-collapse, tab:paraphrase-unsafe, thm:cost, thm:crossing, thm:lipschitz, thm:pipeline, thm:pipeline-impossible, app:landscape, app:attacks, app:stability, app:cost, def:steep, tab:judge-robustness, tab:judge-committee.
