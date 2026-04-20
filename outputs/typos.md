# Typo and consistency audit — paper2_v2.tex (and siblings)

Audited files:
- `/Users/mbhatt/stuff/paper2_v2.tex`              (2148 lines)
- `/Users/mbhatt/stuff/paper2_neurips.tex`         (1732 lines)
- `/Users/mbhatt/stuff/overleaf_package/paper2_v2.tex`      (1925 lines)
- `/Users/mbhatt/stuff/overleaf_package/paper2_neurips.tex` (1683 lines)

Lean artifact at `/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs/` (45 files in subdir) + 1 root `ManifoldProofs.lean` → 46 total files, matching paper claim.

---

## Category 1: Typos (apply verbatim)

### 1.1 Ligature / hex-corruption hunt
- No hits for `6rreservation`, `6reservation`, `6resser`, `6rese`, `f(K+1)` (OCR artifact) in any of the four tex files. The broken-OCR "f(K+1)" seen in the professor's copy does NOT appear here — all instances are correctly `\ell(K+1)`. No fixes needed.

### 1.2 Malformed LaTeX macros — `\providecommand` with `{}` in name
File: `/Users/mbhatt/stuff/paper2_neurips.tex`
- [ ] Line 1031: `\providecommand{\BootstrapL{}}{TODO}` → `\providecommand{\BootstrapL}{TODO}`
- [ ] Line 1032: `\providecommand{\BootstrapK{}}{TODO}` → `\providecommand{\BootstrapK}{TODO}`
- [ ] Line 1033: `\providecommand{\BootstrapEll{}}{TODO}` → `\providecommand{\BootstrapEll}{TODO}`
- [ ] Line 1034: `\providecommand{\BootstrapG{}}{TODO}` → `\providecommand{\BootstrapG}{TODO}`

These are syntactically invalid: `\providecommand` expects a macro name without `{}` suffix. Currently these define a macro named `\BootstrapL` whose argument-count spec is `{}` (mis-parsed) — LaTeX will silently accept and produce odd results at any `\BootstrapL` usage. Fix by deleting the empty-braces before the replacement text.

### 1.3 Double spaces — none found in prose
Only hit: table cell alignment in Table 7 (saturated results row, e.g. line 1482 in paper2_v2.tex) where the `identity` row uses spaces for column alignment. Intentional — leave as is.

---

## Category 2: Broken cross-references

### paper2_v2.tex
No broken `\ref` / `\Cref`. (`\ref` targets all have matching `\label`.)

Orphan labels (defined but never referenced; low priority, mostly section anchors that are reasonable as external-citation anchors):
- `app:additional`, `def:ad`, `def:defense`, `fig:landscape`, `fig:theory-vs-reality-saturated`, `prop:transversality`, `rem:safe-preserving-escape`, `sec:boundary`, `sec:bridge`, `sec:conclusion`, `sec:discrete-stress`, `sec:eps-robust`, `sec:extensions`, `sec:gp-instance`, `sec:identity-sanity`, `sec:intro`, `sec:limitations`, `sec:quantitative`, `sec:related`, `sec:relaxed`, `sec:setup`, `tab:bootstrap-CI`, `tab:sparse-smoke-tests`, `thm:disc-ivt`, `thm:gradient`, `thm:nonlocal`, `thm:pipeline-impossible`, `thm:trilemma`
- Of these, `fig:theory-vs-reality-saturated` is Figure 4 itself — it is **not** `\Cref`'d anywhere in paper2_v2.tex; the main caller line only says "We present Figure~4" rather than `\Cref{fig:theory-vs-reality-saturated}`. Consider adding a `\Cref{fig:theory-vs-reality-saturated}` reference in Sec. 10.2 prose (line ~1321) for consistency with `\Cref{fig:trilemma}`/`\Cref{fig:escalation}` style.

### paper2_neurips.tex — **broken refs** (these will print `??` in the PDF)
- [ ] Line 1042: `\Cref{sec:estimators}` — no matching `\label{sec:estimators}` in this file (the label exists only in `paper2_v2.tex` line 1246). Either:
  - (a) add `\label{sec:estimators}` to the relevant subsection in `paper2_neurips.tex`, or
  - (b) replace the cref with inline description, or
  - (c) cut the forward reference.
- [ ] Line 1082: `\Cref{app:sparse-smoke-tests}` — label exists only in `paper2_v2.tex` line 2058/2074. Same fix options.
- [ ] Line 1086: `\Cref{app:judge-robustness}` — label exists only in `paper2_v2.tex` line 2117. Same fix options.

All three are self-contained to the NeurIPS short version; the `overleaf_package/paper2_neurips.tex` mirrors this loose version but no longer cites these labels, so those are clean.

### overleaf_package/paper2_v2.tex and overleaf_package/paper2_neurips.tex
No broken refs.

---

## Category 3: Lean references

Every Lean name cited by the paper resolves to an actual definition in `/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs/`.

Verified existing:
- `MoF_11_EpsilonRobust` — file present (`MoF_11_EpsilonRobust.lean`).
- `MoF_12_Discrete`, `MoF_15_NonlinearAgents`, `MoF_17_CoareaBound`, `MoF_18_ConeBound`, `MoF_19_OptimalDefense`, `MoF_20_RefinedPersistence`, `MoF_21_GradientChain` — all present.
- `shallow_boundary_no_persistence` — theorem in `MoF_19_OptimalDefense.lean:175`.
- `gradient_norm_implies_steep_nonempty` — theorem in `MoF_21_GradientChain.lean:166`.
- `optimal_K_exists` — theorem in `MoF_19_OptimalDefense.lean:97`.
- `running_max_monotone` — theorem in `MoF_13_MultiTurn.lean:270`.
- `transversality_reachable` — theorem in `MoF_13_MultiTurn.lean:345`.
- `persistent_unsafe_refined` — theorem in `MoF_20_RefinedPersistence.lean:124`.

No paper-cited Lean name is missing from the Lean source. **Category 3: clean.**

---

## Category 4: Math consistency

### 4.1 Threshold τ
All instances in paper2_v2.tex are `\tau` (math mode), including appendix. Zero occurrences of `\Tau`, bare `tau`, stray `t` or `T` used as threshold. **Clean.**

### 4.2 `\ell` vs `L`
Every place that should say `\ell(K+1)` does — see all 22 matches. No place uses `L(K+1)` where the paper's text talks about the defense-path Lipschitz constant. The `L` (global Lipschitz) vs `\ell` (defense-path Lipschitz) distinction is preserved throughout Sections 5–6 and appendix.
No `f(K+1)` bad-OCR substrings anywhere. **Clean.**

### 4.3 Equation / theorem numbering (paper2_v2.tex)
Counter shared across `theorem|lemma|corollary|proposition|definition|remark`, reset per section. Manual enumeration:
- Sec 4 (Boundary Fixation): 4.1 Thm Boundary Fixation (`thm:main`); 4.2 Thm Defense Trilemma (`thm:trilemma`); 4.3 Rem; 4.4 Thm Score-Preserving (`thm:score-preserving`); 4.5 Thm ε-Relaxed (`thm:eps-relaxed`); 4.6 Rem. → **4.1, 4.4, 4.5 match expected.**
- Sec 5 (ε-Robust): 5.1 Thm ε-Robust (`thm:eps-robust`); 5.2 Thm ε-Band (`thm:band-measure`); 5.3 Rem. → **5.1, 5.2 match.**
- Sec 6 (Persistent Unsafe): 6.1 Lem Input-Relative Bound (`lem:input-bound`); 6.2 Def Steep region (`def:steep`); 6.3 Thm Persistent Unsafe Region (`thm:persistent`); 6.4 Prop Transversality (`prop:transversality`). → **6.3 matches.**
- Sec 7 (Quantitative Bounds): 7.1 `thm:coarea`; 7.2 `thm:cone`; 7.3 `thm:dilemma`. → **Match.**
- Sec 8 (Discrete): 8.1 Continuous Relaxation; 8.2 Discrete IVT (`thm:disc-ivt`); 8.3 Discrete Defense Dilemma. → **Match.**
- Sec 9 (Extensions): 9.1 Multi-Turn; 9.2 Stochastic; 9.3 Pipeline Lipschitz; 9.4 Pipeline Impossibility (`thm:pipeline-impossible`). → **Match.**

All theorem numbers are correct.

### 4.4 "Theorem 6.1" → "Lemma 6.1" confusion
In `paper2_v2.tex`, Section 6's proof sketch at line 672 uses `\Cref{lem:input-bound}`, which `cleveref` renders as "Lemma 6.1". No hand-written "Theorem 6.1" string exists in the file (grep for `Theorem 6\.1` and `Theorem~6\.1`: 0 hits). **Clean** — the professor's OCR artifact is not in the source.

### 4.5 `\ell` in figure 4 caption
Figure 4 caption (paper2_v2.tex lines 1330–1350) uses `\hat\ell = 0.86`, `\hat K = 1.05`, `\hat\ell(\hat K{+}1) = 1.77`, `\hat G = 23.6`, `|\mathcal{S}_{\text{pred}}| = 3`, `|\mathcal{S}_{\text{act}}| = 68`. These match the text on lines 1319–1323 and the expected values in the prompt (`ℓ=0.86, K=1.05, ℓ(K+1)=1.77, G=23.6, |Ssteep|=3, |Sact|=68, TP=3, FP_int=0`).

Note: the prompt refers to "Ssteep" but the paper uses `\mathcal{S}_{\text{pred}}` symbolically, with textual label "steep set". That is internally consistent (Def 6.2 "Steep region" = `\mathcal{S}` = predicted). No action required.

---

## Category 5: Figure 4 caption numbers — consistency

Figure 4 caption (paper2_v2.tex lines 1330–1350) vs body text (lines 1316–1323):

| Quantity               | Caption value | Body-text value | Prompt expected | Status |
|------------------------|---------------|-----------------|------------------|--------|
| θ (GP oblique angle)   | 89.5°         | 89.5°           | —                | OK     |
| $\hat\ell$             | 0.86          | 0.86            | 0.86             | OK     |
| $\hat K$               | 1.05          | 1.05            | 1.05             | OK     |
| $\hat\ell(\hat K{+}1)$ | 1.77          | 1.77            | 1.77             | OK     |
| $\hat G$               | 23.6          | 23.6            | 23.6             | OK     |
| `|S_pred|`             | 3             | 3               | 3                | OK     |
| `|S_act|`              | 68            | 68              | 68               | OK     |
| TP                     | (implicit "all predicted ... persistent")  | 3 | 3 | OK |
| FP_int                 | not in caption | 0              | 0                | OK (body) |
| FN                     | 65            | not in body     | —                | OK (caption) |
| filled cells           | 82            | 82              | —                | OK     |
| τ                      | 0.5           | 0.5             | —                | OK     |

**All values in Figure 4 caption are consistent** with the surrounding text and the prompt spec. One polish note: the caption does not explicitly state TP=3 and FP_int=0 — it says "The predicted three cells are all actually persistent" (implies TP=3) — when Agent 4 regenerates the figure, consider adding "(TP=3, FP_int=0)" inside the caption for unambiguous alignment with Table 7 (`tab:continuous-sweep` and `tab:gp-sensitivity`).

---

## Category 6: Bibliography

### 6.1 Venue capitalization
Scanned all `\bibitem` entries in paper2_v2.tex. Venues used: ICLR, ICML, AAAI, CAV, POPL, IEEE S&P, NAACL, ACL, AISec, NeurIPS (written as "Advances in Neural Information Processing Systems"), Findings of ACL, Findings of EMNLP, JMLR ("Journal of Machine Learning Research"). Capitalization is uniform (no "Iclr"/"Icml"/"Neurips" lowercase variants). **Clean.**

### 6.2 arXiv IDs
Dated April 2026 → up to `2604.xxxxx` is natural. Scan of all arXiv IDs in paper2_v2.tex bibliography:
- `arXiv:2308.14132` (alon2023detecting, 2023) — ok
- `arXiv:2212.08073` (bai2022constitutional, 2022) — ok
- `arXiv:2310.08419` (chao2024jailbreaking, 2024) — ok
- `arXiv:2312.06674` (inan2023llama, 2023) — ok
- `arXiv:1504.04909` (mouret2015illuminating, 2015) — ok
- `arXiv:2602.22291v2` (munshi2026manifold, 2026) — companion paper, ok
- `arXiv:2307.15043` (zou2023universal, 2023) — ok
- `arXiv:2401.05566` (hubinger2024sleeper, 2024) — ok
- `arXiv:2410.02644` (zhang2024asb, 2024) — ok
- `arXiv:2512.12066` (yuan2025instability, 2025) — month=12 → December 2025, ok
- `arXiv:2502.15799` (skoltech2025quant, 2025) — ok
- `arXiv:2603.20957` (liu2026whackamole, 2026) — **FLAG**: the 5-digit paper number `20957` is higher than any month's actual submission volume (arXiv monthly totals are ~20k; borderline plausible for CS alone but rarely seen this late in the range). Not clearly fabricated, but suspicious — worth double-checking before camera-ready.
- `arXiv:2503.00555` (huang2025safetytax, 2025) — ok
- `arXiv:2603.00047` (huang2026formal, 2026) — ok
- `arXiv:2602.02395` (slingshot2026, 2026) — ok

No clearly impossible IDs (no `3000.xxx` or similar). **One soft flag** on `2603.20957`.

---

## Category 7: Abstract / artifact factual cross-check

### 7.1 File count
- Claim (paper2_v2.tex lines 97, 204, 2113; overleaf mirror): "46 files"
- Actual `find ... -name "*.lean"` in `ManifoldProofs/`: 45 inside `ManifoldProofs/ManifoldProofs/` + 1 root `ManifoldProofs.lean` = **46 total**. ✓
- Claim (paper2_neurips.tex lines 87, 194, 1703; overleaf mirror): "45 files" — **INCONSISTENCY** with v2 version; paper2_neurips undercounts by one (omits the root import file). Fix by changing `45 files, ${\sim}350$ theorems` → `46 files, ${\sim}360$ theorems` in the neurips version to match v2.
  - [ ] paper2_neurips.tex line 87: `45 files, ${\sim}350$ theorems` → `46 files, ${\sim}360$ theorems`
  - [ ] paper2_neurips.tex line 194: same substitution.
  - [ ] paper2_neurips.tex line 1703: `The artifact comprises 45 files:` → `The artifact comprises 46 files:`
  - [ ] overleaf_package/paper2_neurips.tex lines 87, 194, 1654: identical substitutions.

### 7.2 `sorry` / `admit`
Ripgrep of `/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs/*.lean` for a bare `sorry` or `admit` token at line start returns zero proof-term hits. The only matches are:
- Comments and docstrings containing the words "sorry" / "admits" (e.g., `-- sorry count: 0`, `theorem finite_data_admits_continuous_extension`, `theorem safe_preserving_admits_complete_defense`). These are declarations/documentation, not unfinished proofs.

Claim "no admitted proofs" is **correct**.

### 7.3 "validated" vs "illustrated"
- paper2_v2.tex line 98: `"illustrated empirically on three LLMs"` ✓ (already softened)
- paper2_neurips.tex line 88: `"illustrated empirically on three LLMs"` ✓
- overleaf_package/paper2_v2.tex line 98: `"illustrated empirically on three LLMs"` ✓
- overleaf_package/paper2_neurips.tex line 88: `"illustrated empirically on three LLMs"` ✓
- paper2_defense_impossibility.tex line 95: `"validated empirically on three LLMs"` — **not in audit target**, but flagged for consistency (the older/alt draft still says "validated").

All four audit targets already use "illustrated". **Nothing to do here** — paper agent's softening is complete.

---

## Summary

**Total issues: 13**

**High priority (breaks build or is factually wrong): 8**
1. `\providecommand{\BootstrapL{}}{TODO}` at paper2_neurips.tex:1031 (and three similar at 1032–1034) — malformed macro definitions.
2. Broken `\Cref{sec:estimators}` at paper2_neurips.tex:1042 — missing label → `??` in PDF.
3. Broken `\Cref{app:sparse-smoke-tests}` at paper2_neurips.tex:1082 — missing label.
4. Broken `\Cref{app:judge-robustness}` at paper2_neurips.tex:1086 — missing label.
5. File-count mismatch between v2 ("46 files, ~360 theorems") and neurips ("45 files, ~350 theorems"). Six lines to change across paper2_neurips.tex and overleaf_package/paper2_neurips.tex (lines 87, 194, 1703 and 87, 194, 1654).

**Medium (polish): 2**
6. paper2_v2.tex: Figure 4 label `fig:theory-vs-reality-saturated` is never `\Cref`'d in the body prose — add a `\Cref{fig:theory-vs-reality-saturated}` in Sec. 10.2 around line 1321 so Figure 4 is explicitly referenced.
7. Consider adding `(TP=3, FP_int=0)` explicitly in the Figure 4 caption for Agent 4 to ensure the regenerated figure caption exposes these numbers symbolically.

**Low (stylistic): 3**
8. Soft flag on `arXiv:2603.20957` (liu2026whackamole) — 5-digit paper number `20957` is atypically large; verify before camera-ready.
9. Orphan labels listed in Category 2 (28 labels in paper2_v2.tex never referenced). Most are reasonable section/theorem anchors; no action needed unless you want to trim.
10. `paper2_defense_impossibility.tex` (not in audit target) still says "validated empirically" rather than "illustrated" — flag only.

---

## Top-5 one-shot fixes for the paper agent

1. **paper2_neurips.tex lines 1031–1034** — remove the spurious `{}` inside the macro name of each `\providecommand`:
   `\providecommand{\BootstrapL{}}{TODO}` → `\providecommand{\BootstrapL}{TODO}` (and similarly for `\BootstrapK`, `\BootstrapEll`, `\BootstrapG`).

2. **paper2_neurips.tex line 87 and 194** (and the overleaf mirror at lines 87 and 194) — change `45 files, ${\sim}350$ theorems` → `46 files, ${\sim}360$ theorems` to match paper2_v2.tex. Also line 1703 (overleaf mirror 1654): `The artifact comprises 45 files:` → `46 files:`.

3. **paper2_neurips.tex lines 1042, 1082, 1086** — the three `\Cref{sec:estimators}`, `\Cref{app:sparse-smoke-tests}`, `\Cref{app:judge-robustness}` have no matching `\label{}` in this file. Either add the labels to the relevant sections (preferred) or rewrite the forward references to stand alone.

4. **paper2_v2.tex around line 1321** — add an explicit `\Cref{fig:theory-vs-reality-saturated}` reference so Figure 4 is cited from prose (currently the figure is defined but never cross-referenced).

5. **Agent 4 Figure 4 regeneration** — when regenerating `figures/oblique_theory_vs_reality.pdf`, carry through the same numbers already baked into the caption (`ℓ=0.86, K=1.05, ℓ(K+1)=1.77, G=23.6, |S_pred|=3, |S_act|=68`); consider adding `TP=3, FP_int=0` to the caption at paper2_v2.tex line 1340–1345 for parity with Tables 7–8.
