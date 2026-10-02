# Skill audit of the TMLR draft 2: "Truth Has a Boundary"

Method: an independent audit agent re-ran compute_bootstrap, compute_controls, compute_crossing_conf and compute_oddness; all outputs were byte-identical. It read every Lean statement in Table 1 and the Defense Trilemma (ManifoldProofs), and web-checked 5 citations. The coordinator independently re-verified the paired sign tests (table below).

## Verdict
**MAJOR REVISION as submitted** (likely desk reject while the red markers are visible). The theory half passes. With the text-only fixes below, a minor revision or accept is realistic, since TMLR judges correctness and interest, not significance.

## What passed
- **Theory:** all 13 numbered results plus the multi-turn and expected-field statements match their Lean statements, including quantifiers and hypotheses. No prose drops a needed hypothesis.
- **Paper-only proofs:** Example 1, the nonemptiness step, Remark 1 and the dichotomy remark are all correct and marked P.
- **Numbers:** every number traced to its JSON matches. The derived JSON regenerates byte-identically.
- **Novelty:** the symmetry, involution and hyperplane results have no analogue in the Defense Trilemma (grep confirms). The related work does not caricature anyone.
- **Negative results** are reported honestly.

## What failed

| # | Severity | Issue | Evidence | Fix (text-only unless noted) |
|---|---|---|---|---|
| 1 | BLOCKING | Six red [EVIDENCE NEEDED] markers in the PDF | PDF text | Resolve each, or replace with "X was not computed" |
| 2 | MAJOR | Abstract/intro: "no smaller than" / "not distinguishable from" the midpoint baseline understates the result | Paired sign tests (below): never better; significantly worse in 3 conditions after Bonferroni | "never reliably smaller than, and in several conditions significantly larger than…"; report paired counts and p-values |
| 3 | MAJOR | The abstract's "65% to 100% of paths" is conditional on probe-correct endpoints | Unconditional over all 149 pairs: 29%–99% | Report both |
| 4 | MAJOR | "Their expected output is the three standard axioms": no log, and many Table 1 identifiers have no `#print axioms` | grep | Attach a `lake build` log (in progress via the toolchain agent), or delete the sentence |
| 5 | MAJOR | Single split and single fit; endogenous and translation runs lack baselines; polarity confound not controlled | scripts | **Needs new experiments**, or state as single-split descriptives |
| 6 | MAJOR (integrity) | Supplement README names a workshop venue and the old title of an earlier, never-submitted draft; Lean comments reference `MoF_*` files (an anonymity leak); README says "every theorem formalized" | README line 5, HoF_02/03/04/09 | Strip these from the supplement (done). No disclosure needed: the earlier draft was never submitted |
| 7 | MINOR | "Bimodal" holds for only 3 of 5 models (GPT-2 and Qwen-1.5B are roughly flat) | 10-bin histograms | "widely dispersed, often U-shaped" |
| 8 | MINOR | Defense Trilemma's stochastic variant not credited; Thm 1, Thm 6 and Prop 12 restate DT lemmas | MoF_13 `stochastic_defense_impossibility`, MoF_03/12 | Credit both |
| 9 | MINOR | Missing related work: selective classification / reject option; adversarial-example inevitability (Shafahi et al. 2019) | — | Add a paragraph |
| 10 | MINOR | Lean 4 and Mathlib are never cited, although they are in refs.bib | — | Cite them in §8 |
| 11 | MINOR | Supplement docstrings contradict the paper (HoF_13 "infimum bounded away"; "topologically impossible" header); experiment docstrings overclaim | source | Edit the supplement |
| 12 | MINOR | Title still omits exact separation | — | e.g. "…under Connectedness and Exact Separation" |
| 13 | MINOR | Add the "gap is itself a premise-violation measure" sentence to the §9 preamble | — | Text |
| 14 | COSMETIC | The abstract's "corridor around the coupled query" (the corridor is between decisive regions); Example 1 only at τ=½; "decisive" vs "endpoint-separating"; 0.3125 decimals | — | Text |

## Paired per-path comparison: trained confidence gap vs midpoint baseline (endpoint-separating paths)

Counts are the number of paths on which the head is worse or better than the midpoint. p is an exact two-sided sign test; the Bonferroni threshold over 14 tests is 0.0036.

| Readout | Model | Worse | Better | p |
|---|---|---|---|---|
| linear | GPT-2 | 34 | 24 | 0.24 |
| linear | Pythia-410M | 45 | 29 | 0.081 |
| linear | Qwen2.5-0.5B | 71 | 47 | 0.034 |
| linear | Phi-1.5 | 22 | 18 | 0.64 |
| linear | Qwen2.5-1.5B | 66 | 57 | 0.47 |
| MLP | GPT-2 | 58 | 29 | **0.0025** |
| MLP | Pythia-410M | 49 | 32 | 0.075 |
| MLP | Qwen2.5-0.5B | 75 | 38 | **0.00064** |
| MLP | Phi-1.5 | 48 | 27 | 0.02 |
| MLP | Qwen2.5-1.5B | 69 | 55 | 0.24 |
| endogenous | GPT-2 | 12 | 9 | 0.66 |
| endogenous | Qwen2.5-0.5B | 74 | 45 | 0.01 |
| endogenous | Phi-1.5 | 40 | 13 | **0.00027** |
| endogenous | Qwen2.5-1.5B | 73 | 66 | 0.61 |

## Submission gate (skill §25)
- **Scientific:** contribution scoped PASS · claims match evidence **FAIL** (#2, #3, #7) · limitations PASS · negative results PASS · prior work PASS (minor)
- **Experimental:** seeds **FAIL** · uncertainty **FAIL** (partial) · baselines PASS (partial) · multiple comparisons **FAIL** · confounds **FAIL** · compute **FAIL** · code and data PASS
- **Theory:** assumptions visible PASS · matches mechanization PASS · paper-only proofs PASS · build and axiom evidence **FAIL**
- **Writing:** no placeholders **FAIL** · number consistency PASS · terminology **FAIL** (cosmetic) · title/abstract ≤ body **FAIL**
- **Integrity:** anonymity **FAIL** · prior-version disclosure **FAIL** (pending) · citations **FAIL** (partial) · no fabricated values PASS

## Draft-1 findings
- **Resolved:** #2–4, #9–16, #18, #21.
- **Partial:** #1 (wording, see #2 above), #5, #17, #19.
- **Not resolved:** #7 (markers), #8 (README/anonymity).
- **Disclosed only:** #20.
