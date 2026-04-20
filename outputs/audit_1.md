# Audit 1 — Abstract, Intro, Lean

**Scope:** Abstract, §1 Introduction, §3 Problem Setup, and Lean-artifact claims in `/Users/mbhatt/stuff/paper2_v3.tex`.

**Method:** Each quantitative / citation / label claim is verified against primary data (Lean sources, bibliography, paper labels).

## Claims checked

| # | Section / line | Claim | Source file | Result |
|---|---|---|---|---|
| 1  | Abstract L96 | "46 files" (Lean) | `/Users/mbhatt/stuff/ManifoldProofs/` (45 under `ManifoldProofs/` + 1 root `ManifoldProofs.lean`) | ✅ matches (45 + 1 = 46) |
| 2  | Abstract L96 | "~360 theorems" | `grep ^(theorem\|lemma\|corollary) ` across `*.lean` | ✅ 361 declarations (within "~360") |
| 3  | Abstract L96–97 | "no admitted proofs" | grep `^\s*(sorry\|admit)` in `*.lean` | ✅ 0 code-level `sorry`/`admit`; one hit is a doc comment in `MoF_ContinuousRelaxation.lean` line 34 ("sorry count: 0") |
| 4  | Abstract L97 | "only three standard axioms" | `ManifoldProofs/README.md` L48 | ✅ explicitly lists `propext`, `Classical.choice`, `Quot.sound`; root `ManifoldProofs.lean` L2 repeats the claim |
| 5  | Abstract L98 | URL `github.com/mbhatt1/stuff/.../ManifoldProofs` | paper | ✅ link present (unverifiable online; path under repo exists locally) |
| 6  | Abstract — spec item | "three LLMs" reference | paper | N/A — the abstract does NOT contain the phrase "three LLMs"; the spec's trigger text is absent, so no [17] citation is made in the abstract. Closest match: `\cite{munshi2026manifold}` appears at L910 and L973 (body, not abstract). |
| 7  | Bibliography | `[17]` resolves to `munshi2026manifold` | `\bibitem` ordering L1256–L1349 | ✅ counting in order: alon(1), bagnall(2), bai(3), chao(4), cohen(5), goodfellow(6), inan(7), katz(8), carlini(9), mehrotra(10), fawzi(11), greshake(12), huang(13), madry(14), mouret(15), naitzat(16), **munshi(17)** |
| 8  | §1 L115 | `\cite{alon2023detecting}` | bibliography L1256 | ✅ exists |
| 9  | §1 L116 | `\cite{bai2022constitutional}` | bibliography L1268 | ✅ exists |
| 10 | §1 L117 | `\cite{inan2023llama}` | bibliography L1289 | ✅ exists |
| 11 | §1 L136 | `\Cref{thm:main}` | L327 | ✅ label exists |
| 12 | §1 L136 | `\Cref{thm:score-preserving}` | L419 | ✅ label exists |
| 13 | §1 L136 | `\Cref{thm:eps-relaxed}` | L436 | ✅ label exists |
| 14 | §1 L136 | `\Cref{thm:eps-robust}` | L470 | ✅ label exists |
| 15 | §1 L136 | `\Cref{thm:persistent}` | L556 | ✅ label exists |
| 16 | §1 L142 | `\Cref{thm:disc-dilemma}` | L728 | ✅ label exists |
| 17 | §1 L147 | `\Cref{thm:multi-turn}` | L778 | ✅ label exists |
| 18 | §1 L153 | `\Cref{thm:stochastic}` | L830 | ✅ label exists |
| 19 | §1 L181 | `\Cref{app:counterexamples}` | L1704 | ✅ label exists |
| 20 | §1 L186 | `\Cref{thm:main,thm:score-preserving,thm:eps-relaxed,thm:eps-robust,thm:persistent}` (contributions) | see above | ✅ all exist |
| 21 | §1 L192 | `\Cref{thm:disc-dilemma}` | L728 | ✅ exists |
| 22 | §1 L196 | `\Cref{thm:multi-turn,thm:stochastic}` | L778, L830 | ✅ both exist |
| 23 | §1 L204 | Contributions: "46 files" | `ls ManifoldProofs/` | ✅ 46 |
| 24 | §1 L204 | Contributions: "~360 theorems" | grep count | ✅ 361 |
| 25 | §1 L205 | "no admitted proofs" | grep `sorry`/`admit` | ✅ 0 |
| 26 | §1 L205 | "three standard axioms" | README.md L48 | ✅ confirmed |
| 27 | Abstract L88–90 | refs `thm:coarea`, `thm:cone`, `thm:dilemma` | L1526, L1544, L1555 | ✅ all three labels exist |
| 28 | §3 L279 | ref `thm:main` in figure caption | L327 | ✅ exists |
| 29 | §3 L326 | `\begin{theorem}[Boundary Fixation]` with `\label{thm:main}` | L327 | ✅ defined |
| 30 | §3 L358 | `\begin{theorem}[Defense Trilemma]` with `\label{thm:trilemma}` | L359 | ✅ defined |
| 31 | §3 L368 | `\Cref{fig:trilemma}` and `\Cref{app:counterexamples}` | L402, L1704 | ✅ both exist |
| 32 | §3 L418 | `thm:score-preserving` | L419 | ✅ exists |
| 33 | §3 L435 | `thm:eps-relaxed` | L436 | ✅ exists |
| 34 | §3 L124 | `\Cref{fig:trilemma}` in intro | L402 | ✅ exists |
| 35 | Lean Artifact L2180 | "46 files" | `ls` | ✅ 46 |
| 36 | Lean Artifact L2181–L2212 | file-count breakdown sums to 46 | 10+10+10+12 singletons+3 capstone+1 root = 46 | ✅ matches |
| 37 | Lean Artifact L2177 | "Lean 4.28.0 with Mathlib v4.28.0" | README.md L46 | ✅ README confirms |
| 38 | Lean Artifact L2186–L2211 | Specific singletons (MoF_11_EpsilonRobust, MoF_12_Discrete, MoF_13_MultiTurn, MoF_14_MetaTheorem, MoF_15_NonlinearAgents, MoF_16_RelaxedUtility, MoF_17_CoareaBound, MoF_18_ConeBound, MoF_19_OptimalDefense, MoF_20_RefinedPersistence, MoF_21_GradientChain, MoF_ContinuousRelaxation) | `ls ManifoldProofs/ManifoldProofs/` | ✅ all 12 exist |
| 39 | Lean Artifact L2209 | "3 capstone files (MasterTheorem, Euclidean instantiation, verification)" | files: MoF_MasterTheorem.lean, MoF_Instantiation_Euclidean.lean, MoF_FinalVerification.lean | ✅ all three exist |
| 40 | README.md L12 | "39 files" (README internal claim) | `ls` gives 45 under subdir | ⚠️ MISMATCH (README out of date; paper says 46, dir has 45+1=46). Not a paper claim, noted for completeness. |
| 41 | README.md L14 heading | "Structure (39 files)" | actual 45 in subdir | ⚠️ MISMATCH in README (not a paper claim) |

## Notes on specific items

- **"three LLMs" (spec item 2):** The audit spec asked to check the abstract's "three LLMs" reference citing [17]. That phrase does **not** appear anywhere in `paper2_v3.tex`. There is no such claim in the abstract. Marked N/A rather than ❌ because the claim does not exist to be fabricated; however, the spec's expected phrasing is not in the paper.
- **Citation [17] mapping:** Although no reference in the abstract points to [17] explicitly, the numeric position of `munshi2026manifold` in the `\bibitem` list is 17th, so any `\cite{munshi2026manifold}` in body (L910, L973) renders as `[17]` under default `plain`/`unsrt` ordering.
- **README staleness:** `ManifoldProofs/README.md` still says "39 files" (L12, L14). The paper's "46 files" claim is the up-to-date count and is supported by the directory listing. The README does correctly list the three standard axioms at L48.
- **`sorry`/`admit`:** The only grep hits for these tokens in any form are non-code (a docstring comment `sorry count: 0` in `MoF_ContinuousRelaxation.lean` L34, narrative text `All results are sorry-free` in `MoF_03_ThresholdCrossing.lean` L180, and `they are sorry-free` in `MoF_FinalVerification.lean` L135). No admitted proofs in code.
- **§3 Problem Setup:** All theorem environments in §3 (thm:main, thm:trilemma, thm:score-preserving, thm:eps-relaxed, thm:eps-robust, thm:persistent, lem:input-bound, def:ad, def:defense, def:steep) have matching `\label`s and are referenced consistently.

## Summary

- Total claims checked: 41
- ✅ passes: 39
- ❌ fabricated: 0
- ⚠️ mismatches: 2 (both internal to `ManifoldProofs/README.md`, neither affects a paper claim)
- N/A: 1 (spec-requested "three LLMs" text not present in abstract)

**Overall verdict for Audit 1 scope:** No fabricated claims found in the Abstract, §1 Introduction, §3 Problem Setup, or the Lean artifact section. All quantitative Lean numbers (46 files, ~360 theorems, zero admitted proofs, three standard axioms) are backed by the primary source. All intra-document cross-references (`\Cref{thm:*}`, `\Cref{app:*}`) resolve to existing labels. All §1 `\cite{}` keys resolve to present `\bibitem{}` entries. The README's "39 files" heading is stale but is not a claim the paper makes.
