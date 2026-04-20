# Audit 2: Theorem/Lemma/Proposition and Proof-Block Audit

**Auditor:** Agent 2 of 10 (READ-ONLY)
**Target:** `/Users/mbhatt/stuff/paper2_v3.tex` (2214 lines)
**Lean tree:** `/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs/*.lean` (45 module files + 1 root = 46 files)
**Scope:** §4–§9 main paper and §B full-proofs appendix, plus every `\Cref{thm:...}`/`\label{thm:...}` and every explicit Lean-name citation.

---

## 1. Specifically named Lean declarations — existence check

Every declaration explicitly named in the paper was verified by searching `theorem <name>|lemma <name>|def <name>` across `/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs/*.lean`.

| Paper citation (LaTeX `\texttt{...}`) | Cited module (paper) | Lean location | Status |
|---|---|---|---|
| `persistent_unsafe_refined` | `MoF_20_RefinedPersistence` | `MoF_20_RefinedPersistence.lean:124` `theorem persistent_unsafe_refined` | OK |
| `MoF_20_RefinedPersistence` (module) | — | `/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs/MoF_20_RefinedPersistence.lean` | OK (5 theorems + 1 def, matches paper's "primary formalization of `thm:persistent, lem:input-bound, def:steep`") |
| `gradient_norm_implies_steep_nonempty` | `MoF_21_GradientChain` | `MoF_21_GradientChain.lean:166` `theorem gradient_norm_implies_steep_nonempty` | OK |
| `running_max_monotone` | (L794) | `MoF_13_MultiTurn.lean:270` `theorem running_max_monotone` | OK |
| `transversality_reachable` | (L795) | `MoF_13_MultiTurn.lean:345` `theorem transversality_reachable` | OK |
| `shallow_boundary_no_persistence` | (L522) | `MoF_19_OptimalDefense.lean:175` `theorem shallow_boundary_no_persistence` | OK |
| `optimal_K_exists` | `MoF_19_OptimalDefense` | `MoF_19_OptimalDefense.lean:97` `theorem optimal_K_exists` | OK |
| `MoF_17_CoareaBound` (module, thm:coarea) | §B.2 | `MoF_17_CoareaBound.lean` contains `theorem epsilon_band_volume_lower_bound` / `_euclidean` / `_real` / `_pos_unconditional` | OK (module present with on-topic theorems) |
| `MoF_18_ConeBound` (module, thm:cone) | §B.2 | `MoF_18_ConeBound.lean` contains `theorem cone_measure_bound` and `cone_bound_implies_persistent_unsafe` | OK |
| `MoF_19_OptimalDefense` (module, thm:dilemma) | §B.2 | `MoF_19_OptimalDefense.lean` contains `theorem defense_cannot_win`, `defense_dilemma_both_realizable`, `defense_dilemma_tight`, `optimal_K_exists` | OK |
| `MoF_15_NonlinearAgents` (module, thm:pipeline-impossible) | §B.3 | `MoF_15_NonlinearAgents.lean` contains `theorem pipeline_impossibility` at line 117 and `pipeline_constant_exponential` | OK |
| `MoF_21_GradientChain` (module) | §I | `MoF_21_GradientChain.lean` contains `gradient_norm_implies_steep_nonempty`, `gradient_chain_persistent_unsafe`, `deriv_implies_local_growth`, `deriv_implies_strict_local_growth`, `near_optimal_direction` | OK |
| `MoF_12_Discrete` (module, thm:disc-dilemma) | §6 L725 | `MoF_12_Discrete.lean` contains `discrete_defense_boundary_fixed`, `injectivity_forces_incompleteness`, `completeness_forces_noninjectivity`, `discrete_trilemma` | OK |
| `MoF_11_EpsilonRobust` (module, mentioned as earlier version) | §B.1 L1697 | file present; earlier global-L persistence | OK |

**Result: 0 fabricated Lean names.** Every explicitly-cited Lean declaration or module that the paper names exists in the repository and is on-topic for the paper's claim.

---

## 2. `\Cref{thm:...}`/`\ref{thm:...}`/`\Cref{lem:...}` — referent check

All `\label{thm|lem|prop|def:...}` targets in the paper:

```
def:ad            (L286)
def:defense       (L298)
def:steep         (L548)
thm:main          (L327)
thm:trilemma      (L359)
thm:score-preserving (L419)
thm:eps-relaxed   (L436)
thm:eps-robust    (L470)
lem:input-bound   (L528)
thm:persistent    (L556)
thm:disc-dilemma  (L728)
thm:multi-turn    (L778)
thm:stochastic    (L830)
thm:tietze        (L1488)
thm:coarea        (L1526)
thm:cone          (L1544)
thm:dilemma       (L1555)
thm:pipeline      (L1585)
thm:pipeline-impossible (L1598)
thm:basin         (L1625)
thm:fragment      (L1632)
thm:lipschitz     (L1737)
thm:convergence   (L1744)
thm:transfer      (L1751)
thm:authority     (L1758)
thm:gradient      (L1768)
thm:interior-stable (L1778)
thm:crossing      (L1786)
thm:nonlocal      (L1795)
thm:cost          (L1806)
```

Every distinct key cited by `\Cref{...}` or `\ref{...}` appears in the label set above:

| Cited key | Label present? |
|---|---|
| thm:main | OK |
| thm:trilemma | OK |
| thm:score-preserving | OK |
| thm:eps-relaxed | OK |
| thm:eps-robust | OK |
| thm:persistent | OK |
| lem:input-bound | OK |
| def:steep | OK |
| thm:disc-dilemma | OK |
| thm:multi-turn | OK |
| thm:stochastic | OK |
| thm:tietze | OK |
| thm:coarea | OK |
| thm:cone | OK |
| thm:dilemma | OK |
| thm:pipeline | OK |
| thm:pipeline-impossible | OK |
| thm:crossing | OK |
| thm:lipschitz | OK |
| thm:cost | OK |

Compound `\Cref{...,...,...}` citations also checked:
- L136, L186: `thm:main,thm:score-preserving,thm:eps-relaxed,thm:eps-robust,thm:persistent` — all present.
- L196: `thm:multi-turn,thm:stochastic` — both present.
- L700: `thm:coarea,thm:cone,thm:dilemma` — all present.
- L894: `thm:pipeline,thm:pipeline-impossible,app:landscape,app:attacks,app:stability,app:cost` — thm keys both present; the app labels are not in-scope here but all four `\label{app:...}` targets exist in the file.
- L2204: `thm:persistent,lem:input-bound,def:steep` — all present.

**Result: 0 dangling theorem references.**

---

## 3. Proof sketches claiming "Full proof in §B" — existence of the full proof

The phrase "Full proof in \Cref{app:proofs}" appears in exactly three proof sketches:

| Theorem (sketch loc.) | Claim | Full proof loc. in §B | Status |
|---|---|---|---|
| thm:main (L337-346) | "Full proof in \Cref{app:proofs}" L345 | L1644 `\begin{proof}[Proof of \Cref{thm:main} (Boundary Fixation)]` | Present (5-step proof, L1644–1670) |
| thm:eps-robust (L482-488) | "Full proof in \Cref{app:proofs}" L487 | L1672 `\begin{proof}[Proof of \Cref{thm:eps-robust} ...]` | Present (2-step proof, L1672–1681) |
| thm:persistent (L572-578) | "Full proof in \Cref{app:proofs}" L577 | L1683 `\begin{proof}[Proof of \Cref{thm:persistent} ...]` | Present (3-step + Lean note, L1683–1700) |

§B (lines 1641–1700) contains **exactly these three** full proofs and nothing else. No proof sketch with a "Full proof in §B" promise is orphaned.

Other in-paper proof sketches (thm:score-preserving, thm:eps-relaxed, lem:input-bound, thm:multi-turn, thm:stochastic, thm:disc-dilemma [which is a full `\begin{proof}`, not a sketch], thm:tietze) do **not** claim an appendix-B continuation; they stand as-is. No additional promises to audit.

---

## 4. Section-by-section theorem placement & numbering narration

Since the paper uses only `\Cref{...}` and `\ref{...}` (no prose "Theorem 4.1"-style narration), LaTeX auto-numbering is the source of truth; a grep confirms zero literal strings matching `Theorem\s+\d+\.\d+` or `§\d` or `Section \d+\.\d+` in the file. Numbering narrations cannot be mis-synchronized with LaTeX counters because no such narrations exist.

For record, the section-to-theorem map is:

| Section (latex `\section{}`) | Line | Theorems/lemmas with labels |
|---|---|---|
| §4 `Impossibility of Wrapper Defense in Continuous Settings` | L315 | thm:main (L327), thm:trilemma (L359), thm:score-preserving (L419), thm:eps-relaxed (L436), thm:eps-robust (L470), lem:input-bound (L528), def:steep (L548), thm:persistent (L556) |
| §5 `Impossibility of Wrapper Defense in Discrete Settings` | L704 | thm:disc-dilemma (L728) |
| §6 `Impossibility of Wrapper Defense in Stochastic and Multi-Turn Settings` | L768 | thm:multi-turn (L778), thm:stochastic (L830) |
| §7 `Experimental Validation` | L898 | (no theorems) |
| §8 `Implications, Scope, and Limitations` | L1151 | (no theorems) |
| §9 `Conclusion` | L1220 | (no theorems) |
| §A `Continuous Interpolation of Discrete Observations` | L1481 | thm:tietze (L1488) |
| §B (§ "Quantitative Refinements") | L1519 | thm:coarea, thm:cone, thm:dilemma |
| §`Pipeline Composition` | L1581 | thm:pipeline, thm:pipeline-impossible |
| §`Vulnerability Landscape` | L1619 | thm:basin, thm:fragment |
| §`Full Proofs` | L1641 | (only proof environments, no new statements) |
| §`Counterexamples` | L1703 | (no thm/lem) |
| §`Attack Properties` | L1733 | thm:lipschitz, thm:convergence, thm:transfer, thm:authority, thm:gradient |
| §`Stability Under Fine-Tuning` | L1774 | thm:interior-stable, thm:crossing, thm:nonlocal |
| §`Cost Asymmetry` | L1802 | thm:cost |

Minor note (not a bug, just a caveat for the caller's attention): the prompt says "§B full-proofs". The LaTeX structure puts the "Full Proofs" section at L1641 with `\label{app:proofs}`. In the printed PDF it will be `\appendix` section C or similar (depending on how many appendix sections precede it), **not** a literal "§B". The paper's cross-references all use `\Cref{app:proofs}` so LaTeX will print the correct letter automatically; I flag this only so the caller doesn't search for a literal "Appendix B" heading.

---

## 5. Structural Lean-side sanity — proof-of-existence of referenced theorems

| Paper theorem | Principal Lean witness (module) | Witness declaration found? |
|---|---|---|
| thm:main (Boundary Fixation) | MoF_01_Foundations / MoF_02_BasinStructure (not explicitly cited) | — (paper does not pin a specific Lean name; body of core modules present) |
| thm:persistent (Persistent Unsafe Region) | `persistent_unsafe_refined` in `MoF_20_RefinedPersistence` | OK |
| thm:disc-dilemma | `MoF_12_Discrete` (explicitly cited L725); contains `discrete_trilemma`, `injectivity_forces_incompleteness`, `completeness_forces_noninjectivity` | OK |
| thm:multi-turn | `MoF_13_MultiTurn` contains `multi_turn_impossibility` L59 | OK |
| thm:stochastic | `MoF_13_MultiTurn` contains `stochastic_defense_impossibility` L110 | OK |
| thm:tietze | `MoF_ContinuousRelaxation` contains `continuous_relaxation_master` and `euclidean_continuous_relaxation` | OK |
| thm:coarea | `MoF_17_CoareaBound` (explicit) | OK |
| thm:cone | `MoF_18_ConeBound` (explicit) | OK |
| thm:dilemma | `MoF_19_OptimalDefense` (explicit) | OK |
| thm:pipeline | `MoF_15_NonlinearAgents` (`two_stage_lipschitz`, `three_stage_lipschitz`, `pipeline_constant_exponential`) | OK |
| thm:pipeline-impossible | `MoF_15_NonlinearAgents` `pipeline_impossibility` (explicit L1607) | OK |
| thm:authority | `MoF_07_AuthorityMonotonicity` (`critical_threshold_exists`, `monotone_boundary`) | OK |

No fabricated citations detected.

---

## 6. Lean artifact file-count claim (L2180)

Paper (L2180) claims "46 files". Actual count:

```
/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs/*.lean  = 45 files
/Users/mbhatt/stuff/ManifoldProofs/ManifoldProofs.lean     = 1 file (root import)
Total                                                      = 46
```

Claim matches.

---

## Summary

| Check | Items | Pass | Fail |
|---|---|---|---|
| Named Lean declarations (`persistent_unsafe_refined`, `gradient_norm_implies_steep_nonempty`, `running_max_monotone`, `transversality_reachable`, `shallow_boundary_no_persistence`, `optimal_K_exists`) | 6 | 6 | 0 |
| Named Lean modules (`MoF_17_CoareaBound`, `MoF_18_ConeBound`, `MoF_19_OptimalDefense`, `MoF_15_NonlinearAgents`, `MoF_20_RefinedPersistence`, `MoF_21_GradientChain`, `MoF_12_Discrete`, `MoF_11_EpsilonRobust`, `MoF_13_MultiTurn`) | 9 | 9 | 0 |
| `\Cref{thm/lem/def:...}` referent resolution | ~60 call sites / 20 distinct keys | 20/20 | 0 |
| "Full proof in §B" promises resolved | 3 | 3 | 0 |
| Section-numbering narrations consistent with LaTeX counters | no prose narrations exist (auto-numbered throughout) | n/a | 0 |
| Lean artifact file-count claim (46 files) | 1 | 1 | 0 |

**No fabricated Lean declarations, no dangling `\Cref` targets, no unfulfilled "full proof in §B" promises, no numbering narration drift.** The theorem/proof layer of `paper2_v3.tex` §4–§9 + §B is consistent with the `ManifoldProofs` Lean tree as audited.
