# Audit Plan: defense-trilemma-lean-audit

## Target
- **Paper:** `paper2_v2.tex` — "The Defense Trilemma: Why Prompt Injection Defense Wrappers Fail?"
- **Codebase:** `ManifoldProofs/` — Lean 4 + Mathlib formalization (45 files, ~8275 LOC, ~350 theorems)
- **Repo:** https://github.com/mbhatt1/stuff/tree/main/ManifoldProofs

## Audit Scope

### 1. Claim-to-Code Correspondence (HIGH PRIORITY)
Check that each numbered theorem in the paper has a matching Lean theorem with equivalent hypotheses and conclusions.

| Paper Theorem | Expected Lean Location | Check |
|---|---|---|
| Thm 4.1 (Boundary Fixation) | MoF_08_DefenseBarriers | Hypotheses match? Conclusion match? |
| Thm 4.2 (Defense Trilemma) | MoF_08_DefenseBarriers | Separate theorem or corollary of 4.1? |
| Thm 4.3 (Score-Preserving) | MoF_16_RelaxedUtility | Relaxation correctly formalized? |
| Thm 4.4 (ε-Relaxed) | MoF_16_RelaxedUtility | ε bound matches paper? |
| Thm 5.1 (ε-Robust Constraint) | MoF_11_EpsilonRobust | LK·dist bound correct? |
| Thm 5.2 (Positive-Measure Band) | MoF_17_CoareaBound | Ball inclusion proven or assumed? |
| Thm 6.3 (Persistent Unsafe Region) | MoF_11_EpsilonRobust or MoF_20 | Three conclusions all proven? |
| Thm 6.1 (Volume Lower Bound) | MoF_17_CoareaBound | V_n · (ε/4L)^n explicit? |
| Thm 6.2 (Cone Measure Bound) | MoF_18_ConeBound | δ₀ bound correct? |
| Thm 6.3 (Defense Dilemma) | MoF_19_OptimalDefense | K* = G/ℓ - 1 formalized? |
| Thm 7.2 (Discrete IVT) | MoF_12_Discrete | — |
| Thm 7.4 (Discrete Defense Dilemma) | MoF_12_Discrete | Both directions? |
| Thm 8.1 (Multi-Turn) | MoF_13_MultiTurn | Per-turn application? |
| Thm 8.2 (Stochastic) | MoF_13_MultiTurn | g = E[f∘D] formalized? |
| Thm 8.4 (Pipeline Lipschitz) | MoF_15_NonlinearAgents | ∏Kᵢ bound? |
| Thm 7.1 (Continuous Relaxation / Tietze) | MoF_ContinuousRelaxation | Tietze actually invoked? |

### 2. Sorry / Axiom Audit (HIGH PRIORITY)
- Paper claims "zero sorry statements, three standard axioms."
- Preliminary grep found zero sorry in proof terms. Confirm.
- Identify which three axioms. Are they truly standard (propext, funext, Quot.sound) or something exotic?
- Check for `native_decide`, `decide`, `omega` used in ways that hide complexity.

### 3. Hypothesis Strength Comparison (MEDIUM PRIORITY)
- Are the Lean hypotheses strictly stronger than the paper's? (e.g., does Lean require `MetricSpace` where paper says `TopologicalSpace`?)
- Does the Lean code add extra hypotheses not mentioned in the paper (e.g., `CompactSpace`, `LocallyCompactSpace`, `SecondCountableTopology`)?
- Check the "connected Hausdorff" assumption: is it formalized as `ConnectedSpace` + `T2Space`?

### 4. Namespace / Import Structure (MEDIUM PRIORITY)
- The FinalVerification file documents namespace collisions preventing joint import.
- Are the colliding definitions truly equivalent, or do they differ subtly?
- Does this affect any cross-file dependency the paper implicitly relies on?

### 5. Formalization Gaps (MEDIUM PRIORITY)
- Paper claims ~350 theorems. Count actual `theorem` declarations.
- Which paper results, if any, lack a Lean counterpart?
- Are the appendix results (basin structure, fragmentation, transferability, cost asymmetry) all formalized or only some?

### 6. Quantitative Claims (LOW-MEDIUM PRIORITY)
- "45 files" — count actual .lean files
- "~350 theorems" — count `theorem` + `lemma` declarations
- Lean/Mathlib version pinning in lakefile/lean-toolchain

### 7. Empirical Section Consistency (LOW PRIORITY)
- The Lean code is pure math; empirical validation references a companion paper [munshi2026manifold].
- Check that the paper's empirical estimates (G ≈ 5, ℓ ≈ 1, K = 1) are labeled as estimates, not proven.

## Execution Plan
1. **Phase 1 — Automated sweeps:** File counts, theorem counts, sorry/axiom grep, hypothesis extraction from key files.
2. **Phase 2 — Claim-by-claim correspondence:** Read the 8 highest-priority Lean files and compare theorem statements to paper.
3. **Phase 3 — Structural checks:** Namespace collisions, import graph, version pinning.
4. **Phase 4 — Synthesis:** Write the audit artifact.

## Output
- `outputs/defense-trilemma-lean-audit-audit.md`
