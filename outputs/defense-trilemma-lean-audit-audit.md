# Paper–Code Audit: "The Defense Trilemma" × Lean 4 Formalization

**Paper:** `paper2_v2.tex` — "The Defense Trilemma: Why Prompt Injection Defense Wrappers Fail?"  
**Codebase:** `ManifoldProofs/` — Lean 4 + Mathlib formalization  
**Repo:** https://github.com/mbhatt1/stuff/tree/main/ManifoldProofs  
**Audit date:** 2026-04-09 (v2 — with argument gap analysis)

---

## Executive Summary

The formalization is substantially sound. The core theorems match the paper's claims, the build passes with zero `sorry` and only the three standard Lean/Mathlib axioms. However, the audit identified **seven argument gaps** ranging from a genuine hypothesis-strength mismatch in the transversality theorem to unformalised intermediate claims. No incorrect theorems were found. Every Lean proof verifies what it states. The gaps are about distances between what the paper claims and what the Lean code proves.

**Fixes applied in this round:**
- Artifact list now clarifies that MoF_11 formalizes the global-L version of persistence while MoF_20 formalizes the defense-path ℓ version that matches the paper.
- Defense Dilemma (Thm 6.3) Lean reference now explains that `optimal_K_exists` in MoF_19 is parameterised by generic (G, L) and recovers the paper's version by instantiating L ↦ ℓ.
- Appendix proof of Thm 6.3 now cites `persistent_unsafe_refined` in MoF_20 as the primary Lean counterpart.

---

## Argument Gaps

### Gap 1 (MEDIUM): Transversality hypothesis is stronger in Lean than stated in paper

**Paper (Prop 6.4):** "if $f$ has directional derivative $c > \ell(K+1)$ along a unit vector $v$ at boundary point $z$, then $z + tv \in \mathcal{S}$ for sufficiently small $t > 0$."

**Lean (`transversality_from_deriv` in MoF_11):**
```
(h_deriv : ∀ t : ℝ, 0 < t → t < 1 → f (z + t • v) ≥ τ + c * t)
```

**The mismatch:** The paper claims the directional derivative $c$ suffices. A directional derivative gives $f(z + tv) = \tau + ct + o(t)$, which implies $f(z + tv) \ge \tau + ct$ only for *sufficiently small* $t$, not for all $t \in (0, 1)$.

The Lean hypothesis is a **uniform linear lower bound** on $(0, 1)$, strictly stronger than a directional derivative. The paper says "directional derivative"; the Lean requires a global linear minorant.

**Impact:** The Lean theorem is correct but proves a stronger (harder to satisfy) hypothesis than the paper states. A paper reader would think a directional derivative suffices; the Lean code actually requires more. To close this gap, the Lean code would need a lemma: "if $f$ has directional derivative $c$ at $z$ along $v$, then $\exists \delta > 0$ such that $f(z + tv) \ge \tau + ct$ for $t \in (0, \delta)$" — this is standard but absent.

**Fix needed:** Either weaken the Lean hypothesis to use `HasFDerivAt` / Fréchet derivative (harder Lean work), or add an intermediate lemma deriving the growth bound from a derivative, or clarify in the paper that a linear growth condition is assumed rather than just a derivative.

---

### Gap 2 (MEDIUM): Defense Dilemma is logically trivial in Lean

**Paper (Thm 6.3, "Defense Dilemma"):** Presents a fundamental tradeoff: K < K* → persistence; K ≥ K* → wide band.

**Lean (`defense_cannot_win` in MoF_19):**
```lean
theorem defense_cannot_win (G L K : ℝ) :
    G > L * (K + 1) ∨ L * (K + 1) ≥ G := by
  by_cases h : G > L * (K + 1)
  · exact Or.inl h
  · exact Or.inr (le_of_not_gt h)
```

**The mismatch:** This is law of excluded middle on a comparison — `a > b ∨ b ≥ a`. The non-trivial content is:
1. The *interpretation*: horn (1) connects to `persistent_unsafe_refined`, horn (2) connects to the ε-robust band width.
2. The *realizability*: `defense_dilemma_both_realizable` proves both horns are achievable.

But these connecting pieces are not composed into a single theorem in Lean. The "dilemma" as proved is pure trichotomy.

**Impact:** Presentation gap. A reviewer inspecting the Lean source might note that the "Defense Dilemma" theorem has a one-line proof (`by_cases`), undermining the claimed significance. The real content is distributed across `optimal_K_exists`, `persistent_unsafe_refined`, and `epsilon_robust_impossibility`, but never assembled.

---

### Gap 3 (MEDIUM): Horn (2) of the dilemma is a proof limitation, not an impossibility

**Paper (Thm 6.3, item 2):** "If $K \geq K^*$: the $\varepsilon$-robust bound $\tau - \ell(K+1)\delta$ becomes loose enough that the theorem can no longer exclude the defense from succeeding on the steep region ($\ell(K+1) \geq G$)."

**Analysis:** This is correctly stated as a proof limitation ("can no longer exclude"), not a proved impossibility. But the theorem title "Defense Dilemma" and the framing as two "horns" suggest symmetric badness. In reality:

- **Horn (1)** (K < K*): Proved impossibility — the defense provably fails on a positive-measure set.
- **Horn (2)** (K ≥ K*): No proved impossibility — the theorem merely *stops applying*. The defense might succeed here.

The dilemma is real (increasing K helps against persistence but widens the ε-band), but the two horns have asymmetric proof strength. Horn (2) shows the band widens ($L \cdot K \cdot \delta$ grows), but widening of the *constraint* is not the same as widening of *actual failure*.

**Recommendation:** Consider restating horn (2) as: "the ε-robust constraint $f(D(x)) \geq \tau - LK\delta$ weakens, and the near-threshold band $\mathcal{B}_\varepsilon$ where the defense provably cannot push far below $\tau$ grows as $O(K)$."

---

### Gap 4 (LOW-MEDIUM): Gradient-to-directional-derivative link is not formalised

**Paper (Thm 6.3):** "Assume $f$ is differentiable at boundary point $z$ with $G = \|\nabla f(z)\|$."  
**Paper (Prop 6.4):** "if $f$ has directional derivative $c > \ell(K+1)$ along a unit vector $v$..."

The implicit link: $G = \|\nabla f(z)\|$ guarantees $\exists v$ with $\nabla f(z) \cdot v = G$, so the max directional derivative equals $G$. When $G > \ell(K+1)$, this $v$ satisfies Prop 6.4's hypothesis.

**Lean status:** MoF_19 takes $G$ as a free real parameter. MoF_11's `transversality_from_deriv` takes $c$ as a free parameter. Neither connects $G$ to $\|\nabla f(z)\|$ or proves that a gradient exists and achieves the max directional derivative. The gradient-norm machinery is in Mathlib (`HasFDerivAt`, `fderiv`) but not used.

**Impact:** The end-to-end chain "differentiable ⟹ gradient exists ⟹ max directional derivative = ‖∇f‖ = G ⟹ transversality" is not formalised. Each step is standard real analysis, but the composition is missing from the artifact.

---

### Gap 5 (LOW-MEDIUM): Coarea formula claim is not formalised

**Paper (Thm 5.2):** "The remainder — boundary points outside $\overline{S_\tau}$ — is contained in the level set $f^{-1}(\tau)$, which has measure zero when $f$ is Lipschitz on $\mathbb{R}^n$ (by the coarea formula)."

**Lean status:** MoF_17_CoareaBound explicitly says in its header: "The full coarea formula may not be available in Mathlib, so we use a self-contained Lipschitz ball-containment argument." The Lean code proves positive measure of the ε-band via ball containment. It does **not** prove the level set $f^{-1}(\tau)$ has measure zero.

**Impact:** The paper's claim about "almost every" band point being fixed relies on the coarea formula, which is not in the Lean artifact. The conclusion that the band has positive measure is proved; the sharper claim about measure-zero exceptions is not.

---

### Gap 6 (LOW): Capacity parity theorems are trivially true

As documented in the v1 audit: `defense_leaks_per_turn` proves `T ≤ T`, `capacity_parity_disadvantage` proves `n_unsafe < n_total`, `one_more_attack_overwhelms` proves `n < n + 1`. These pass the type checker but encode no real content of the informal arguments they claim to represent.

---

### Gap 7 (LOW): Binary search claim is not formalised

**Paper (§8.1):** "the attacker can steer toward transversality via binary search (`transversality_reachable`)."

**Lean (`transversality_reachable` in MoF_13):** Proves *existence* of a transversality-inducing parameter via IVT on a continuous slope function. Does not prove binary search convergence or query complexity.

**Impact:** The claim that binary search efficiently *finds* the transversality parameter is informal. The Lean theorem proves existence, not computability.

---

## Claim-to-Code Correspondence Table

(Updated with gap references)

| Paper Theorem | Lean Location | Match | Gaps |
|---|---|---|---|
| Thm 4.1 (Boundary Fixation) | `defense_incompleteness`, MoF_08 | ✅ Exact | — |
| Thm 4.2 (Defense Trilemma) | Corollary + `complete_defense_must_jump`, MoF_13 | ✅ | — |
| Thm 4.3 (Score-Preserving) | `score_preserving_boundary_fixation`, MoF_16 | ✅ Exact | — |
| Thm 4.4 (ε-Relaxed) | `eps_relaxed_boundary_fixation`, MoF_16 | ✅ Exact | — |
| Thm 5.1 (ε-Robust) | `epsilon_robust_impossibility`, MoF_11 | ✅ Exact | — |
| Thm 5.2 (Pos.-Measure Band) | `positive_measure_failure_band`, MoF_11 | ⚠️ | Gap 5 (coarea) |
| Lem 5.3 (Input-Relative) | `defense_from_input_bound_refined`, MoF_20 | ✅ | — |
| Def 5.4 (Steep Region) | `steepRegionRefined`, MoF_20 | ✅ | — |
| Thm 6.3 (Persistent Region) | `persistent_unsafe_refined`, MoF_20 | ✅ | — |
| Prop 6.4 (Transversality) | `transversality_from_deriv`, MoF_11 | ⚠️ | **Gap 1** (hypothesis) |
| Thm 6.1 (Volume Bound) | `epsilon_band_volume_lower_bound_real`, MoF_17 | ✅ | — |
| Thm 6.2 (Cone Bound) | `cone_measure_bound`, MoF_18 | ✅ | — |
| Thm 6.3 (Defense Dilemma) | `optimal_K_exists`, MoF_19 | ⚠️ | **Gaps 2, 3, 4** |
| Thm 7.1 (Tietze Bridge) | `continuous_relaxation_master`, MoF_CR | ✅ | — |
| Thm 7.2 (Discrete IVT) | `discrete_ivt`, MoF_12 | ✅ | — |
| Thm 7.4 (Discrete Dilemma) | `injectivity_forces_incompleteness` + dual, MoF_12 | ✅ | — |
| Thm 8.1 (Multi-Turn) | `multi_turn_impossibility`, MoF_13 | ✅ | — |
| Thm 8.2 (Stochastic) | `stochastic_defense_impossibility`, MoF_13 | ✅ | — |
| Thm 8.3 (Pipeline Lipschitz) | `two_stage_lipschitz` etc., MoF_15 | ✅ | — |
| Thm 8.4 (Pipeline Impossibility) | `pipeline_impossibility`, MoF_15 | ✅ | — |

---

## Sorry / Axiom Audit — PASS

- **Sorry count: 0.** Confirmed by grep.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound` — all standard.
- **Build:** 8066 jobs, all successful. Only linter warnings.

---

## Quantitative Claims — PASS

| Claim | Verified | Match |
|---|---|---|
| "45 files" | 44 + 1 root = 45 | ✅ |
| "~350 theorems" | 357 | ✅ |
| "zero sorry" | 0 | ✅ |
| "three standard axioms" | propext, Classical.choice, Quot.sound | ✅ |
| Lean 4.28.0, Mathlib v4.28.0 | Confirmed in toolchain + lakefile | ✅ |

---

## Summary of All Findings

| # | Severity | Finding | Status |
|---|---|---|---|
| 1 | **MEDIUM** | Lean `transversality_from_deriv` requires uniform linear growth, not just directional derivative. Paper states "directional derivative" suffices. | **CLOSED — MoF_21_GradientChain** derives the growth bound from `HasFDerivAt` |
| 2 | **MEDIUM** | `defense_cannot_win` is logically trivial (excluded middle). Content is distributed but not composed. | Open — presentation |
| 3 | **MEDIUM** | Horn (2) of dilemma is a proof limitation, not proved impossibility. Asymmetric with horn (1). | Open — clarify |
| 4 | LOW-MED | Gradient → directional derivative → transversality chain not end-to-end formalised. | **CLOSED — MoF_21_GradientChain** |
| 5 | LOW-MED | Coarea formula (level set measure zero) cited but not formalised. | Open |
| 6 | LOW | Capacity parity theorems prove trivial arithmetic. | Open |
| 7 | LOW | Binary search claim for steering is informal. | Open |
| R1 | — | MoF_11 vs MoF_20 reference confusion for persistent region. | **Fixed** |
| R2 | — | MoF_19 `optimalK` parameter naming (L vs ℓ). | **Fixed** (clarified instantiation) |

---

## Sources

- **Paper:** `paper2_v2.tex` (local)
- **Lean formalization:** https://github.com/mbhatt1/stuff/tree/main/ManifoldProofs
- **Build log:** `lean_build_output.txt` (8066 jobs, 0 errors)
- **Companion paper:** Munshi et al., "Manifold of Failure," arXiv:2602.22291v2, 2026.
