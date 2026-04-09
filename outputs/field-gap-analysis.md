# What's Missing to Turn This Into a Field

**Repo:** Defense Trilemma — impossibility theorems for prompt injection wrapper defenses  
**Current state:** One paper (v2), 46 Lean files (~360 theorems), 14 derived predictions verified against literature, 4 research dossiers, companion empirical paper (Munshi et al.)

---

## What You Have (Inventory)

| Layer | What exists | Strength |
|---|---|---|
| **Core theory** | Three-tier impossibility (boundary fixation → ε-robust → persistent unsafe region), discrete dilemma, multi-turn, stochastic, pipeline degradation | Mechanically verified, clean escalation, counterexamples proving tightness |
| **Formal artifact** | 46 Lean 4 files, zero `sorry`, three standard axioms, Mathlib-backed | Strongest verification artifact in LLM security to date |
| **Predictions** | 14 falsifiable predictions derived from named theorems, 12/14 confirmed by independent literature | Strong empirical coverage; the theory *retrodicts* known phenomena |
| **Empirical validation** | 3 LLMs on a 2D behavioral grid (companion paper) | Directional confirmation, but limited scale |
| **Engineering prescription** | 4 concrete levers (shallow boundary, reduce L, reduce d, monitor don't eliminate) | Actionable but qualitative |

## What a Field Needs That You Don't Have

A field is not a result. A result becomes a field when other groups can (1) use your framework to ask new questions, (2) compete on shared benchmarks, (3) extend the theory in directions you didn't anticipate, and (4) build practical systems informed by it. Here's the gap analysis, ordered from highest leverage to lowest.

---

### 1. An Empirical Measurement Protocol (Critical Gap)

**Problem:** The alignment deviation function $f: X \to \mathbb{R}$ is the central object of the theory, but there is no standardized way to *measure it*. The companion paper uses a 2D behavioral grid (query indirection × authority framing) on 3 models. This is a proof-of-concept, not a measurement standard.

**What's needed:**
- **Operational definition of $f$**: How do you compute AD for an arbitrary (prompt, model) pair? What judge? What rubric? What scale? Is it the probability of harmful completion? A continuous harm severity score? A classifier logit?
- **Reference implementation**: An open-source tool that takes (model, prompt) → AD score, with documented judge calibration.
- **Canonical prompt sets**: Not just attack prompts — you need *grid-covering* sets that sample the space uniformly enough to estimate basin structure, boundary location, Lipschitz constants, and fragment counts.
- **Multi-dimensional behavioral coordinates**: The 2D (indirection, authority) grid is a start. But the theory operates on the full prompt space $X$. You need a principled embedding that others can replicate: what are the behavioral axes? How many dimensions matter? Is there a low-dimensional manifold where the interesting structure lives?

**Why it's critical:** Without this, nobody can independently measure the quantities your theorems are about. The Lipschitz constant $L$, the basin rate, the transversality slope $G$ — these are all empirically estimable *in principle*, but no one has a protocol to estimate them for a new model. The theory remains unfalsifiable in practice.

**Deliverable:** A paper or technical report titled something like "Measuring Alignment Deviation: A Protocol for Estimating Defense-Theoretic Quantities in Language Models." Includes: operational definition, reference code, calibration study across ≥5 models, inter-rater reliability for the judge, and estimation procedures for $L$, $G$, basin volume, and fragment count.

---

### 2. Benchmark Suite for Defense-Theoretic Quantities (Critical Gap)

**Problem:** Existing LLM safety benchmarks (HarmBench, AdvBench, StrongREJECT, WildGuard) measure attack success rates — a one-dimensional summary. Your framework predicts *geometric structure*: basins, boundaries, fragments, Lipschitz constants, cost asymmetries. No benchmark measures these.

**What's needed:**
- **DefenseTrilemma-Bench**: A benchmark that, for a given model, outputs:
  - Basin rate at threshold $\tau$ (fraction of prompts with $f(x) > \tau$)
  - Estimated Lipschitz constant $L$ (from finite differences on the grid)
  - Fragment count and size distribution
  - Boundary sharpness profile (estimated $G$ at detected boundary crossings)
  - Cost asymmetry ratio at the tested dimensionality
  - Pareto curve: $\tau$ vs. $\mu(U_\tau)$
- **Leaderboard**: Rank models not by "attack success rate" (a single number) but by their defense-theoretic profile. A model with shallow boundaries and low $L$ is fundamentally more defensible than one with deep basins and high $L$, even if both have the same ASR on a fixed attack set.
- **Standard attacks that exercise the theory**: Attacks designed to test specific predictions — interpolation attacks (Prediction 13), multi-depth pipeline attacks (Prediction 3), context-length scaling attacks (Prediction 2), merge-and-test protocols (Prediction 6).

**Why it's critical:** Fields crystallize around shared evaluation. ImageNet made computer vision a field. GLUE/SuperGLUE made NLU a field. SWE-bench made coding agents a field. You need the equivalent.

---

### 3. Estimation Theory for $L$, $G$, and Basin Geometry (Major Gap)

**Problem:** The theorems are parameterized by $L$ (Lipschitz constant of $f$), $K$ (Lipschitz constant of defense $D$), $G$ (transversality slope), and $\ell$ (defense-path Lipschitz constant). The paper estimates these crudely from a 2D grid. There is no systematic estimation theory.

**What's needed:**
- **Statistical estimators** for $L$ from finite samples of $(x_i, f(x_i))$. What's the sample complexity? How does the estimate degrade with dimension?
- **Confidence intervals**: When you estimate $L \approx 5$ from a 2D grid, what's the uncertainty? The persistent unsafe region theorem requires $G > \ell(K+1)$ — is this satisfied with statistical confidence, or just point-estimated?
- **Dimensional scaling**: The theory predicts defense cost $\sim N^d$. But what is $d$ for a real model? Is there an effective dimensionality of the alignment-relevant prompt manifold? Can you estimate it?
- **Connection to model internals**: Can $L$ be estimated from model weights or representations, not just black-box queries? If the alignment surface is approximately a linear probe on some internal representation, $L$ is bounded by the probe's operator norm times the embedding Lipschitz constant.

**Why it matters:** Right now, the theory is exact but the instantiation is approximate. A field needs practitioners who can plug in their model and get quantitative predictions. That requires estimation theory, not just existence theorems.

---

### 4. Constructive Results: Optimal and Near-Optimal Defenses (Major Gap)

**Problem:** The paper proves what defenses *cannot* do. It says almost nothing about what they *should* do. MoF_19 characterizes the optimal defense Lipschitz constant $K^* = G/L - 1$ and proves the defense dilemma (you can't escape both the persistent region and the wide band), but there is no constructive defense that achieves the Pareto bound.

**What's needed:**
- **Minimax defense**: Given estimated $f$, $L$, $G$, what is the defense $D^*$ that minimizes the worst-case unsafe volume? The optimal defense characterization (MoF_19) identifies the tradeoff but doesn't construct $D^*$.
- **Approximation algorithms**: Even if $D^*$ is intractable to compute exactly, can you get within factor $c$ of optimal? What's the approximation ratio?
- **Defense design principles from the theory**: The engineering prescription (§11) gives 4 qualitative levers. These need to become quantitative design rules:
  - "Make the boundary shallow" → what training objective pushes $\max_x f(x)$ toward $\tau$?
  - "Reduce $L$" → what regularization during RLHF controls the Lipschitz constant of the alignment surface?
  - "Reduce $d$" → what prompt interface design minimizes effective dimensionality?
  - "Monitor the boundary" → what online detector estimates distance to the boundary?
- **Lower bounds on defense cost**: For a given $(L, G, d, \tau)$, what is the minimum resource budget for a defense that keeps the unsafe volume below $\epsilon$? This would let practitioners compute "how much defense is enough" for their risk tolerance.

**Why it matters:** Impossibility results alone are intellectually satisfying but operationally sterile. The adversarial robustness field took off when certified defenses (randomized smoothing, interval propagation) gave constructive certificates alongside the impossibilities. Your framework needs the constructive side.

---

### 5. Taxonomy of Defense Classes and Where the Theorems Apply (Moderate Gap)

**Problem:** The paper is careful about scope (§10 Limitations): the theorems apply to continuous, utility-preserving wrappers on connected spaces. Training-time alignment, architectural changes, discontinuous filters, ensemble systems, and human-in-the-loop are explicitly excluded. But the boundary of applicability is fuzzy.

**What's needed:**
- **Formal classification of defenses** into categories with clear membership criteria:
  - Class W: Wrapper defenses $D: X \to X$ (your theorems apply)
  - Class T: Training-time interventions (RLHF, DPO, constitutional training)
  - Class A: Architectural changes (separate safety heads, circuit breakers)
  - Class F: Discontinuous filters (blocklists, classifiers with hard thresholds)
  - Class E: Ensemble/multi-component systems
  - Class H: Human-in-the-loop
- **Which theorems apply to which class**: The paper hints that some predictions extend beyond Class W (e.g., Interior Stability applies to *any* bounded perturbation of $f$, not just wrappers). Make this explicit. Which results are truly wrapper-specific and which are model-inherent?
- **Reduction theorems**: Can you prove that certain Class T or Class A defenses *reduce to* Class W defenses under appropriate formalization? If RLHF is equivalent to applying a continuous perturbation to $f$, then Interior Stability applies to RLHF too — and that's a much stronger claim than "wrappers can't be complete."

**Why it matters:** The biggest objection reviewers will raise is "I don't use wrappers, so this doesn't apply to me." A clean taxonomy with formal reduction theorems would show exactly which practitioners are affected and which are not. The predictions about fine-tuning diminishing returns (Prediction 1) and alignment tax (Prediction 10) already implicitly use Interior Stability beyond the wrapper setting — make this extension rigorous.

---

### 6. Tight Bounds and Lower Bound Completeness (Moderate Gap)

**Problem:** Several bounds are proved to hold but not proved to be tight. The persistent unsafe region has positive measure — but how large? The Markov bound $\mu(\{f \geq \varepsilon\}) \leq (1/\varepsilon)\int f\,d\mu$ is a *generic* bound; it doesn't use the specific structure of the defense setting.

**What's needed:**
- **Tightness examples**: For each main theorem, an explicit construction achieving equality (or approaching it). The counterexamples in §C show the hypotheses are necessary; you also need extremal examples showing the bounds are best possible.
- **Improved volume bounds**: The coarea bound (MoF_17) and cone bound (MoF_18) give positive-measure guarantees. Can these be sharpened to give explicit constants in terms of $(L, G, K, d)$?
- **Matching upper bounds**: For the cost asymmetry, the $N^d$ defense cost assumes exhaustive enumeration. The paper acknowledges (§10) that learning-based defenses might sidestep this. Can you prove a *lower bound* on defense cost that holds even for learning-based methods? (This would require information-theoretic or query-complexity arguments, not just grid counting.)

---

### 7. Connections to Adjacent Fields (Moderate Gap)

**Problem:** The paper positions itself against adversarial robustness (Tsipras, Fawzi, Madry) and no-free-lunch (Wolpert). But the theory touches several other fields where explicit connections would recruit researchers.

**What's needed:**
- **Topological data analysis (TDA)**: The basin structure, fragment counting, and boundary detection are all persistent-homology questions. Can you characterize the unsafe region's topology (Betti numbers, persistence diagrams) from finite samples? This would connect to the TDA community.
- **Game theory / mechanism design**: The cost asymmetry (defense $N^d$, attack $1/\delta$) is a game-theoretic statement. Can the defense-attack interaction be formalized as a Stackelberg game? What's the Nash equilibrium? Does the Folk theorem apply to the multi-turn setting?
- **Information theory**: The discrete dilemma (completeness, utility preservation, injectivity can't coexist) has an information-theoretic interpretation: complete defense requires lossy compression of the prompt space. What's the rate-distortion curve? How much information must the defense destroy to achieve a given safety level?
- **Control theory**: The multi-turn impossibility (unsafe recurrence at every turn) resembles a controllability result. Can the defense problem be cast as a control problem where the alignment surface is the plant, the defense is the controller, and the attacker is a disturbance?
- **Differential privacy**: The $\varepsilon$-robust constraint ($f(D(x)) \geq \tau - LK\delta$) looks like a sensitivity bound. Is there a formal connection between defense impossibility and privacy impossibility?

---

### 8. Second-Generation Experiments (Moderate Gap)

**Problem:** The empirical validation (§9) uses 3 models on a 2D grid from a companion paper, with 9 qualitative predictions checked directionally. This is first-generation validation. A field needs second-generation experiments that:

**What's needed:**
- **Directly measure predicted quantities**: Estimate $L$, $G$, basin volume, fragment count for ≥10 models. Plot predicted vs. observed unsafe volume. Compute $R^2$.
- **Test the derived predictions with controlled experiments**:
  - Prediction 2 (long context): Same model, same attack, context lengths 4K/16K/64K/128K. Measure ASR scaling. Fit the power law. Compare exponent to $d$-estimate.
  - Prediction 3 (pipeline depth): Build agents with 1/2/3/5/10 tool calls. Measure ASR at each depth. Fit exponential. Compare rate to estimated $K$.
  - Prediction 5 (quantization): Quantize a model to INT8/INT4/INT3. Measure which jailbreaks survive. Compare survival threshold to estimated $\varepsilon_\text{quant}$.
  - Prediction 6 (merging): Merge at ratios 0.7/0.5/0.3. Test known jailbreaks. Compare survival to predicted critical ratio $\alpha^*$.
  - Prediction 13 (interpolation): Embed two jailbreaks, interpolate, decode, test. Check convexity of unsafe region in embedding space.
- **Negative predictions**: The theory predicts GPT-5-Mini (peak AD 0.50, basin rate 0%) should show *no* impossibility. Confirm this explicitly by showing that wrapper defenses actually succeed on it. A confirmed negative prediction is more convincing than 12 confirmed positive ones.

---

### 9. Software Library / Toolkit (Important Gap)

**Problem:** There is no software artifact that lets a practitioner *use* the theory. The Lean proofs verify the mathematics; they don't compute anything about real models.

**What's needed:**
- **`defense-trilemma` Python package** with:
  - `estimate_alignment_surface(model, prompts, judge)` → AD scores on a grid
  - `estimate_lipschitz(surface)` → $\hat{L}$ with confidence interval
  - `detect_boundaries(surface, tau)` → boundary point locations
  - `estimate_transversality(surface, boundary_points)` → $\hat{G}$ estimates
  - `compute_basin_stats(surface, tau)` → basin rate, fragment count, size distribution
  - `pareto_curve(surface)` → $\tau$ vs. $\mu(U_\tau)$
  - `predict_defense_bound(L, G, K, tau)` → guaranteed unsafe volume lower bound
  - `visualize_landscape(surface)` → 2D/3D plots of basins, boundaries, fragments
- **Integration with existing safety tooling**: HuggingFace Evaluate, HarmBench, SALAD-Bench APIs.

---

### 10. Open Problem List (Important Gap)

**Problem:** A field needs an explicit list of open problems that graduate students and postdocs can pick up. The paper doesn't have one.

**Suggested open problems:**

1. **Tight volume bound**: What is the exact minimum $\mu(\mathcal{S})$ as a function of $(L, G, K, d, \tau)$? The current bound is existence (positive measure). A tight bound would give quantitative predictions.

2. **Adaptive defense impossibility**: The current theorems assume a fixed defense $D$. Can an adaptive defense $D_t$ that updates after each interaction escape the trilemma? (The multi-turn theorem suggests no, but for a stronger adversary model.)

3. **Computational complexity of defense**: Given oracle access to $f$, what is the query complexity of computing an $\varepsilon$-optimal defense? Is it polynomial in $1/\varepsilon$ and $d$, or does it require exponential queries?

4. **Effective dimensionality**: What is the effective dimensionality $d$ of the alignment-relevant prompt manifold for current LLMs? Is it $\ll$ the token-space dimension? How does it scale with model size?

5. **Information-theoretic defense cost**: The grid-based cost asymmetry ($N^d$ vs. $1/\delta$) assumes exhaustive enumeration. What is the information-theoretic lower bound on defense cost (allowing arbitrary algorithms, not just grids)?

6. **Extension to output-space defenses**: The theorems cover input wrappers $D: X \to X$. Do analogous impossibilities hold for output filters $F: Y \to Y$? (The dual problem.)

7. **Quantitative alignment tax**: Prove a lower bound on capability loss as a function of safety improvement, using the theory's framework. Currently the alignment tax is empirically observed but not formally bounded.

8. **Escape conditions**: Characterize exactly which $(f, \tau, X)$ triples admit complete defenses. The counterexamples show disconnected $X$ or utility-sacrificing $D$ work. What is the full characterization?

9. **Stochastic defense tightness**: The stochastic impossibility shows $\mathbb{E}[f(D(z))] = \tau$ at boundary points. What is the minimum variance? Can randomization reduce the *probability* of unsafe output below any $\delta > 0$, even if the expectation is fixed?

10. **Multi-agent defense**: Multiple models reviewing each other's outputs (constitutional AI chains, debate protocols). Does the trilemma extend to the Nash equilibrium of multi-agent defense games?

---

### 11. Narrative and Naming (Polish Gap)

**Problem:** The repo uses two names ("Defense Trilemma" and "Manifold of Failure / Geometric Limits of Defense Design"). The field needs one name. Also:

- The term "alignment deviation" is good but not yet standard. You need the community to adopt it. Explicit comparison to existing metrics (ASR, harmfulness score, toxicity probability) showing why AD is better would help.
- The 14 predictions need to become a "prediction registry" — a living document that tracks which predictions are confirmed, by whom, and with what evidence. This is how a theoretical framework gains credibility over time (cf. the Standard Model prediction tracker in physics).
- The paper reads as a mathematics paper. For the ML safety community, a "tutorial" version that explains the intuitions without requiring topology background would dramatically lower the barrier to entry.

---

## Priority Ranking

| Priority | Gap | Reason |
|---|---|---|
| 🔴 **P0** | Measurement protocol + reference implementation | Without this, nobody can use the theory |
| 🔴 **P0** | Benchmark suite | Without this, nobody can compare |
| 🟠 **P1** | Estimation theory for $L$, $G$, $d$ | Without this, predictions are qualitative only |
| 🟠 **P1** | Constructive defense results | Without this, the theory doesn't help defenders |
| 🟡 **P2** | Defense taxonomy + reduction theorems | Without this, scope confusion limits adoption |
| 🟡 **P2** | Second-generation controlled experiments | Without this, confirmations are post-hoc only |
| 🟡 **P2** | Open problem list | Without this, no PhD students join |
| 🔵 **P3** | Software toolkit | Accelerates adoption |
| 🔵 **P3** | Connections to adjacent fields | Recruits researchers |
| 🔵 **P3** | Tight bounds | Theoretical completeness |
| ⚪ **P4** | Naming/narrative/tutorial | Community building |

---

## The One-Sentence Version

You have a **verified impossibility result with strong retrodictive power**. To turn it into a field, you need: **(1) a way to measure the quantities the theory is about**, **(2) a benchmark that operationalizes those measurements**, and **(3) constructive results that tell practitioners what to do, not just what they can't do**.

The impossibility is the spark. The measurement protocol is the kindling. The benchmark is the fire. The constructive theory is what keeps it burning.
