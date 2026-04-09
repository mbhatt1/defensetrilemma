# Textbook Plan: *The Geometry of LLM Safety*

**Working title:** *The Geometry of LLM Safety: Impossibility Theorems, Verified Proofs, and the Limits of Defense*

**Alternative titles:**
- *Defense Trilemma: A Mathematical Theory of LLM Safety Limits*
- *Why Wrappers Fail: The Topology and Geometry of Prompt Injection Defense*

---

## Key Decisions Up Front

### Audience
**Primary:** Graduate students and researchers in ML safety, adversarial robustness, and formal verification. People who read Madry et al., Carlini & Wagner, and Cohen et al. — and want to know what the analogous theory looks like for LLM defenses specifically.

**Secondary:** Senior ML engineers building defense systems at labs (Anthropic, OpenAI, Google DeepMind, etc.) who need to understand what their systems provably cannot do. Security researchers entering the LLM space.

**Not the audience (directly):** Undergraduates, policymakers, general public. But Part I should be accessible to anyone with linear algebra and basic topology.

### Prerequisites
- Linear algebra, basic real analysis (continuity, compactness, connectedness)
- Exposure to metric spaces and measure theory (can be reviewed in appendices)
- Basic ML background (what a language model is, what fine-tuning means)
- No Lean 4 experience needed (but Lean-literate readers get a bonus track)

### What makes this a textbook and not a long paper
1. **Self-contained mathematical development** — all prerequisites built from scratch
2. **Exercises** — ~15 per chapter, mix of proof exercises, computational exercises, and "connect to the literature" exercises
3. **Empirical chapters** — not just theory; chapters devoted to measurement, estimation, and experimental design
4. **Case studies** — extended examples applying the framework to real models and real defenses
5. **Open problems** — flagged throughout, collected in a final chapter
6. **Lean companion** — every major theorem linked to its verified proof, with a "Lean track" appendix for readers who want to follow the formalization

---

## Structure

### Part I: Foundations (Chapters 1–4)
*What the objects are. Self-contained. A motivated graduate student starts here.*

---

#### Chapter 1: The Defense Problem
**Pages: ~25 | Exercises: 12**

Why this book exists. The prompt injection problem stated precisely. What a wrapper defense is and why people build them.

- 1.1 Language models as functions: $M: X \to Y$
- 1.2 The wrapper defense model: $D: X \to X$ preprocessing inputs
- 1.3 Three desiderata: continuity, utility preservation, completeness
- 1.4 The trilemma informally: you can have any two
- 1.5 What's at stake: catalog of real-world defense systems and which class they belong to
  - Input classifiers (Alon et al.)
  - Constitutional rewriting (Bai et al.)
  - Input sanitization (Llama Guard, etc.)
  - Perplexity filters
  - Paraphrasing defenses
- 1.6 What the theorems do and do not cover
  - The explicit scope box: training-time, architectural, discontinuous, ensemble, human-in-the-loop defenses are NOT covered
  - The reduction question: when does a non-wrapper defense *behave like* a wrapper?
- 1.7 Historical context: adversarial examples, no-free-lunch, certified robustness
- 1.8 How to read this book (two tracks: theory-first vs. empirical-first)

**Exercises:** Classify 10 real defense systems into wrapper / non-wrapper. Show that a hard blocklist violates continuity. Show that mapping all inputs to a fixed safe point violates utility preservation. Show that a disconnected prompt space admits a complete defense.

---

#### Chapter 2: The Prompt Space
**Pages: ~30 | Exercises: 15**

The mathematical structure of the space where prompts live: topology, metric, measure. Why connectedness matters. Why the safe region is open but not closed.

- 2.1 Token sequences as a discrete space
- 2.2 Embedding spaces: why we work in $\mathbb{R}^d$
- 2.3 Connectedness and its consequences
  - Path-connectedness, simple connectedness
  - Why disconnected spaces are easy (Counterexample 1)
- 2.4 The alignment deviation function $f: X \to \mathbb{R}$
  - Operational definition: what does $f(x)$ measure?
  - Continuity as a modeling assumption: when is it justified?
  - The safe region $S_\tau = \{f < \tau\}$ is open
  - The unsafe region $U_\tau = \{f > \tau\}$ is open
  - The boundary $\partial = \{f = \tau\}$
- 2.5 The Hausdorff condition and its role
- 2.6 Lipschitz functions and regularity
  - The Lipschitz constant $L$ as a measure of surface roughness
  - Directional derivatives and transversality
- 2.7 Measure and volume on prompt spaces
- 2.8 The discrete-to-continuous bridge: Tietze extension
  - Finite behavioral observations → continuous interpolant
  - Why the impossibility applies to every extension

**Exercises:** Prove that $S_\tau$ is not closed in a connected space when both $S_\tau \neq \emptyset$ and $U_\tau \neq \emptyset$. Compute the boundary of $\{f > \tau\}$ for $f(x) = \|x\|^2$ on $\mathbb{R}^2$. Show that the Tietze extension preserves the existence of boundary crossings.

---

#### Chapter 3: Basin Geometry
**Pages: ~30 | Exercises: 15**

The shape of the unsafe region: basins, fragments, boundaries, and how they respond to perturbation.

- 3.1 Basins: connected components of $U_\tau$
  - Openness and positive measure (Thm Basin Structure)
  - The basin fragment minimum size: diameter $\geq 2(f(p) - \tau)/L$ (Thm Fragment)
  - Smooth surfaces → large basins; rough surfaces → many small fragments
- 3.2 The Lipschitz robustness ball: $B(p, (f(p)-\tau)/L) \subseteq U_\tau$
  - Every jailbreak has a neighborhood of jailbreaks
  - The ball radius is monotone in alignment deviation
- 3.3 Authority monotonicity and structured basins
  - When $f$ is monotone in one coordinate: upward-closed vulnerability sets
  - The critical threshold curve $a^*(y)$
  - Horizontal banding in behavioral heatmaps
- 3.4 Basin connectedness on convex domains
  - Quasiconcave $f$ → convex basins → single connected component
  - The interpolation corollary: linear interpolation between jailbreaks stays in $U_\tau$
- 3.5 Boundary dimension
  - The boundary is (at most) codimension-1
  - The boundary as a level set of $f$
- 3.6 Convergence of attacks
  - Monotone improvement → convergence in bounded steps
  - Step count $\leq \lfloor 1/\delta \rfloor$ for minimum gain $\delta$

**Exercises:** For $f(x,y) = x^2 + y^2$ on $[-1,1]^2$ with $\tau = 0.5$, compute basin rate, fragment count, and boundary. For a Lipschitz function with $L=10$ and peak AD of 0.8, compute the minimum basin diameter. Show that quasiconcavity implies the unsafe region is path-connected.

---

#### Chapter 4: Fixed Points and the Defense Map
**Pages: ~20 | Exercises: 10**

The properties of the defense $D$ that follow from utility preservation and continuity alone — before any impossibility.

- 4.1 The fixed-point set $\operatorname{Fix}(D) = \{x : D(x) = x\}$
  - Closed in Hausdorff spaces
  - Contains $\overline{S_\tau}$ under utility preservation
- 4.2 Defense as retraction
  - When $D$ is a retraction onto a subspace
  - Why non-contractiveness ($K \geq 1$) is forced by utility preservation on non-trivial spaces
- 4.3 The Lipschitz constant of the defense
  - $K$-Lipschitz: $d(D(x), D(y)) \leq K \cdot d(x,y)$
  - The displacement bound: $d(D(x), x) \leq (K+1) \cdot d(x, z)$
- 4.4 Score-preserving vs. input-preserving defenses
  - $f(D(x)) \leq f(x)$ for all $x$ (score-preserving: weaker than input-preserving)
  - When score-preservation suffices for the theorems
- 4.5 $\varepsilon$-relaxed utility preservation
  - $f(x) < \tau - \varepsilon \implies D(x) = x$
  - How much slack can you buy?

**Exercises:** Prove that the identity is the only $1$-Lipschitz utility-preserving defense on a convex safe region. Show that $\operatorname{Fix}(D)$ is closed in a Hausdorff space. Construct a defense with $K = 2$ on $[0,1]$ that fixes all of $[0, 0.5)$ and maps $[0.5, 1]$ to $[0, 0.4]$.

---

### Part II: The Impossibility Theorems (Chapters 5–9)
*The core results. Each chapter is one theorem or theorem family, with full proof, intuition, tightness analysis, and Lean reference.*

---

#### Chapter 5: Boundary Fixation
**Pages: ~30 | Exercises: 12**

The first impossibility: the defense must fix a boundary point.

- 5.1 The five-step proof
  - Step 1: $\operatorname{Fix}(D)$ is closed (Hausdorff)
  - Step 2: $S_\tau \subseteq \operatorname{Fix}(D)$, so $\overline{S_\tau} \subseteq \operatorname{Fix}(D)$ (utility preservation)
  - Step 3: $S_\tau$ is open but not closed (connectedness + both regions nonempty)
  - Step 4: $\exists z \in \overline{S_\tau} \setminus S_\tau$ with $f(z) = \tau$ (boundary point)
  - Step 5: $z \in \operatorname{Fix}(D)$, so $D(z) = z$ and $f(D(z)) = \tau$ (defense fixes it)
- 5.2 Why each hypothesis is necessary
  - Counterexample: disconnected $X$
  - Counterexample: discontinuous $D$
  - Counterexample: non-utility-preserving $D$
- 5.3 The Defense Trilemma as a corollary
- 5.4 Variants
  - Score-preserving defense: same conclusion
  - $\varepsilon$-relaxed utility: boundary point has $f(z) \leq \tau + \varepsilon$
- 5.5 What boundary fixation means in practice
  - The defense has a "blind spot" at the safety boundary
  - If boundary-level behavior is benign (polite refusal), the theorem is true but harmless
  - If boundary-level behavior is ambiguous, the blind spot is dangerous

**Lean track:** `defense_fixation`, `defense_trilemma_corollary` in `MoF_08_DefenseBarriers`

**Exercises:** Write out the full proof for a specific space ($[0,1]$ with $f(x) = x$, $\tau = 0.5$). Show that boundary fixation holds for score-preserving defenses. Prove that $\varepsilon$-relaxed utility preservation shifts the fixed point to $f(z) \leq \tau + \varepsilon$.

---

#### Chapter 6: The $\varepsilon$-Robust Constraint
**Pages: ~30 | Exercises: 12**

Adding Lipschitz structure: the failure spreads from a point to a band.

- 6.1 The constraint: $f(D(x)) \geq \tau - LK \cdot d(x, z)$
  - Proof: two applications of the Lipschitz condition
  - The $\delta$-band: inputs within distance $\delta$ of $z$ have $f(D(x)) \geq \tau - LK\delta$
- 6.2 Positive-measure $\varepsilon$-band
  - The band has positive measure (measure positive on open sets)
  - Quantitative: $\mu(\text{band}) \geq \mu(B(z, \delta))$ for $\delta = \varepsilon / (LK)$
- 6.3 The role of the Lipschitz constant $K$
  - Smaller $K$ → narrower band (gentler defense)
  - $K = 0$ (constant defense) eliminates the band but destroys utility
  - $K \to \infty$ → band covers the whole space
- 6.4 Interpreting the bound operationally
  - Near the blind spot, the defense "almost doesn't help"
  - How near is near? Depends on $LK$

**Lean track:** `epsilon_robust_defense`, `band_positive_measure` in `MoF_11_EpsilonRobust`

**Exercises:** For $L=5$, $K=2$, compute the band width needed for $f(D(x)) \geq \tau - 0.1$. Show that the $\varepsilon$-band is strictly larger than the fixed-point set. Prove that adding more defense layers (composing $D_1, D_2$) does not shrink the band.

---

#### Chapter 7: The Persistent Unsafe Region
**Pages: ~35 | Exercises: 15**

The strongest result: a positive-measure set stays strictly unsafe.

- 7.1 The transversality condition: $G > \ell(K+1)$
  - What it means: the alignment surface rises faster than the defense can pull it down
  - Global Lipschitz $L$ vs. defense-path constant $\ell$ vs. directional slope $G$
  - When does $G > \ell(K+1)$ hold? (steep boundaries + gentle defenses)
- 7.2 The input-relative bound (Lemma)
  - $f(D(x)) \geq f(x) - \ell(K+1) \cdot d(x, z)$
- 7.3 The persistent region $\mathcal{S}$
  - Definition: $\mathcal{S} = \{x : f(x) > \tau + \ell(K+1) \cdot d(x, z)\}$
  - $\mathcal{S}$ is open (superlevel set of a continuous function)
  - $\mathcal{S}$ has positive measure
  - For all $x \in \mathcal{S}$: $f(D(x)) > \tau$ (the defense fails)
- 7.4 Connecting transversality to derivatives
  - Directional derivative $c > \ell(K+1)$ at $z$ along $v$ → persistence
  - The Lean gap: derivative vs. linear growth condition (honest discussion)
  - How to close it: from derivative to local linear lower bound
- 7.5 When persistence fails
  - Isotropic surfaces ($\ell = L$): the steep region may be empty
  - Shallow boundaries: $G \leq \ell(K+1)$ everywhere → no persistence
  - The GPT-5-Mini escape: $U_\tau = \emptyset$
- 7.6 The gradient chain
  - If $\|\nabla f(z)\| > \ell(K+1)$, extract the direction and get persistence
- 7.7 The refined formulation
  - Using defense-path $\ell$ instead of global $L$
  - Why this matters: $\ell$ can be much smaller than $L$

**Lean track:** `persistent_unsafe_refined` in `MoF_20_RefinedPersistence`, `transversality_from_deriv` in `MoF_11`, `gradient_chain_persistence` in `MoF_21`

**Exercises:** Construct a specific $(f, D, \tau)$ where $\mathcal{S}$ is nonempty and compute its measure. Find a surface where $G > L(K+1)$ everywhere and compute $\mu(\mathcal{S})$. Prove that $\mathcal{S}$ shrinks as $K$ increases and compute the rate.

---

#### Chapter 8: Quantitative Bounds
**Pages: ~25 | Exercises: 10**

Volume bounds on how much fails: the coarea bound, cone bound, and the defense dilemma.

- 8.1 Volume lower bound via coarea inequality
  - $\mu(\mathcal{S}) \geq$ (explicit expression in $G, \ell, K, \delta$)
- 8.2 Cone measure bound
  - Conical region around the transversality direction $v$
- 8.3 The Defense Dilemma
  - $K < K^*$ → persistent unsafe region exists
  - $K \geq K^*$ → $\varepsilon$-band width $\geq G \cdot \delta$
  - $K^* = G/L - 1$: the critical defense constant
  - Both horns are achievable (realizability)
  - The dilemma is not an artifact: it's a genuine Pareto frontier
- 8.4 The optimal defense characterization
  - The tradeoff curve: band width vs. persistent volume as a function of $K$
  - Why the defender cannot escape both constraints simultaneously
- 8.5 Tightness: are the bounds best possible?
  - Which bounds are tight (with constructions)
  - Which bounds have gaps (open problems)

**Lean track:** `MoF_17_CoareaBound`, `MoF_18_ConeBound`, `MoF_19_OptimalDefense`

---

#### Chapter 9: The Discrete Theory
**Pages: ~25 | Exercises: 10**

Impossibility without topology: what happens on finite sets.

- 9.1 The Discrete IVT
- 9.2 The Discrete Defense Dilemma
  - Completeness + utility preservation → non-injectivity (information loss)
  - Injectivity + utility preservation → incompleteness
  - Completeness + injectivity → utility sacrifice
  - The three-way trilemma on finite sets
- 9.3 Capacity exhaustion
  - An injective defense that fixes all safe inputs uses up $|S_\tau|$ of its $|X|$ capacity on safe inputs, leaving $|X| - |S_\tau|$ outputs for $|U_\tau|$ unsafe inputs
  - If $|U_\tau| > |X| - |S_\tau|$... impossible
- 9.4 The continuous relaxation bridge
  - Tietze extension: discrete observations → continuous interpolant
  - The impossibility applies to every interpolant
  - Practical import: even if your prompt space is "really" discrete (token sequences), the continuous theory applies to any smooth approximation

**Lean track:** `MoF_12_Discrete`, `MoF_ContinuousRelaxation`

---

### Part III: Extensions (Chapters 10–13)
*Beyond the single-turn, deterministic, single-stage wrapper.*

---

#### Chapter 10: Multi-Turn Interactions
**Pages: ~25 | Exercises: 10**

- 10.1 The multi-turn model: defense applied at each turn
- 10.2 The impossibility recurs: if $S_\tau$ and $U_\tau$ are nonempty at any turn, boundary fixation holds at that turn
- 10.3 Attacker monotone improvement across turns
- 10.4 Attacker steering: IVT-based reachability of transversality via parameter tuning
- 10.5 Implications for conversational AI safety

#### Chapter 11: Stochastic Defenses
**Pages: ~25 | Exercises: 10**

- 11.1 Randomized defenses: $D(x)$ is a random variable
- 11.2 The expected alignment deviation: $g(x) = \mathbb{E}[f(D(x))]$
- 11.3 Stochastic defense impossibility: $g$ inherits continuity and utility preservation → boundary fixation on $g$
- 11.4 The stochastic dichotomy: at boundary points, either $f(D(z)) = \tau$ a.s. (deterministic), or $P(f(D(z)) > \tau) > 0$ (unsafe with positive probability)
- 11.5 Temperature sampling as stochastic defense
- 11.6 Stochastic regularity: what smoothing buys you (and what it can't)

#### Chapter 12: Pipelines and Agent Systems
**Pages: ~30 | Exercises: 12**

- 12.1 Nonlinear agent pipelines: $P = T_n \circ D_n \circ \cdots \circ T_1 \circ D_1$
- 12.2 Lipschitz composition: $K_{\text{pipeline}} = \prod K_i$
- 12.3 Pipeline impossibility: the failure band widens exponentially in depth
- 12.4 Tool calls as nonlinear transformations
- 12.5 Indirect prompt injection through the pipeline lens
- 12.6 Defense position invariance: $K_D \cdot K_T^n$ whether defense is first or last
- 12.7 Case study: a 5-tool RAG agent with defense wrappers at each stage

#### Chapter 13: The Meta-Theorem
**Pages: ~20 | Exercises: 8**

- 13.1 Regularity implies spillover: a representation-independent statement
- 13.2 What "regularity" captures: continuity, Lipschitz, finite capacity, any mechanism preventing the fixed-point set from equaling $S_\tau$ exactly
- 13.3 Unifying all paths through a single principle
- 13.4 The Master Theorem: complete formalization linking all major results

**Lean track:** `MoF_14_MetaTheorem`, `MoF_MasterTheorem`

---

### Part IV: The Empirical Side (Chapters 14–17)
*Measuring, estimating, testing, and applying the theory to real models.*

---

#### Chapter 14: Measuring Alignment Deviation
**Pages: ~30 | Exercises: 12**

This chapter does not yet exist in your materials. It is the single most important new content.

- 14.1 Operationalizing $f$: from mathematical object to measurement protocol
  - Option A: Probability of harmful completion under fixed generation settings
  - Option B: Continuous harm severity score from a calibrated judge
  - Option C: Classifier logit / confidence score
  - Option D: Human-rated harm on a continuous scale
  - Tradeoffs: reliability, cost, resolution, continuity assumption
- 14.2 Choosing a judge
  - LLM-as-judge (GPT-4, Claude) with rubric
  - Classifier-based (HarmBench, WildGuard)
  - Human evaluation and inter-rater reliability
  - Calibration: ensuring the judge's output is approximately continuous
- 14.3 Designing behavioral coordinates
  - The 2D grid (indirection × authority) from the companion paper
  - Extending to higher dimensions: what axes matter?
  - Principal components of the behavioral space
  - Embedding-based coordinates: using the model's own representation space
- 14.4 Sampling strategy
  - Grid-based: exhaustive but exponential
  - Adaptive: concentrate samples near detected boundaries
  - Random: cheap but coverage depends on basin rate
  - Latin hypercube / Sobol sequences for uniform coverage in high dimensions
- 14.5 Reference implementation sketch

#### Chapter 15: Estimating Defense-Theoretic Quantities
**Pages: ~30 | Exercises: 12**

Also mostly new. The statistical estimation chapter.

- 15.1 Estimating $L$ (Lipschitz constant)
  - Finite-difference estimators: $\hat{L} = \max_{i \neq j} |f(x_i) - f(x_j)| / d(x_i, x_j)$
  - Sample complexity: how many samples to estimate $L$ within factor $c$?
  - Bias: finite-difference estimators always underestimate $L$
  - Confidence intervals via extreme-value theory
- 15.2 Estimating $G$ (transversality slope)
  - Directional finite differences at detected boundary points
  - Estimating the direction of steepest ascent
  - Sample complexity near the boundary
- 15.3 Estimating basin rate and fragment count
  - Basin rate: $\hat{p} = |\{x_i : f(x_i) > \tau\}| / n$ with binomial confidence interval
  - Fragment count: connected component detection on sampled grid
  - The resolution problem: small fragments are invisible at coarse grids
- 15.4 Estimating effective dimensionality
  - Participation ratio of the Hessian of $f$
  - Intrinsic dimensionality estimators from the embedding space
  - Fractal dimension of the boundary
- 15.5 The Pareto curve $\tau \mapsto \mu(U_\tau)$
  - Estimation by threshold sweep
  - Smoothing and confidence bands
- 15.6 Checking the transversality condition: is $G > \ell(K+1)$?
  - Point estimate + confidence interval → hypothesis test
  - What to conclude when the condition is borderline

#### Chapter 16: Predictions and Experimental Tests
**Pages: ~35 | Exercises: 10**

The 14 predictions, their derivations, and the empirical evidence for each.

- 16.1 The prediction framework: theorem → instantiation → falsifiable claim → test
- 16.2 The 14 predictions (from your existing `derived-predictions.md` and `additional-predictions.md`), each with:
  - Source theorem
  - Derivation chain
  - Empirical evidence (from your research dossiers)
  - Verification status
  - Suggested controlled experiment
- 16.3 Confirmed predictions: what they tell us
- 16.4 Partially confirmed predictions: what's missing
- 16.5 The GPT-5-Mini negative prediction: why confirmed absence matters
- 16.6 Designing your own prediction: how to derive a new testable claim from the framework

#### Chapter 17: Case Studies
**Pages: ~30 | Exercises: 8**

Extended worked examples applying the full framework.

- 17.1 **Case Study: Llama-3-8B** — deep basins, flat surface, high basin rate. The impossibility theorems apply strongly. Estimate $L$, $G$, basin rate. Predict defense performance. Compare to observed.
- 17.2 **Case Study: GPT-OSS-20B** — fragmented landscape, moderate basins. The mosaic pattern and authority banding.
- 17.3 **Case Study: GPT-5-Mini** — shallow surface, $U_\tau = \emptyset$. The impossibility theorems don't apply. Why this model escapes.
- 17.4 **Case Study: A RAG agent pipeline** — 3-stage pipeline, estimating $K^3$, predicting indirect prompt injection success rate.
- 17.5 **Case Study: Model merging** — merging a vulnerable and a safe model at various ratios. Predicting jailbreak survival from Interior Stability.

---

### Part V: Constructive Theory and Open Frontiers (Chapters 18–21)
*What to do about it, and what we don't know yet.*

---

#### Chapter 18: The Engineering Prescription
**Pages: ~25 | Exercises: 10**

Translating impossibility into design principles.

- 18.1 Make the boundary shallow: training objectives that minimize peak AD
- 18.2 Reduce the Lipschitz constant: regularization during RLHF
- 18.3 Reduce the effective dimension: constrained prompt interfaces
- 18.4 Monitor, don't eliminate: runtime boundary detection
- 18.5 The cost-benefit framework: how much defense is enough?
  - Given $(L, G, d, \tau)$, compute the minimum residual unsafe volume
  - Compare residual risk to risk tolerance
  - Accept or invest in changing the model (not the wrapper)
- 18.6 When to give up on wrappers and change the model

#### Chapter 19: Toward Optimal Defenses
**Pages: ~25 | Exercises: 10**

Constructive results and what's known about the best achievable defense.

- 19.1 The defense Pareto frontier: band width vs. persistent volume vs. $K$
- 19.2 The nearest-safe-projection defense: $D(x) = \arg\min_{x' \in S_\tau} d(x, x')$
  - When this is optimal
  - Computational cost
- 19.3 Relaxed defenses: trading utility for safety
  - $\varepsilon$-utility sacrifice: $D(x)$ may differ from $x$ even when $f(x) < \tau - \varepsilon$
  - How much utility sacrifice buys how much safety gain
- 19.4 Ensemble defenses: when composition helps and when it hurts
- 19.5 Open problem: minimax optimal defense for given $(f, \tau, L, G)$

#### Chapter 20: Connections
**Pages: ~25 | Exercises: 8**

The framework's relationships to other fields.

- 20.1 Adversarial robustness: Tsipras et al., Fawzi et al., certified defenses
- 20.2 No-free-lunch: Wolpert & Macready, the structural analogy
- 20.3 Topological data analysis: persistent homology of basins
- 20.4 Game theory: the defense-attack game, Stackelberg equilibrium, cost asymmetry
- 20.5 Information theory: the discrete dilemma as lossy compression
- 20.6 Control theory: defense as control, alignment surface as plant, attacker as disturbance
- 20.7 Differential geometry: the alignment surface as a manifold, curvature and geodesics

#### Chapter 21: Open Problems
**Pages: ~15 | Exercises: 0 (these ARE the exercises)**

A curated list of open problems, organized by difficulty and topic.

- 21.1 Tight volume bounds ★★
- 21.2 Computational complexity of defense ★★★
- 21.3 Effective dimensionality of real prompt spaces ★★
- 21.4 Information-theoretic defense cost lower bounds ★★★
- 21.5 Output-space defense impossibility (the dual problem) ★★
- 21.6 Adaptive defense impossibility ★★★
- 21.7 Quantitative alignment tax lower bound ★★★
- 21.8 Multi-agent defense games ★★
- 21.9 Stochastic defense tightness ★★
- 21.10 Full characterization of defensible triples $(f, \tau, X)$ ★★★
- 21.11 Escape conditions: when is $U_\tau = \emptyset$ achievable by training? ★★★
- 21.12 Extension to output-side + input-side joint defenses ★★

---

### Appendices

#### Appendix A: Mathematical Background
- A.1 Metric spaces, open/closed sets, connectedness
- A.2 Continuity, compactness, Hausdorff spaces
- A.3 Lipschitz functions
- A.4 Measure theory essentials
- A.5 The intermediate value theorem and its relatives
- A.6 The Tietze extension theorem
- A.7 Convexity and quasiconcavity

#### Appendix B: The Lean 4 Companion
- B.1 What Lean is and why mechanical verification matters
- B.2 Reading Lean proofs (a tutorial)
- B.3 The artifact structure: 46 files, dependency graph
- B.4 How to build and verify: `lake build`
- B.5 Mapping paper theorems to Lean theorems (cross-reference table)
- B.6 The seven argument gaps (from the audit) and their status

#### Appendix C: Notation and Symbols

#### Appendix D: Complete Theorem Index
- Every theorem in the book with: name, number, page, Lean file, Lean name

---

## Metrics

| Item | Count |
|---|---|
| Chapters | 21 |
| Estimated pages | ~550–600 |
| Exercises | ~200 |
| Theorems proved | ~50 in text (300+ in Lean companion) |
| Case studies | 5 |
| Open problems | 12 |
| Predictions verified | 14 |

---

## What Exists vs. What Must Be Written

| Chapter | Material exists? | Work needed |
|---|---|---|
| 1 (Defense Problem) | Paper §1–2, research dossiers | Rewrite as exposition; add defense catalog |
| 2 (Prompt Space) | Paper §3, Lean MoF_01 | Expand; write the measurement sections |
| 3 (Basin Geometry) | Paper App A–D, Lean MoF_01–07 | Reorganize and expand with exercises |
| 4 (Fixed Points) | Paper §3–4, Lean MoF_08 | Write as standalone chapter |
| 5 (Boundary Fixation) | Paper §4, Lean MoF_08 | Expand proof exposition; add exercises |
| 6 ($\varepsilon$-Robust) | Paper §5, Lean MoF_11 | Expand |
| 7 (Persistent Region) | Paper §6, Lean MoF_11, 20, 21 | Significantly expand; address Lean gaps |
| 8 (Quantitative) | Paper §7, Lean MoF_17–19 | Expand |
| 9 (Discrete) | Paper §8, Lean MoF_12 | Expand |
| 10 (Multi-Turn) | Paper §9.1, Lean MoF_13 | Expand |
| 11 (Stochastic) | Paper §9.2, Lean MoF_13 | Expand |
| 12 (Pipelines) | Paper §9.3, Lean MoF_15 | Expand significantly; add case study |
| 13 (Meta-Theorem) | Lean MoF_14, MasterTheorem | Write narrative around Lean |
| 14 (Measuring AD) | **Does not exist** | Write from scratch |
| 15 (Estimation) | **Does not exist** | Write from scratch |
| 16 (Predictions) | `derived-predictions.md`, `prediction-verification.md` | Reorganize into chapter form |
| 17 (Case Studies) | Paper §9, companion paper | Expand into full case studies |
| 18 (Engineering) | Paper §10 | Expand significantly |
| 19 (Optimal Defense) | Lean MoF_19, partially | Mostly new |
| 20 (Connections) | **Does not exist** | Write from scratch |
| 21 (Open Problems) | `field-gap-analysis.md` partial | Formalize and expand |
| App A (Math Background) | **Does not exist** | Write from scratch |
| App B (Lean Companion) | `defense-trilemma-lean-audit-audit.md`, README | Reorganize |

**Bottom line:** ~40% of the content exists in some form. ~60% must be written from scratch, with the heaviest new writing in Part IV (empirical methods), Part V (constructive theory), and the appendices.

---

## Suggested Writing Order

The order that maximizes early usability and maintains momentum:

1. **Chapter 14 (Measuring AD)** — this is the P0 gap from the field analysis; it makes the rest testable
2. **Chapters 5–7 (core impossibility)** — the heart of the book; adapt from paper + Lean
3. **Chapter 1 (Defense Problem)** — the on-ramp; motivates everything
4. **Chapter 2–4 (foundations)** — prerequisites laid out cleanly
5. **Chapters 8–9 (quantitative + discrete)** — complete Part II
6. **Chapter 16 (predictions)** — the payoff chapter that connects theory to reality
7. **Chapters 10–13 (extensions)** — Part III
8. **Chapter 15 (estimation)** — statistical backbone for Part IV
9. **Chapter 17 (case studies)** — apply everything
10. **Chapters 18–21 (constructive + open)** — Part V
11. **Appendices** — last

---

## What the Book Accomplishes That the Paper Doesn't

1. **Teaches the prerequisites** — a reader with basic math can work through the theory from scratch
2. **Provides the measurement layer** — Chapters 14–15 create the empirical protocol that's missing
3. **Establishes the field infrastructure** — open problems, case studies, exercises, prediction registry
4. **Makes the Lean artifact accessible** — Appendix B + Lean Track throughout
5. **Goes constructive** — Chapters 18–19 tell practitioners what to *do*, not just what they can't
6. **Invites extension** — Chapter 20 (connections) and 21 (open problems) are explicit invitations
