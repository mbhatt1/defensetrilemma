# The Lean Artifact

The complete theory is mechanically verified in Lean 4 with Mathlib. **45 files, ~350 theorems, zero `sorry` statements, three standard axioms** (`propext`, `Classical.choice`, `Quot.sound`).

[**View on GitHub →**](https://github.com/mbhatt1/stuff/tree/main/ManifoldProofs)

<div class="diagram">

<svg viewBox="0 0 800 540" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="larr" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#b0413e" />
    </marker>
  </defs>

  <!-- Capstone at top -->
  <rect x="280" y="20" width="240" height="50" rx="8" fill="rgba(176, 65, 62, 0.18)" stroke="#b0413e" stroke-width="2" />
  <text x="400" y="42" class="label label-bold" text-anchor="middle">MoF_MasterTheorem</text>
  <text x="400" y="58" class="label-small" text-anchor="middle">capstone: assembles all results</text>

  <!-- Arrows down to four cluster -->
  <line x1="400" y1="72" x2="120" y2="105" stroke="#b0413e" stroke-width="1.5" opacity="0.6"/>
  <line x1="400" y1="72" x2="295" y2="105" stroke="#b0413e" stroke-width="1.5" opacity="0.6"/>
  <line x1="400" y1="72" x2="500" y2="105" stroke="#b0413e" stroke-width="1.5" opacity="0.6"/>
  <line x1="400" y1="72" x2="680" y2="105" stroke="#b0413e" stroke-width="1.5" opacity="0.6"/>

  <!-- Cluster 1: core theory MoF_01-10 -->
  <rect x="40" y="105" width="180" height="200" rx="8" fill="rgba(43, 108, 176, 0.08)" stroke="#2b6cb0" stroke-width="1.5"/>
  <text x="130" y="125" class="label label-bold" text-anchor="middle" fill="#2b6cb0">Core Theory</text>
  <text x="130" y="142" class="label-small" text-anchor="middle">MoF_01–MoF_10 (10 files)</text>

  <text x="50" y="165" class="label-small">01 Foundations</text>
  <text x="50" y="180" class="label-small">02 Basin Structure</text>
  <text x="50" y="195" class="label-small">03 Threshold Crossing</text>
  <text x="50" y="210" class="label-small">04 Lipschitz Basin</text>
  <text x="50" y="225" class="label-small">05 Monotone Convergence</text>
  <text x="50" y="240" class="label-small">06 Transferability</text>
  <text x="50" y="255" class="label-small">07 Authority Monotonicity</text>
  <text x="50" y="270" class="label-small">08 Defense Barriers</text>
  <text x="50" y="285" class="label-small">09 Dimensional Scaling</text>
  <text x="50" y="300" class="label-small">10 Gradient Attack</text>

  <!-- Cluster 2: extensions MoF_11-20 -->
  <rect x="240" y="105" width="180" height="240" rx="8" fill="rgba(214, 158, 46, 0.08)" stroke="#d69e2e" stroke-width="1.5"/>
  <text x="330" y="125" class="label label-bold" text-anchor="middle" fill="#9c5d0e">Extensions</text>
  <text x="330" y="142" class="label-small" text-anchor="middle">MoF_11–MoF_20 (10 files)</text>

  <text x="250" y="165" class="label-small">11 ε-Robust ★</text>
  <text x="250" y="180" class="label-small">12 Discrete</text>
  <text x="250" y="195" class="label-small">13 Multi-Turn + Stochastic</text>
  <text x="250" y="210" class="label-small">14 Meta-Theorem</text>
  <text x="250" y="225" class="label-small">15 Nonlinear Agents</text>
  <text x="250" y="240" class="label-small">16 Relaxed Utility</text>
  <text x="250" y="255" class="label-small">17 Coarea Bound</text>
  <text x="250" y="270" class="label-small">18 Cone Bound</text>
  <text x="250" y="285" class="label-small">19 Optimal Defense</text>
  <text x="250" y="300" class="label-small">20 Refined Persistence ★</text>
  <text x="250" y="325" class="label-small" font-style="italic" fill="#9c5d0e">★ = Theorems 5.1, 6.2</text>

  <!-- Cluster 3: cost theory -->
  <rect x="440" y="105" width="180" height="200" rx="8" fill="rgba(56, 161, 105, 0.08)" stroke="#38a169" stroke-width="1.5"/>
  <text x="530" y="125" class="label label-bold" text-anchor="middle" fill="#1c5b34">Cost Theory</text>
  <text x="530" y="142" class="label-small" text-anchor="middle">MoF_Cost_01–10 (10 files)</text>

  <text x="450" y="165" class="label-small">01 Ball Volume</text>
  <text x="450" y="180" class="label-small">02 Basin Volume</text>
  <text x="450" y="195" class="label-small">03 Hitting Time</text>
  <text x="450" y="210" class="label-small">04 Concentration</text>
  <text x="450" y="225" class="label-small">05 Attack Cost</text>
  <text x="450" y="240" class="label-small">06 Defense Cost</text>
  <text x="450" y="255" class="label-small">07 Transfer Cost</text>
  <text x="450" y="270" class="label-small">08 Cost Ratio</text>
  <text x="450" y="285" class="label-small">09 Lipschitz Estimation</text>
  <text x="450" y="300" class="label-small">10 Unified Theory</text>

  <!-- Cluster 4: advanced -->
  <rect x="640" y="105" width="140" height="200" rx="8" fill="rgba(176, 65, 62, 0.08)" stroke="#b0413e" stroke-width="1.5"/>
  <text x="710" y="125" class="label label-bold" text-anchor="middle" fill="#742a2a">Advanced</text>
  <text x="710" y="142" class="label-small" text-anchor="middle">MoF_Adv_01–10 (10 files)</text>

  <text x="650" y="165" class="label-small">01 Connectedness</text>
  <text x="650" y="180" class="label-small">02 Boundary Dim</text>
  <text x="650" y="195" class="label-small">03 Fine-Tuning</text>
  <text x="650" y="210" class="label-small">04 Model Scale</text>
  <text x="650" y="225" class="label-small">05 Convexity</text>
  <text x="650" y="240" class="label-small">06 Approximation</text>
  <text x="650" y="255" class="label-small">07 Fragmentation</text>
  <text x="650" y="270" class="label-small">08 Stability</text>
  <text x="650" y="285" class="label-small">09 OptLandscape</text>
  <text x="650" y="300" class="label-small">10 MeasureBounds</text>

  <!-- Bottom: support files -->
  <rect x="40" y="380" width="740" height="135" rx="8" fill="rgba(0,0,0,0.04)" stroke="currentColor" stroke-width="1" stroke-dasharray="3,3"/>
  <text x="410" y="400" class="label label-bold" text-anchor="middle">Support and verification (5 files)</text>

  <text x="60" y="425" class="label-small">• MoF_ContinuousRelaxation — Tietze extension bridge from discrete to continuous</text>
  <text x="60" y="442" class="label-small">• MoF_FinalVerification — final axiom check, depends-on tracking</text>
  <text x="60" y="459" class="label-small">• MoF_Instantiation_Euclidean — concrete instantiation in ℝⁿ</text>
  <text x="60" y="476" class="label-small">• ManifoldProofs.lean — root import file</text>
  <text x="60" y="493" class="label-small">• MoF_MasterTheorem.lean — capstone (shown at top)</text>

  <text x="410" y="530" class="label-small" text-anchor="middle" font-style="italic">~350 theorems · 0 sorry · 3 axioms (propext, Classical.choice, Quot.sound)</text>
</svg>

<p class="diagram-caption">
  The 45-file Lean artifact organized into four clusters with a top-level capstone. Theorems 5.1 (ε-Robust) and 6.2 (Persistent Unsafe Region) live in MoF_11 and MoF_20 respectively (marked ★).
</p>

</div>

## How the paper's theorems map to Lean files

| Paper theorem | Lean file | Lean theorem name |
|---|---|---|
| Thm 4.1 (Boundary Fixation) | `MoF_11_EpsilonRobust.lean` | `epsilon_robust_impossibility` (existence portion) |
| Thm 5.1 (ε-Robust Constraint) | `MoF_11_EpsilonRobust.lean` | `defense_output_near_threshold` |
| Thm 5.2 (Positive-Measure Band) | `MoF_11_EpsilonRobust.lean` | `epsilonBand_contains_ball` |
| Lemma 6.1 (Input-Relative Bound) | `MoF_20_RefinedPersistence.lean` | `defense_from_input_bound_refined` |
| Thm 6.2 (Persistent Unsafe Region) | `MoF_20_RefinedPersistence.lean` | `persistent_unsafe_refined` |
| Thm 7.1 (Volume Lower Bound) | `MoF_17_CoareaBound.lean` | `epsilonBand_measure_pos` |
| Thm 7.2 (Cone Measure Bound) | `MoF_18_ConeBound.lean` | `cone_measure_bound` |
| Thm 7.3 (Defense Dilemma) | `MoF_19_OptimalDefense.lean` | `optimal_K_exists`, `defense_cannot_win` |
| Thm 8.2 (Discrete Dilemma) | `MoF_12_Discrete.lean` | `discrete_defense_dilemma` |
| Thm 9.1 (Multi-Turn) | `MoF_13_MultiTurn.lean` | `multi_turn_impossibility` |
| Thm 9.2 (Stochastic) | `MoF_13_MultiTurn.lean` | `stochastic_defense_impossibility` |
| Thm 9.4 (Pipeline) | `MoF_15_NonlinearAgents.lean` | `pipeline_impossibility` |
| Thm A.6 (Crossing Preservation) | `MoF_Adv_08_Stability.lean` | `perturbed_crossing_ivt` |
| Thm A.6.1 (Cost Asymmetry) | `MoF_Cost_08_CostRatio.lean` | `defense_cost_exponential` |

## Reproducing the build

```bash
git clone https://github.com/mbhatt1/stuff.git
cd stuff/ManifoldProofs
lake build
```

Expected output: `Build completed successfully (8071 jobs).`

The build uses Lean 4.28.0 + Mathlib v4.28.0. Total verification time on a modern laptop: roughly 5–10 minutes for a fresh build (mostly Mathlib dependencies); subsequent incremental builds are fast.

## What "0 sorry" means

`sorry` is Lean's placeholder for an unproven proposition. A file containing `sorry` will compile, but the theorem it appears in is *not actually proved* — `sorry` lets you assume any goal. The artifact has zero of these. Every theorem statement listed above is a complete formal proof from the Mathlib axioms.

## What the three axioms are

Lean 4's logic is dependent type theory, and three axioms are standard in Mathlib:

1. **`propext`** (propositional extensionality): two propositions that imply each other are equal as propositions.
2. **`Classical.choice`** (axiom of choice): standard set-theoretic choice.
3. **`Quot.sound`** (quotient soundness): equal representatives in a quotient type are propositionally equal.

These are the same axioms used by all of Mathlib. No additional axioms specific to this paper.

## Why mechanically verify?

The paper makes mathematical claims about the impossibility of an entire class of defenses. The strength of the conclusion is proportional to confidence in the proof. Mechanical verification removes:

- **Errors in the proof** that wouldn't be caught by human review.
- **Ambiguity** about what exactly was proved (the Lean statement is the theorem, period).
- **Hidden dependencies** on unstated assumptions (the axiom check makes them explicit).

This matters more here than for typical mathematics, because the claim is *negative* — "no defense exists with these properties." Such claims are easy to undermine if even one corner case slips through informal review.

→ Back to the [trilemma overview](/) or read the [paper](https://github.com/mbhatt1/stuff/blob/main/paper2_neurips.pdf).
