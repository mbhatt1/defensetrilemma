---
layout: home

hero:
  name: The Defense Trilemma
  text: Continuity, utility, completeness — pick two.
  tagline: A geometric impossibility theorem for wrapper defenses on connected prompt spaces. Mechanically verified in Lean 4.
  actions:
    - theme: brand
      text: Walk through the proof →
      link: /boundary-proof
    - theme: alt
      text: Read the paper
      link: https://github.com/mbhatt1/stuff/blob/main/paper2_neurips.pdf

features:
  - icon: 🔵
    title: Boundary fixation
    details: Any continuous, utility-preserving defense on a connected space must leave at least one threshold-level prompt unchanged.
  - icon: 🟡
    title: ε-robust constraint
    details: Under Lipschitz regularity, a positive-measure band around fixed boundary points is constrained to near-threshold output.
  - icon: 🔴
    title: Persistent unsafe region
    details: Where the alignment surface rises faster than the defense can pull it down, a positive-measure region remains strictly unsafe.
---

<style scoped>
.hero-svg-wrap {
  max-width: 1100px;
  margin: 3rem auto 1rem;
  padding: 0 1.5rem;
}
</style>

<div class="hero-svg-wrap">

## The trilemma at a glance

<div class="diagram">

<svg viewBox="0 0 720 360" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <linearGradient id="triBg" x1="0%" y1="0%" x2="0%" y2="100%">
      <stop offset="0%" stop-color="rgba(176, 65, 62, 0.18)" />
      <stop offset="100%" stop-color="rgba(176, 65, 62, 0.05)" />
    </linearGradient>
  </defs>

  <!-- Triangle -->
  <polygon points="120,300 600,300 360,40" fill="url(#triBg)" stroke="currentColor" stroke-width="2" />

  <!-- Vertex labels -->
  <text x="120" y="325" class="label label-bold" text-anchor="middle">Continuity</text>
  <text x="600" y="325" class="label label-bold" text-anchor="middle">Utility Preservation</text>
  <text x="360" y="28" class="label label-bold" text-anchor="middle">Completeness</text>

  <!-- Edge labels -->
  <text x="360" y="318" class="label" text-anchor="middle" fill="#2b6cb0">
    Both ⇒ defense fixes the boundary  (our result)
  </text>
  <text x="195" y="170" class="label" text-anchor="end" fill="#38a169">
    Both ⇒
  </text>
  <text x="195" y="185" class="label" text-anchor="end" fill="#38a169">
    destroys utility
  </text>
  <text x="525" y="170" class="label" text-anchor="start" fill="#c53030">
    Both ⇒
  </text>
  <text x="525" y="185" class="label" text-anchor="start" fill="#c53030">
    discontinuous jump
  </text>

  <!-- Center label -->
  <text x="360" y="200" class="label label-bold" text-anchor="middle" font-style="italic">
    All three
  </text>
  <text x="360" y="218" class="label label-bold" text-anchor="middle" font-style="italic">
    simultaneously
  </text>
  <text x="360" y="236" class="label label-bold" text-anchor="middle" font-style="italic">
    impossible
  </text>
</svg>

<p class="diagram-caption">
  The defense trilemma. A continuous wrapper <code>D: X → X</code> on a connected prompt space can satisfy at most two of the three properties.
</p>
</div>

## The three impossibility levels

Each level adds hypotheses to the previous one and reaches a strictly stronger conclusion.

<div class="diagram-row">

<div class="diagram">
<svg viewBox="0 0 280 220" xmlns="http://www.w3.org/2000/svg">
  <!-- Axes -->
  <line x1="20" y1="190" x2="260" y2="190" class="axis" />
  <line x1="20" y1="20" x2="20" y2="190" class="axis" />
  <text x="265" y="195" class="label-small">x</text>
  <text x="15" y="15" class="label-small">f(x)</text>

  <!-- Threshold line -->
  <line x1="20" y1="110" x2="260" y2="110" class="threshold" />
  <text x="14" y="113" class="label-small" text-anchor="end">τ</text>

  <!-- Safe shading -->
  <rect x="20" y="110" width="120" height="80" class="safe-fill" />

  <!-- f curve passing through (140, 110) -->
  <path d="M 20,170 Q 80,140 140,110 T 260,40" class="curve" />

  <!-- Fixed boundary point z -->
  <circle cx="140" cy="110" r="4.5" class="point" />
  <text x="146" y="125" class="label-small">z (fixed)</text>

  <text x="140" y="14" class="label label-bold" text-anchor="middle">(a) Boundary Fixation</text>
</svg>
<p class="diagram-caption">Defense must fix at least one boundary point z with f(z) = τ.</p>
</div>

<div class="diagram">
<svg viewBox="0 0 280 220" xmlns="http://www.w3.org/2000/svg">
  <line x1="20" y1="190" x2="260" y2="190" class="axis" />
  <line x1="20" y1="20" x2="20" y2="190" class="axis" />
  <line x1="20" y1="110" x2="260" y2="110" class="threshold" />
  <text x="14" y="113" class="label-small" text-anchor="end">τ</text>

  <rect x="20" y="110" width="120" height="80" class="safe-fill" />

  <!-- ε-band: rectangle around z -->
  <rect x="80" y="80" width="120" height="50" class="band-fill" />

  <path d="M 20,170 Q 80,140 140,110 T 260,40" class="curve" />
  <circle cx="140" cy="110" r="4.5" class="point" />

  <!-- Bracket -->
  <line x1="80" y1="200" x2="200" y2="200" stroke="#b7791f" stroke-width="1.5"/>
  <line x1="80" y1="196" x2="80" y2="204" stroke="#b7791f" stroke-width="1.5"/>
  <line x1="200" y1="196" x2="200" y2="204" stroke="#b7791f" stroke-width="1.5"/>
  <text x="140" y="215" class="label-small" fill="#b7791f" text-anchor="middle">δ-neighborhood</text>

  <text x="225" y="98" class="label-small" fill="#b7791f">ε-band</text>

  <text x="140" y="14" class="label label-bold" text-anchor="middle">(b) ε-Robust Constraint</text>
</svg>
<p class="diagram-caption">Near z, |f(D(x)) − τ| ≤ LK·dist(x,z): defense is constrained on a positive-measure band.</p>
</div>

<div class="diagram">
<svg viewBox="0 0 280 220" xmlns="http://www.w3.org/2000/svg">
  <line x1="20" y1="190" x2="260" y2="190" class="axis" />
  <line x1="20" y1="20" x2="20" y2="190" class="axis" />
  <line x1="20" y1="110" x2="260" y2="110" class="threshold" />
  <text x="14" y="113" class="label-small" text-anchor="end">τ</text>

  <rect x="20" y="110" width="120" height="80" class="safe-fill" />

  <!-- Defense budget cone -->
  <line x1="140" y1="110" x2="260" y2="60" class="cone-line" />

  <!-- f curve rises ABOVE the cone past z -->
  <path d="M 20,170 Q 80,140 140,110 Q 180,80 260,30" class="curve" />

  <!-- Persistent region between curve and cone -->
  <path d="M 140,110 Q 180,80 260,30 L 260,60 Z" class="persistent-fill" />

  <circle cx="140" cy="110" r="4.5" class="point" />

  <text x="220" y="58" class="label-small" fill="#d69e2e">τ + ℓ(K+1)δ</text>
  <text x="220" y="78" class="label-small" fill="#c53030">𝒮: stays unsafe</text>

  <text x="140" y="14" class="label label-bold" text-anchor="middle">(c) Persistent Region</text>
</svg>
<p class="diagram-caption">Where f rises faster than the defense's Lipschitz budget, the unsafe region survives.</p>
</div>

</div>

## What this site contains

This is a diagrammatic walkthrough of the **Defense Trilemma** paper. Each page focuses on one diagram from the paper and unpacks what it means.

| Page | What it shows |
|---|---|
| [2D Prompt Space](/prompt-space) | The geometric setup: safe region, unsafe region, boundary, defense map |
| [Boundary Fixation Proof](/boundary-proof) | The five-step argument as two converging chains |
| [Three-Level Hierarchy](/hierarchy) | How each theorem strengthens the previous one |
| [The K Dilemma](/dilemma) | Why no choice of defense Lipschitz constant escapes both failure modes |
| [Discrete Dilemma](/discrete) | The same theorem on finite sets, no topology |
| [Extensions](/extensions) | Multi-turn, stochastic, and pipeline failure modes |
| [Empirical Surfaces](/empirical) | Three real LLMs: mesa, mosaic, flat |
| [Counterexamples](/counterexamples) | Each hypothesis is necessary |
| [Engineering Prescription](/engineering) | What to do when elimination is impossible |
| [Lean Artifact](/lean-artifact) | The 45-file mechanically verified proof |

</div>
