# The K Dilemma

The defense designer chooses the Lipschitz constant $K$ of the defense map $D$. Two competing forces pull in opposite directions: small $K$ means a *gentle* defense that cannot remap points far enough; large $K$ means an *aggressive* defense whose ε-band swells without limit. There is a critical $K^* = G/\ell - 1$ where both failure modes are sharp.

<div class="diagram">

<svg viewBox="0 0 760 400" xmlns="http://www.w3.org/2000/svg">
  <!-- Axes -->
  <line x1="80" y1="340" x2="720" y2="340" class="axis" />
  <line x1="80" y1="60" x2="80" y2="340" class="axis" />

  <!-- X-axis label -->
  <text x="400" y="380" class="label label-bold" text-anchor="middle">Defense Lipschitz constant K</text>

  <!-- Y-axis label -->
  <text x="30" y="200" class="label label-bold" text-anchor="middle" transform="rotate(-90, 30, 200)">"Cost" of failure</text>

  <!-- K* vertical line -->
  <line x1="400" y1="60" x2="400" y2="340" stroke="#b0413e" stroke-width="1.5" stroke-dasharray="5,4" />
  <text x="400" y="55" class="label label-bold" text-anchor="middle" fill="#b0413e">K* = G/ℓ − 1</text>

  <!-- Persistent region cost: high for small K, drops to 0 at K* -->
  <path d="M 80,90 Q 200,100 300,180 T 400,340 L 400,340" fill="none" stroke="#c53030" stroke-width="3" />
  <text x="180" y="120" class="label label-bold" fill="#c53030">persistent region size</text>
  <text x="180" y="138" class="label-small" fill="#c53030">G − ℓ(K+1)</text>

  <!-- Band width: linear, low for small K -->
  <path d="M 80,310 L 400,200 L 720,90" fill="none" stroke="#d69e2e" stroke-width="3" />
  <text x="600" y="120" class="label label-bold" fill="#d69e2e" text-anchor="end">ε-band width</text>
  <text x="600" y="138" class="label-small" fill="#d69e2e" text-anchor="end">LK · δ</text>

  <!-- Failure regions -->
  <rect x="80" y="345" width="320" height="14" fill="rgba(229, 62, 62, 0.25)" />
  <text x="240" y="354" class="label-small" text-anchor="middle" fill="#742a2a">Horn 1: persistent unsafe region</text>

  <rect x="400" y="345" width="320" height="14" fill="rgba(214, 158, 46, 0.25)" />
  <text x="560" y="354" class="label-small" text-anchor="middle" fill="#9c5d0e">Horn 2: ε-band blown up</text>

  <!-- Sweet spot annotation -->
  <circle cx="400" cy="200" r="5" fill="#b0413e" />
  <text x="410" y="205" class="label label-bold" fill="#b0413e">tightest tradeoff</text>

  <!-- Gentle / Aggressive labels -->
  <text x="180" y="320" class="label-small" font-style="italic" fill="#742a2a">"too gentle"</text>
  <text x="600" y="320" class="label-small" font-style="italic" fill="#9c5d0e">"too aggressive"</text>

  <!-- K=0 marker -->
  <text x="80" y="360" class="label-small" text-anchor="middle">0</text>
</svg>

<p class="diagram-caption">
  The two failure modes as functions of K. Below K* the persistent unsafe region exists (red horn). Above K* the ε-band that the defense cannot push below threshold widens linearly (yellow horn). At exactly K = K*, both failure modes meet at a finite, irreducible cost.
</p>

</div>

<div class="thm">
<div class="thm-title">Theorem 7.3 — Defense Dilemma</div>

Assume $f$ is differentiable at boundary point $z$ with directional gradient $G = \|\nabla f(z)\|$, and let $\ell$ be the defense-path Lipschitz constant. Define $K^* = G/\ell - 1$. Then:

1. **If $K < K^*$:** the persistent unsafe region exists ($G > \ell(K+1)$, Theorem 6.2 applies).
2. **If $K \geq K^*$:** the ε-robust bound $\tau - \ell(K+1)\delta$ becomes loose enough that the theorem can no longer exclude the defense from succeeding on the steep region.

Since $\ell \leq L$, the dilemma is sharpest when $\ell \ll L$ (anisotropic surfaces).
</div>

## The two horns, intuitively

<div class="three-card">

<div class="card">
<h4>Horn 1: K too small</h4>
<p>A gentle defense barely moves anything. Mathematically: $\dist(D(x), x) \leq K \cdot \dist(x, z)$ is small. Geometrically: the defense's "reach" is short. If $f$ rises steeply away from $z$, the defense cannot pull steep points back below $\tau$ — they stay above. <strong>A positive-measure set remains strictly unsafe.</strong></p>
</div>

<div class="card">
<h4>Horn 2: K too large</h4>
<p>An aggressive defense moves things far. Mathematically: $D(x)$ can land anywhere within $K \cdot \dist(x, z)$ of itself. But the constrained ε-band scales as $LK\delta$ — so widening $K$ widens the band of points the defense cannot push <em>far</em> below $\tau$. <strong>An arbitrarily wide band of near-threshold outputs.</strong></p>
</div>

<div class="card">
<h4>K = K*: tightest tradeoff</h4>
<p>At exactly $K^* = G/\ell - 1$, the persistence condition $G > \ell(K+1)$ becomes $G > G$ — barely failing. The persistent region disappears, but the ε-band has reached its minimum non-zero width. This is the <em>least-bad</em> defense: still constrained, but no longer leaving strictly unsafe volume.</p>
</div>

</div>

## When the dilemma is sharp

The dilemma is sharpest when the alignment surface is **anisotropic**: $f$ rises steeply in some directions ($G$ large) but is smooth along the directions the defense actually pulls in ($\ell$ small).

This is exactly what's observed empirically. On the [Llama-3-8B surface](/empirical), $G \approx 5$ at the steepest boundary crossing while $\ell \approx 1$ along the projection direction. So $K^* = 5/1 - 1 = 4$, and the defense designer's choices are:

- $K < 4$: persistent unsafe region exists (from steep-direction gradient).
- $K \geq 4$: ε-band of width $\geq 5 \cdot \delta$ around $z$.

::: warning When the dilemma vanishes
If the alignment surface is **isotropic** ($\ell = L$), then $K^* = G/L - 1 \leq 0$ (since $G \leq L$ for any L-Lipschitz $f$). The persistent-unsafety horn becomes vacuous, and a defense with any $K \geq 0$ avoids Horn 1 by default. This is verified in Lean as `shallow_boundary_no_persistence` — but it's a vacuous escape: the result is non-trivial precisely on anisotropic surfaces, which is the realistic case.
:::

## The cost-benefit summary

For any defense with Lipschitz constant $K$:

| Quantity | Formula | Behavior in $K$ |
|---|---|---|
| Persistent region condition | $G > \ell(K+1)$ | Holds for $K < K^*$ |
| Critical $K^*$ | $G/\ell - 1$ | Larger when $G/\ell$ is larger (anisotropic) |
| ε-band depth bound | $LK \cdot \delta$ | Linear in $K$, no upper limit |
| Persistent set size lower bound | $\delta_0$ from cone bound | Positive whenever Horn 1 active |

→ The discrete version of this same dilemma — without any topology — is on the [discrete dilemma page](/discrete).
