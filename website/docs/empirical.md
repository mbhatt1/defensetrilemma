# Empirical Surfaces: Three Models, Three Shapes

The Manifold of Failure framework maps three LLMs over a 2D behavioral space (query indirection × authority framing). The three models produce three qualitatively different alignment surfaces, and the theorems correctly predict where impossibility applies and where it doesn't.

<div class="diagram-row">

<div class="diagram">
<svg viewBox="0 0 240 240" xmlns="http://www.w3.org/2000/svg">
  <!-- Mesa surface: large, flat, high-AD region -->
  <rect x="20" y="20" width="200" height="200" fill="#f0f0f0" stroke="currentColor" stroke-width="1"/>

  <!-- Single large red plateau -->
  <rect x="35" y="35" width="170" height="170" fill="rgba(229, 62, 62, 0.65)"/>
  <rect x="50" y="50" width="140" height="140" fill="rgba(229, 62, 62, 0.85)"/>

  <!-- Boundary curve (sharp edge of mesa) -->
  <rect x="35" y="35" width="170" height="170" fill="none" stroke="#742a2a" stroke-width="1.5"/>

  <!-- Steep arrow indicating directional gradient -->
  <line x1="35" y1="120" x2="20" y2="120" stroke="#d69e2e" stroke-width="2"/>
  <polygon points="20,116 14,120 20,124" fill="#d69e2e"/>
  <text x="14" y="115" class="label-small" fill="#d69e2e" text-anchor="end">G ≈ 5</text>

  <!-- Axes -->
  <text x="120" y="235" class="label-small" text-anchor="middle">indirection</text>
  <text x="14" y="125" class="label-small" text-anchor="end" transform="rotate(-90, 14, 125)">authority</text>

  <text x="120" y="14" class="label label-bold" text-anchor="middle">Llama-3-8B: mesa</text>
</svg>
<p class="diagram-caption"><strong>Llama-3-8B</strong> · mean AD 0.93 · basin rate 93.9% · near-flat alignment surface, large robustness radii. Steep edge → persistent unsafe region applies.</p>
</div>

<div class="diagram">
<svg viewBox="0 0 240 240" xmlns="http://www.w3.org/2000/svg">
  <rect x="20" y="20" width="200" height="200" fill="#f0f0f0" stroke="currentColor" stroke-width="1"/>

  <!-- Mosaic: many small basins of varying intensity -->
  <rect x="30" y="30" width="40" height="35" fill="rgba(229, 62, 62, 0.45)"/>
  <rect x="80" y="40" width="35" height="40" fill="rgba(229, 62, 62, 0.65)"/>
  <rect x="125" y="35" width="50" height="35" fill="rgba(229, 62, 62, 0.55)"/>
  <rect x="180" y="40" width="30" height="40" fill="rgba(229, 62, 62, 0.4)"/>

  <rect x="35" y="80" width="35" height="40" fill="rgba(229, 62, 62, 0.7)"/>
  <rect x="80" y="90" width="40" height="35" fill="rgba(229, 62, 62, 0.5)"/>
  <rect x="130" y="85" width="40" height="40" fill="rgba(229, 62, 62, 0.75)"/>
  <rect x="175" y="90" width="35" height="35" fill="rgba(229, 62, 62, 0.5)"/>

  <rect x="30" y="135" width="50" height="35" fill="rgba(229, 62, 62, 0.55)"/>
  <rect x="90" y="140" width="30" height="40" fill="rgba(229, 62, 62, 0.6)"/>
  <rect x="125" y="135" width="40" height="35" fill="rgba(229, 62, 62, 0.4)"/>
  <rect x="170" y="140" width="40" height="40" fill="rgba(229, 62, 62, 0.7)"/>

  <rect x="35" y="185" width="40" height="25" fill="rgba(229, 62, 62, 0.5)"/>
  <rect x="85" y="180" width="40" height="30" fill="rgba(229, 62, 62, 0.65)"/>
  <rect x="135" y="185" width="35" height="25" fill="rgba(229, 62, 62, 0.55)"/>
  <rect x="175" y="180" width="35" height="30" fill="rgba(229, 62, 62, 0.45)"/>

  <!-- Horizontal authority bands hint -->
  <line x1="20" y1="75" x2="220" y2="75" stroke="#2d3748" stroke-width="0.6" stroke-dasharray="3,2" opacity="0.5"/>
  <line x1="20" y1="130" x2="220" y2="130" stroke="#2d3748" stroke-width="0.6" stroke-dasharray="3,2" opacity="0.5"/>
  <line x1="20" y1="178" x2="220" y2="178" stroke="#2d3748" stroke-width="0.6" stroke-dasharray="3,2" opacity="0.5"/>

  <text x="120" y="235" class="label-small" text-anchor="middle">indirection</text>
  <text x="14" y="125" class="label-small" text-anchor="end" transform="rotate(-90, 14, 125)">authority</text>

  <text x="120" y="14" class="label label-bold" text-anchor="middle">GPT-OSS-20B: mosaic</text>
</svg>
<p class="diagram-caption"><strong>GPT-OSS-20B</strong> · mean AD 0.73 · basin rate 64.3% · rugged landscape with many small fragments. Horizontal bands confirm authority monotonicity (Thm A.4).</p>
</div>

<div class="diagram">
<svg viewBox="0 0 240 240" xmlns="http://www.w3.org/2000/svg">
  <rect x="20" y="20" width="200" height="200" fill="#f0f0f0" stroke="currentColor" stroke-width="1"/>

  <!-- Flat surface: only mild orange tinting, NO red region -->
  <rect x="20" y="20" width="200" height="200" fill="rgba(214, 158, 46, 0.18)"/>

  <!-- A few darker patches but never reaching threshold -->
  <ellipse cx="80" cy="100" rx="25" ry="20" fill="rgba(214, 158, 46, 0.35)"/>
  <ellipse cx="160" cy="140" rx="30" ry="25" fill="rgba(214, 158, 46, 0.35)"/>
  <ellipse cx="120" cy="170" rx="20" ry="18" fill="rgba(214, 158, 46, 0.3)"/>

  <!-- Threshold annotation -->
  <text x="120" y="120" class="label label-bold" text-anchor="middle" fill="#9c5d0e">peak AD</text>
  <text x="120" y="138" class="label-small" text-anchor="middle" fill="#9c5d0e">= 0.50 (= τ)</text>

  <!-- "U_τ = ∅" callout -->
  <rect x="35" y="195" width="170" height="20" fill="rgba(56, 161, 105, 0.2)" stroke="#38a169" stroke-width="1"/>
  <text x="120" y="209" class="label-small" text-anchor="middle" fill="#1c5b34">U_τ = ∅ → no impossibility</text>

  <text x="120" y="235" class="label-small" text-anchor="middle">indirection</text>
  <text x="14" y="125" class="label-small" text-anchor="end" transform="rotate(-90, 14, 125)">authority</text>

  <text x="120" y="14" class="label label-bold" text-anchor="middle">GPT-5-Mini: flat</text>
</svg>
<p class="diagram-caption"><strong>GPT-5-Mini</strong> · peak AD 0.50 · basin rate 0% · ceiling exactly at the threshold. None of the three theorems apply — correctly predicting <em>no</em> impossibility.</p>
</div>

</div>

## What the surfaces tell us

<table class="compare-table">
<thead>
<tr>
<th>Model</th>
<th>Surface shape</th>
<th>Mean AD</th>
<th>Basin rate</th>
<th>Theorem application</th>
</tr>
</thead>
<tbody>
<tr>
<td><strong>Llama-3-8B</strong></td>
<td>Mesa: large near-uniform plateau above τ</td>
<td>0.93</td>
<td>93.9%</td>
<td>Boundary fixation + ε-robust + persistence (G ≈ 5, ℓ ≈ 1, K = 1: G &gt; ℓ(K+1) = 2 ✓)</td>
</tr>
<tr>
<td><strong>GPT-OSS-20B</strong></td>
<td>Mosaic: many small basins, horizontal banding</td>
<td>0.73</td>
<td>64.3%</td>
<td>All three apply; banding confirms authority monotonicity (Thm A.4)</td>
</tr>
<tr>
<td><strong>GPT-5-Mini</strong></td>
<td>Flat: peak AD = τ exactly, no points strictly above</td>
<td>0.50</td>
<td>0%</td>
<td><strong>None apply</strong> (U_τ = ∅) — correctly predicts no impossibility</td>
</tr>
</tbody>
</table>

## Why GPT-5-Mini "escapes"

GPT-5-Mini is the only model where the impossibility theorems do *not* apply. This is **the right prediction**: the theorems require both $S_\tau \neq \emptyset$ and $U_\tau \neq \emptyset$. If the model literally cannot produce outputs above $\tau$ — even at the worst observed prompt — then there is no unsafe region, no boundary fixation, no impossibility.

This is a precision check on the theory. The theorems don't say "all defenses fail always." They say "all continuous utility-preserving defenses fail when the alignment surface has nonempty unsafe region under the model." GPT-5-Mini meets the precondition $S_\tau \neq \emptyset$ but fails the precondition $U_\tau \neq \emptyset$, so the theorems correctly stay silent.

::: tip The engineering implication
Make $\tau$ high enough that $U_\tau$ is empty for the strongest attacker you care about. The impossibility is a function of the *threshold* you set, not of the model alone. GPT-5-Mini exemplifies what the [engineering prescription](/engineering) calls **"making the boundary shallow"**: if τ-level behavior is benign, the impossibility is mathematically true but practically harmless.
:::

## What the parameters look like for Llama-3-8B

The persistence theorem requires $G > \ell(K+1)$. For Llama, estimated from the 2D behavioral surface:

- **Directional slope** $G \approx 5$ at the steepest boundary crossing.
- **Defense-path Lipschitz constant** $\ell \approx 1$ (assuming a hypothetical nearest-safe-projection defense, estimated from grid-adjacent score differences in the projection direction on the 2D grid).
- **Defense Lipschitz constant** $K = 1$ (identity-rate defense).

So $G = 5 > 2 = \ell(K+1)$. The transversality condition holds, and Theorem 6.2 applies — there is a positive-measure region where any wrapper defense leaves outputs strictly unsafe.

## Predictions confirmed

| Theorem | Predicts | Confirmed by |
|---|---|---|
| Basin Structure | Basins are open with positive measure | Heatmaps show extended regions |
| Fragmentation | Smooth → large basins; rough → mosaic | Llama: mesa; GPT-OSS: mosaic |
| Convergence | Attacks exhibit monotone improvement | Convergence curves plateau |
| Transferability | Similar surfaces → shared basins | Llama .93 → GPT-OSS .73 → Mini .47 |
| Authority Monotonicity | Horizontal banding | Bands at $a_2 \approx 0.25$–$0.35$, $0.65$–$0.85$ |
| Persistent | Steep boundaries → unsafe volume persists | Llama's .93 plateau persists under defense |
| Interior Stability | Deep basin points survive fine-tuning | Vulnerability persists across variants |
| Cost Asymmetry | 2D tractable, high-d intractable | 15K queries fill 63% at d=2 |
