# The Three-Level Hierarchy

The paper's three impossibility theorems form a strict hierarchy: each adds hypotheses to the previous one and reaches a strictly stronger conclusion. The same fixed boundary point $z$ from Theorem 4.1 is reused as the geometric anchor for the next two levels.

<div class="diagram">

<svg viewBox="0 0 760 460" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="arr2" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#b0413e" />
    </marker>
  </defs>

  <!-- LEVEL 1 -->
  <rect x="20" y="40" width="720" height="115" rx="10" fill="rgba(56, 161, 105, 0.08)" stroke="#38a169" stroke-width="2" />
  <text x="40" y="65" class="label label-bold" fill="#1c5b34" font-size="13">Level 1 — Boundary Fixation (Thm 4.1)</text>

  <text x="40" y="88" class="label-small">Hypotheses:</text>
  <text x="125" y="88" class="label-small">connected Hausdorff X · continuous f, D · D|_S = id</text>

  <text x="40" y="108" class="label-small">Conclusion:</text>
  <text x="125" y="108" class="label-small">∃ z with f(z) = τ and D(z) = z   (one fixed boundary point — measure zero)</text>

  <text x="40" y="135" class="label-small" font-style="italic" fill="#38a169">Pure topology · 50 lines of Lean</text>
  <text x="500" y="135" class="label" text-anchor="end" font-style="italic" fill="#38a169">strength: existence</text>

  <!-- Arrow down: + Lipschitz -->
  <line x1="380" y1="160" x2="380" y2="180" stroke="#b0413e" stroke-width="2.5" marker-end="url(#arr2)" />
  <text x="395" y="174" class="label-small" font-style="italic">+ Lipschitz hypothesis</text>

  <!-- LEVEL 2 -->
  <rect x="20" y="185" width="720" height="115" rx="10" fill="rgba(246, 173, 85, 0.12)" stroke="#d69e2e" stroke-width="2" />
  <text x="40" y="210" class="label label-bold" fill="#9c5d0e" font-size="13">Level 2 — ε-Robust Constraint (Thm 5.1)</text>

  <text x="40" y="233" class="label-small">Adds:</text>
  <text x="125" y="233" class="label-small">(X, d) is a metric space · f is L-Lipschitz · D is K-Lipschitz</text>

  <text x="40" y="253" class="label-small">Conclusion:</text>
  <text x="125" y="253" class="label-small">f(D(x)) ≥ τ − LK · dist(x, z)   (a positive-measure band near z is constrained)</text>

  <text x="40" y="280" class="label-small" font-style="italic" fill="#9c5d0e">Lipschitz chain · 80 lines of Lean</text>
  <text x="500" y="280" class="label" text-anchor="end" font-style="italic" fill="#9c5d0e">strength: positive-measure constraint</text>

  <!-- Arrow down: + transversality -->
  <line x1="380" y1="305" x2="380" y2="325" stroke="#b0413e" stroke-width="2.5" marker-end="url(#arr2)" />
  <text x="395" y="319" class="label-small" font-style="italic">+ transversality (G &gt; ℓ(K+1))</text>

  <!-- LEVEL 3 -->
  <rect x="20" y="330" width="720" height="115" rx="10" fill="rgba(229, 62, 62, 0.12)" stroke="#c53030" stroke-width="2" />
  <text x="40" y="355" class="label label-bold" fill="#742a2a" font-size="13">Level 3 — Persistent Unsafe Region (Thm 6.2)</text>

  <text x="40" y="378" class="label-small">Adds:</text>
  <text x="125" y="378" class="label-small">∃ steep direction: f rises faster than the defense's Lipschitz budget</text>

  <text x="40" y="398" class="label-small">Conclusion:</text>
  <text x="125" y="398" class="label-small">∃ open set 𝒮 with μ(𝒮) &gt; 0 and f(D(x)) &gt; τ for all x ∈ 𝒮</text>

  <text x="40" y="425" class="label-small" font-style="italic" fill="#742a2a">Refined Lipschitz · 200 lines of Lean (MoF_20)</text>
  <text x="500" y="425" class="label" text-anchor="end" font-style="italic" fill="#742a2a">strength: positive-measure failure</text>
</svg>

<p class="diagram-caption">
  Each level reuses the boundary point z from Level 1 as its geometric anchor. The hierarchy is strict: Level 2 implies Level 1, and Level 3 implies Level 2 wherever transversality holds.
</p>

</div>

## Side-by-side comparison

<table class="compare-table">
<thead>
<tr>
<th></th>
<th>Level 1: Boundary Fixation</th>
<th>Level 2: ε-Robust</th>
<th>Level 3: Persistent</th>
</tr>
</thead>
<tbody>
<tr>
<td><strong>Geometry needed</strong></td>
<td>Topological (connected Hausdorff)</td>
<td>Metric (distances)</td>
<td>Metric + directional rate</td>
</tr>
<tr>
<td><strong>Regularity needed</strong></td>
<td>Continuity</td>
<td>Lipschitz</td>
<td>Lipschitz + transversality</td>
</tr>
<tr>
<td><strong>Failure shape</strong></td>
<td>One point (measure 0)</td>
<td>Constrained band (positive measure, near-threshold)</td>
<td>Strictly unsafe set (positive measure, above τ)</td>
</tr>
<tr>
<td><strong>Quantitative bound</strong></td>
<td>Existence only</td>
<td>$|f(D(x)) - \tau| \leq LK \cdot \mathrm{dist}(x, z)$</td>
<td>$f(D(x)) > \tau$ on $\mathcal{S}$</td>
</tr>
<tr>
<td><strong>Lean theorem</strong></td>
<td><code>epsilon_robust_impossibility</code> (existence portion)</td>
<td><code>defense_output_near_threshold</code></td>
<td><code>persistent_unsafe_refined</code> (MoF_20)</td>
</tr>
</tbody>
</table>

## Why escalation works

**Level 1 → Level 2.** Once we have a fixed point $z$ where $f(z) = \tau$ and $D(z) = z$, the Lipschitz chain immediately gives:

$$|f(D(x)) - \tau| = |f(D(x)) - f(z)| \leq L \cdot \mathrm{dist}(D(x), z) = L \cdot \mathrm{dist}(D(x), D(z)) \leq L \cdot K \cdot \mathrm{dist}(x, z).$$

So *every* point near $z$ is constrained: the defense can shift it by at most $LK \cdot \mathrm{dist}(x, z)$ from threshold. This pulls the Level-1 point-failure into a positive-measure band-failure.

**Level 2 → Level 3.** The band failure constrains the *depth* of remediation but allows the defense to push points slightly below $\tau$. To get strictly unsafe outputs, we need a stronger comparison: how fast does $f$ rise *away* from $z$ versus how much can the defense pull it back? When the alignment surface is steep enough — directional gradient $G > \ell(K+1)$, where $\ell$ is the defense-path Lipschitz constant — the defense can never compensate, and a positive-measure region survives strictly above threshold.

::: tip Why $\ell$ instead of $L$?
At Level 3 we use the *defense-path* Lipschitz constant $\ell$, which only measures how much $f$ varies along the displacement direction $D(x) - x$. In anisotropic surfaces, $\ell$ can be much smaller than the global $L$, making the persistence condition $G > \ell(K+1)$ easier to satisfy. See the [K dilemma page](/dilemma) for what this implies for defense design.
:::

## What changes between Level 2 and Level 3

Level 2 says: *the defense cannot push near-boundary points far below threshold*. This is enough to prove that a positive-measure band is constrained, but it does **not** rule out a defense that pushes everything to $\tau - \epsilon$ for small $\epsilon$. Such a defense would technically be complete.

Level 3 closes that loophole. If the alignment surface is *steep enough* in any direction, the defense's Lipschitz budget runs out before it can pull the surface below $\tau$. The shaded red region in the rightmost panel of the [hero diagram](/) is exactly this: a wedge above the defense's budget cone where $f$ outruns $D$.

→ Next: see [why no choice of $K$ escapes both failure modes](/dilemma).
