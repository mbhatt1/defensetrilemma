# 2D Prompt Space

The geometric setup. A defense $D\colon X \to X$ tries to remap unsafe prompts into the safe region while leaving safe prompts unchanged. The theorem says it must also leave at least one boundary prompt unchanged.

<div class="diagram">

<svg viewBox="0 0 720 420" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="arrowhead" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#2b6cb0" />
    </marker>
    <marker id="arrowhead-thin" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">
      <polygon points="0 0, 8 4, 0 8" fill="#2b6cb0" opacity="0.7" />
    </marker>
  </defs>

  <!-- Safe region -->
  <rect x="60" y="60" width="280" height="280" class="safe-fill" stroke="#38a169" stroke-width="1.5" stroke-dasharray="0" />
  <text x="200" y="100" class="label label-bold" text-anchor="middle" fill="#38a169">Safe region S_τ</text>
  <text x="200" y="118" class="label" text-anchor="middle" fill="#38a169">f(x) &lt; τ</text>
  <text x="200" y="155" class="label-small" text-anchor="middle">Defense leaves these unchanged:</text>
  <text x="200" y="170" class="label-small" text-anchor="middle" font-style="italic">D(x) = x  for all x ∈ S_τ</text>

  <!-- Unsafe region -->
  <rect x="340" y="60" width="280" height="280" class="unsafe-fill" stroke="#c53030" stroke-width="1.5" />
  <text x="480" y="100" class="label label-bold" text-anchor="middle" fill="#c53030">Unsafe region U_τ</text>
  <text x="480" y="118" class="label" text-anchor="middle" fill="#c53030">f(x) &gt; τ</text>
  <text x="480" y="155" class="label-small" text-anchor="middle">Defense tries to remap these</text>
  <text x="480" y="170" class="label-small" text-anchor="middle" font-style="italic">into the safe region</text>

  <!-- Boundary line -->
  <line x1="340" y1="60" x2="340" y2="340" stroke="#2d3748" stroke-width="2" stroke-dasharray="6,4" />
  <text x="340" y="50" class="label label-bold" text-anchor="middle">Boundary B_τ:  f(x) = τ</text>

  <!-- Fixed point z (the headline result) -->
  <circle cx="340" cy="220" r="6" fill="#2d3748" />
  <text x="350" y="218" class="label label-bold">z (fixed boundary point)</text>
  <text x="350" y="234" class="label-small">f(z) = τ,  D(z) = z</text>

  <!-- Defense arrows from unsafe region into safe region -->
  <path d="M 540,250 Q 470,310 350,250" stroke="#2b6cb0" stroke-width="2" fill="none" marker-end="url(#arrowhead)" />
  <path d="M 580,200 Q 500,330 320,260" stroke="#2b6cb0" stroke-width="1.6" fill="none" marker-end="url(#arrowhead-thin)" opacity="0.7" />
  <path d="M 500,290 Q 440,340 280,300" stroke="#2b6cb0" stroke-width="1.6" fill="none" marker-end="url(#arrowhead-thin)" opacity="0.7" />

  <text x="430" y="395" class="label" text-anchor="middle" fill="#2b6cb0" font-style="italic">D: defense remaps unsafe → safe</text>

  <!-- Axis hint -->
  <text x="640" y="345" class="label-small">prompt space X</text>
</svg>

<p class="diagram-caption">
  Schematic of the prompt space. The defense D must leave all safe inputs unchanged (utility preservation) and tries to remap unsafe inputs into the safe region. The black dot z is the fixed boundary point that <strong>boundary fixation</strong> guarantees: a prompt where f(z) = τ exactly, passing through with no remediation.
</p>

</div>

## Why this picture forces the impossibility

The picture has three constraints that look reasonable individually but cannot all hold:

<div class="three-card">

<div class="card">
<h4><span class="num">1</span> Utility preservation</h4>
<p>Every safe prompt passes through unchanged. Formally: $D(x) = x$ for all $x \in S_\tau$. This means the entire green region is fixed by $D$.</p>
</div>

<div class="card">
<h4><span class="num">2</span> Continuity</h4>
<p>Similar prompts produce similar rewrites. Formally: $D$ is continuous. This means the fixed-point set $\{x : D(x) = x\}$ is a closed set.</p>
</div>

<div class="card">
<h4><span class="num">3</span> Connectedness</h4>
<p>The prompt space is in one piece. Formally: $X$ is connected. This means $S_\tau$ — being open and nonempty proper — cannot also be closed.</p>
</div>

</div>

::: tip The contradiction
If all three hold, then $\overline{S_\tau} \subsetneq X$ is a closed set strictly containing $S_\tau$. The defense must fix every point in $\overline{S_\tau}$ — including the boundary points $\overline{S_\tau} \setminus S_\tau$, where $f$ equals exactly $\tau$.

There is **no defense** $D$ that satisfies all three constraints and is also complete. The black dot $z$ is unavoidable.
:::

## What "boundary point" actually means

A boundary point $z \in \overline{S_\tau} \setminus S_\tau$ is a prompt that:

- Is **not safe** (it's not in $S_\tau$, so $f(z) \geq \tau$).
- Is **arbitrarily close** to safe prompts (it's a limit of points where $f < \tau$, so $f(z) \leq \tau$).
- Therefore: $f(z) = \tau$ exactly — the defense passes it through with no remediation.

The whole impossibility comes from this: **the boundary is not empty when the safe region is open but not closed**, which is exactly what connectedness forces.

→ Next: see the [proof chain](/boundary-proof) that turns this picture into five formal steps.
