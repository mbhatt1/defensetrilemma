# Extensions: Multi-Turn, Stochastic, Pipeline

The core results assume a static, deterministic, single-turn defense. *Does multi-turn interaction, randomization, or pipelining provide an escape?* No. Each extension is a direct application of the boundary fixation machinery to a modified setting.

## Multi-turn: failure compounds monotonically

<div class="diagram">

<svg viewBox="0 0 760 280" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="marr" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#2b6cb0" />
    </marker>
  </defs>

  <!-- Axes -->
  <line x1="60" y1="220" x2="720" y2="220" class="axis" />
  <line x1="60" y1="40" x2="60" y2="220" class="axis" />
  <text x="730" y="225" class="label-small">turn t</text>
  <text x="55" y="35" class="label-small" text-anchor="end">best AD observed</text>

  <!-- Threshold -->
  <line x1="60" y1="100" x2="720" y2="100" class="threshold" />
  <text x="55" y="103" class="label-small" text-anchor="end">τ</text>

  <!-- Monotone-improving step function -->
  <path d="M 60,200 L 130,200 L 130,180 L 200,180 L 200,160 L 270,160 L 270,140 L 340,140 L 340,130 L 410,130 L 410,115 L 480,115 L 480,105 L 550,105 L 550,98 L 620,98 L 620,95 L 690,95"
        fill="none" stroke="#2b6cb0" stroke-width="2.5" />

  <!-- Boundary fixed points at each turn -->
  <circle cx="130" cy="200" r="3.5" fill="#2d3748" />
  <circle cx="200" cy="180" r="3.5" fill="#2d3748" />
  <circle cx="270" cy="160" r="3.5" fill="#2d3748" />
  <circle cx="340" cy="140" r="3.5" fill="#2d3748" />
  <circle cx="410" cy="115" r="3.5" fill="#2d3748" />
  <circle cx="480" cy="98" r="4.5" fill="#c53030" />
  <text x="490" y="102" class="label-small" fill="#c53030">crossing!</text>

  <!-- Tick labels -->
  <g class="label-small">
    <text x="130" y="240" text-anchor="middle">t=1</text>
    <text x="200" y="240" text-anchor="middle">t=2</text>
    <text x="270" y="240" text-anchor="middle">t=3</text>
    <text x="340" y="240" text-anchor="middle">t=4</text>
    <text x="410" y="240" text-anchor="middle">t=5</text>
    <text x="480" y="240" text-anchor="middle">t=6</text>
    <text x="550" y="240" text-anchor="middle">t=7</text>
    <text x="620" y="240" text-anchor="middle">t=8</text>
  </g>

  <text x="380" y="265" class="label" text-anchor="middle" font-style="italic">Each turn: fresh boundary fixation. Best observed AD never decreases.</text>
</svg>

<p class="diagram-caption">
  At every turn t, Theorem 4.1 applies fresh to (f_t, D_t). The attacker's <em>best observed</em> AD across turns is monotone non-decreasing (verified in Lean as <code>running_max_monotone</code>). The attacker can binary-search toward the steep direction.
</p>

</div>

<div class="thm">
<div class="thm-title">Theorem 9.1 — Multi-Turn Impossibility</div>

Let $\{f_t, D_t\}_{t=1}^T$ be alignment functions and defenses over $T$ turns on a connected Hausdorff space, each continuous and utility-preserving, with $S_\tau^{(t)}, U_\tau^{(t)} \neq \emptyset$ at every turn. Then for every turn $t$, there exists $z_t$ with $f_t(z_t) = \tau$ and $D_t(z_t) = z_t$.
</div>

Multi-turn is not an escape — it's an *amplifier*. The attacker gets a fresh fixed-point existence proof every turn, can remember which turns produced the highest AD, and steer subsequent turns toward those neighborhoods. The expected number of turns to reach a transversal crossing is bounded by the binary-search depth of the steep-direction search.

---

## Stochastic: the dichotomy at boundary points

<div class="diagram">

<svg viewBox="0 0 760 320" xmlns="http://www.w3.org/2000/svg">
  <!-- Center boundary point -->
  <line x1="380" y1="40" x2="380" y2="280" stroke="#2d3748" stroke-width="1" stroke-dasharray="3,3" />
  <text x="380" y="32" class="label label-bold" text-anchor="middle">boundary point z, f(z) = τ</text>

  <!-- Two cases -->
  <!-- LEFT: deterministic -->
  <text x="190" y="70" class="label label-bold" text-anchor="middle">Case A: deterministic at z</text>
  <text x="190" y="88" class="label-small" text-anchor="middle" font-style="italic">f(D(z)) = τ a.s.</text>

  <!-- Spike at τ -->
  <line x1="190" y1="220" x2="190" y2="120" stroke="#2b6cb0" stroke-width="3" />
  <polygon points="184,124 196,124 190,116" fill="#2b6cb0" />

  <!-- Threshold line -->
  <line x1="100" y1="220" x2="280" y2="220" class="threshold" />
  <text x="100" y="217" class="label-small">τ</text>

  <text x="190" y="245" class="label-small" text-anchor="middle">all probability mass</text>
  <text x="190" y="259" class="label-small" text-anchor="middle">at exactly τ</text>

  <text x="190" y="290" class="label" text-anchor="middle" fill="#2b6cb0">"clean" failure</text>

  <!-- RIGHT: stochastic -->
  <text x="570" y="70" class="label label-bold" text-anchor="middle">Case B: genuinely random</text>
  <text x="570" y="88" class="label-small" text-anchor="middle" font-style="italic">P(f(D(z)) > τ) > 0</text>

  <!-- Spread distribution -->
  <path d="M 460,220 Q 510,110 570,110 Q 630,110 680,220 Z" fill="rgba(197, 48, 48, 0.3)" stroke="#c53030" stroke-width="2" />

  <!-- Threshold line on RIGHT -->
  <line x1="460" y1="220" x2="680" y2="220" class="threshold" />
  <text x="460" y="217" class="label-small">τ</text>

  <!-- Right tail shading (positive prob > τ) -->
  <path d="M 570,220 Q 630,110 680,220 Z" fill="rgba(197, 48, 48, 0.5)" />

  <text x="640" y="160" class="label-small" fill="#c53030">positive prob.</text>
  <text x="640" y="174" class="label-small" fill="#c53030">of strictly unsafe</text>

  <text x="570" y="290" class="label" text-anchor="middle" fill="#c53030">actively produces unsafe outputs</text>
</svg>

<p class="diagram-caption">
  The stochastic dichotomy. Since E[f(D(z))] = τ exactly at the boundary point, the random variable f(D(z)) either concentrates entirely at τ (deterministic, Case A) or has positive probability of exceeding τ (Case B). A genuinely random defense at boundary points <strong>must sometimes make things worse</strong>.
</p>

</div>

<div class="thm">
<div class="thm-title">Theorem 9.2 — Stochastic Defense Impossibility</div>

Let $X$ be a connected Hausdorff space, $f\colon X \to \mathbb{R}$ continuous with $S_\tau, U_\tau \neq \emptyset$. Let $D$ be a stochastic defense and $g(x) = \mathbb{E}_{y \sim D(x)}[f(y)]$. If $g$ is continuous and $g(x) = f(x)$ for all $x \in S_\tau$, then there exists $z$ with $f(z) = \tau$ and $g(z) = \tau$.

**Dichotomy:** Since $\mathbb{E}[f(D(z))] = \tau$, either $f(D(z)) = \tau$ almost surely (deterministic), or $\mathbb{P}(f(D(z)) > \tau) > 0$ — the defense actively produces unsafe outputs with positive probability. The stochastic case is **strictly harder** than the deterministic one.
</div>

Randomization does not help. It can only relocate the failure: from "passes through unchanged at $\tau$" to "sometimes passes through above $\tau$".

---

## Pipelines: Lipschitz constants compound exponentially

<div class="diagram">

<svg viewBox="0 0 760 240" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="parr" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#2b6cb0" />
    </marker>
  </defs>

  <!-- Pipeline boxes -->
  <g>
    <rect x="40" y="80" width="100" height="60" rx="6" fill="rgba(43, 108, 176, 0.15)" stroke="#2b6cb0" stroke-width="1.5"/>
    <text x="90" y="105" class="label label-bold" text-anchor="middle">D</text>
    <text x="90" y="125" class="label-small" text-anchor="middle">K_D-Lip</text>

    <line x1="142" y1="110" x2="170" y2="110" stroke="#2b6cb0" stroke-width="2" marker-end="url(#parr)" />

    <rect x="172" y="80" width="100" height="60" rx="6" fill="rgba(43, 108, 176, 0.15)" stroke="#2b6cb0" stroke-width="1.5"/>
    <text x="222" y="105" class="label label-bold" text-anchor="middle">T₁</text>
    <text x="222" y="125" class="label-small" text-anchor="middle">K-Lip</text>

    <line x1="274" y1="110" x2="302" y2="110" stroke="#2b6cb0" stroke-width="2" marker-end="url(#parr)" />

    <rect x="304" y="80" width="100" height="60" rx="6" fill="rgba(43, 108, 176, 0.15)" stroke="#2b6cb0" stroke-width="1.5"/>
    <text x="354" y="105" class="label label-bold" text-anchor="middle">T₂</text>
    <text x="354" y="125" class="label-small" text-anchor="middle">K-Lip</text>

    <line x1="406" y1="110" x2="434" y2="110" stroke="#2b6cb0" stroke-width="2" marker-end="url(#parr)" />

    <text x="466" y="115" class="label" text-anchor="middle">…</text>

    <line x1="490" y1="110" x2="518" y2="110" stroke="#2b6cb0" stroke-width="2" marker-end="url(#parr)" />

    <rect x="520" y="80" width="100" height="60" rx="6" fill="rgba(43, 108, 176, 0.15)" stroke="#2b6cb0" stroke-width="1.5"/>
    <text x="570" y="105" class="label label-bold" text-anchor="middle">T_n</text>
    <text x="570" y="125" class="label-small" text-anchor="middle">K-Lip</text>

    <line x1="622" y1="110" x2="650" y2="110" stroke="#2b6cb0" stroke-width="2" marker-end="url(#parr)" />

    <rect x="652" y="85" width="80" height="50" rx="6" fill="rgba(229, 62, 62, 0.18)" stroke="#c53030" stroke-width="1.5"/>
    <text x="692" y="115" class="label label-bold" text-anchor="middle" fill="#c53030">model</text>
  </g>

  <!-- Effective Lipschitz formula -->
  <text x="380" y="180" class="label label-bold" text-anchor="middle">Effective Lipschitz constant of pipeline:</text>
  <text x="380" y="205" class="label label-bold" text-anchor="middle" fill="#c53030">K_D · K^n   →  exponential in pipeline depth</text>
</svg>

<p class="diagram-caption">
  A defense composed with n downstream tools. Each stage's Lipschitz constant multiplies, so the effective constant grows as K^n. The ε-band scales as L(K_D · K^n + 1)δ — the failure region widens exponentially with pipeline depth.
</p>

</div>

<div class="thm">
<div class="thm-title">Theorem 9.4 — Pipeline Impossibility</div>

If the composed pipeline $P = T_n \circ \cdots \circ T_1 \circ D$ is continuous and $P(x) = x$ for all $x \in S_\tau$, then $P$ has boundary fixed points. If $D$ is $K_D$-Lipschitz and each $T_i$ is $K$-Lipschitz with $K \geq 2$, the ε-robust band scales as $L(K_D \cdot K^n + 1)\delta$ — exponential in depth.
</div>

::: warning Pipelines make things worse
The intuition that "more stages = more chances to catch attacks" is wrong for *continuous* pipelines. Each non-contractive stage multiplies the effective Lipschitz constant; the failure band that the wrapper cannot push below threshold grows exponentially with pipeline depth. Verified in Lean as `MoF_15_NonlinearAgents`.
:::

## Summary of escape attempts

| Escape attempt | Why it fails |
|---|---|
| **Multi-turn** (memory across turns) | Theorem 4.1 applies fresh each turn. Attacker's best observed AD is monotone. |
| **Stochastic** (randomized defense) | Expected AD at boundary is exactly τ → either deterministic or positive prob > τ. |
| **Pipeline** (chain of tools) | Effective Lipschitz constant compounds as $K^n$, widening the failure band exponentially. |

→ Next: see how all this plays out on [three real LLMs](/empirical).
