# The Discrete Defense Dilemma

The same impossibility appears on **finite sets** with no topology at all. Just counting. This rules out the objection that the continuous theorems are an artifact of continuous relaxation.

<div class="diagram">

<svg viewBox="0 0 760 380" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="darr" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#2b6cb0" />
    </marker>
    <marker id="darr-red" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#c53030" />
    </marker>
  </defs>

  <!-- LEFT: Injective + utility-preserving = INCOMPLETE -->
  <text x="190" y="30" class="label label-bold" text-anchor="middle">Injective defense</text>
  <text x="190" y="48" class="label-small" text-anchor="middle" font-style="italic">distinct inputs → distinct outputs</text>

  <!-- Safe inputs (green) -->
  <circle cx="80" cy="100" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="80" y="104" class="label-small" text-anchor="middle">s₁</text>
  <circle cx="80" cy="140" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="80" y="144" class="label-small" text-anchor="middle">s₂</text>
  <circle cx="80" cy="180" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="80" y="184" class="label-small" text-anchor="middle">s₃</text>

  <!-- Unsafe input -->
  <circle cx="80" cy="240" r="14" class="unsafe-fill" stroke="#c53030" stroke-width="1.5"/>
  <text x="80" y="244" class="label-small" text-anchor="middle">u</text>

  <!-- Safe outputs (identity) -->
  <circle cx="280" cy="100" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="280" y="104" class="label-small" text-anchor="middle">s₁</text>
  <circle cx="280" cy="140" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="280" y="144" class="label-small" text-anchor="middle">s₂</text>
  <circle cx="280" cy="180" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="280" y="184" class="label-small" text-anchor="middle">s₃</text>

  <!-- Unsafe output: u must go SOMEWHERE distinct from s₁,s₂,s₃ -->
  <circle cx="280" cy="240" r="14" class="unsafe-fill" stroke="#c53030" stroke-width="1.5"/>
  <text x="280" y="244" class="label-small" text-anchor="middle">u'</text>

  <!-- Identity arrows for safe -->
  <line x1="94" y1="100" x2="266" y2="100" stroke="#38a169" stroke-width="2" marker-end="url(#darr)" />
  <line x1="94" y1="140" x2="266" y2="140" stroke="#38a169" stroke-width="2" marker-end="url(#darr)" />
  <line x1="94" y1="180" x2="266" y2="180" stroke="#38a169" stroke-width="2" marker-end="url(#darr)" />

  <!-- Unsafe → unsafe (arrow with X mark) -->
  <line x1="94" y1="240" x2="266" y2="240" stroke="#c53030" stroke-width="2" marker-end="url(#darr-red)" />

  <text x="190" y="290" class="label" text-anchor="middle" fill="#742a2a">D(u) ≠ s_i (injectivity blocks),</text>
  <text x="190" y="306" class="label" text-anchor="middle" fill="#742a2a">so D(u) lands in unsafe region</text>
  <text x="190" y="322" class="label label-bold" text-anchor="middle" fill="#c53030">⇒ INCOMPLETE</text>

  <!-- DIVIDER -->
  <line x1="380" y1="40" x2="380" y2="340" stroke="currentColor" stroke-width="1" stroke-dasharray="3,3" opacity="0.3"/>

  <!-- RIGHT: Complete + utility-preserving = NON-INJECTIVE -->
  <text x="570" y="30" class="label label-bold" text-anchor="middle">Complete defense</text>
  <text x="570" y="48" class="label-small" text-anchor="middle" font-style="italic">all outputs land in safe region</text>

  <circle cx="460" cy="100" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="460" y="104" class="label-small" text-anchor="middle">s₁</text>
  <circle cx="460" cy="140" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="460" y="144" class="label-small" text-anchor="middle">s₂</text>
  <circle cx="460" cy="180" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="460" y="184" class="label-small" text-anchor="middle">s₃</text>

  <circle cx="460" cy="240" r="14" class="unsafe-fill" stroke="#c53030" stroke-width="1.5"/>
  <text x="460" y="244" class="label-small" text-anchor="middle">u</text>

  <circle cx="660" cy="100" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="660" y="104" class="label-small" text-anchor="middle">s₁</text>
  <circle cx="660" cy="140" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="660" y="144" class="label-small" text-anchor="middle">s₂</text>
  <circle cx="660" cy="180" r="14" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="660" y="184" class="label-small" text-anchor="middle">s₃</text>

  <line x1="474" y1="100" x2="646" y2="100" stroke="#38a169" stroke-width="2" marker-end="url(#darr)" />
  <line x1="474" y1="140" x2="646" y2="140" stroke="#38a169" stroke-width="2" marker-end="url(#darr)" />
  <line x1="474" y1="180" x2="646" y2="180" stroke="#38a169" stroke-width="2" marker-end="url(#darr)" />

  <!-- Unsafe collapses onto s₁ -->
  <path d="M 474,240 Q 565,260 646,108" stroke="#c53030" stroke-width="2.5" fill="none" marker-end="url(#darr-red)" />
  <text x="595" y="220" class="label-small" fill="#c53030">collapse</text>

  <text x="570" y="290" class="label" text-anchor="middle" fill="#742a2a">D(u) = s₁ AND D(s₁) = s₁,</text>
  <text x="570" y="306" class="label" text-anchor="middle" fill="#742a2a">so two distinct inputs map to s₁</text>
  <text x="570" y="322" class="label label-bold" text-anchor="middle" fill="#c53030">⇒ NON-INJECTIVE</text>
</svg>

<p class="diagram-caption">
  The discrete defense dilemma. Left: an injective utility-preserving defense cannot remap u to any s_i (injectivity forces distinct outputs), so D(u) stays in the unsafe region. Right: a complete utility-preserving defense must map u to some safe s_i, but s_i is already fixed by utility preservation, so two inputs collapse to the same output.
</p>

</div>

<div class="thm">
<div class="thm-title">Theorem 8.2 — Discrete Defense Dilemma</div>

Let $X$ be a finite set with $S_\tau, U_\tau \neq \emptyset$, and $D\colon X \to X$ utility-preserving ($D(x) = x$ for $f(x) < \tau$).

1. **If $D$ is injective**, then $f(D(u)) \geq \tau$ for every $u$ with $f(u) \geq \tau$ — the defense is **incomplete**.
2. **If $D$ is complete** ($f(D(x)) < \tau$ for all $x$), then $D$ is **non-injective**: $\exists\, x \neq y$ with $D(x) = D(y)$.
</div>

## The proof in two paragraphs

**Part 1.** Suppose $D$ is injective and $f(D(u)) < \tau$ for some $u$ with $f(u) \geq \tau$. Then $D(u)$ is safe, so by utility preservation $D(D(u)) = D(u)$. Injectivity gives $D(u) = u$, so $f(u) = f(D(u)) < \tau$ — contradicting $f(u) \geq \tau$.

**Part 2.** For any $u \in U_\tau$: completeness gives $f(D(u)) < \tau$, so $D(u)$ is safe and utility preservation gives $D(D(u)) = D(u)$. But $u \neq D(u)$ since $f(u) \geq \tau > f(D(u))$. So $u$ and $D(u)$ are distinct inputs with $D(u) = D(D(u))$ — the defense is non-injective.

## Why this matters

The continuous trilemma trades **continuity** for completeness. The discrete dilemma trades **injectivity** — and injectivity is a much weaker hypothesis than continuity. There's nothing topological here. No connectedness, no Hausdorff, no Lipschitz. Just:

- Defense is a function $X \to X$ on a finite set.
- It fixes safe points.
- It's injective.
- Therefore it's incomplete.

Or, contrapositively:

- Defense is complete.
- It fixes safe points.
- Therefore it's non-injective — distinct inputs collapse to identical outputs.

::: tip Why injectivity is the meaningful constraint
A non-injective defense **destroys information**. Two distinct user prompts produce the same downstream input — the model receives the same input regardless of whether the original was safe or an attack. Any auditing, attack-detection, or human-in-the-loop logic must therefore happen *before* the defense is applied. Once $D$ has run, the original prompt is unrecoverable.
:::

## Why this rules out the "continuous relaxation" objection

A natural objection to the [continuous trilemma](/) is: *the impossibility might be an artifact of how we extended discrete observations to continuous functions*. The discrete dilemma blocks this. The same conclusion holds on finite sets with no extension at all. Whatever the prompt space looks like — discrete, continuous, mixed — utility-preserving defenses face the same bind.

The continuous and discrete versions agree on the conclusion but differ on which property is being traded:

| Setting | Trades for completeness |
|---|---|
| Continuous (connected Hausdorff) | **Continuity** |
| Discrete (finite set) | **Injectivity** (information preservation) |
| Both | Utility preservation cannot coexist with completeness without giving up something |

::: info Lean verification
This is verified in [`MoF_12_Discrete.lean`](https://github.com/mbhatt1/stuff/tree/main/ManifoldProofs/ManifoldProofs/MoF_12_Discrete.lean) using only finite-set counting and pigeonhole. Zero topology imports.
:::
