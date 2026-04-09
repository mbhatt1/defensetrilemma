# Counterexamples: Each Hypothesis Is Necessary

The boundary fixation theorem has three load-bearing hypotheses: **continuity** of $D$, **utility preservation** by $D$, and **connectedness** of $X$. Drop any one and the impossibility evaporates. Here are the explicit counterexamples.

<div class="diagram-row">

<div class="diagram">
<svg viewBox="0 0 280 240" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="cearr1" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#2b6cb0" />
    </marker>
  </defs>

  <text x="140" y="22" class="label label-bold" text-anchor="middle">Drop connectedness</text>
  <text x="140" y="40" class="label-small" text-anchor="middle" font-style="italic">X = {0, 1} discrete</text>

  <!-- Two isolated points -->
  <circle cx="80" cy="120" r="22" class="safe-fill" stroke="#38a169" stroke-width="2"/>
  <text x="80" y="124" class="label label-bold" text-anchor="middle">0</text>
  <text x="80" y="155" class="label-small" text-anchor="middle">f(0) = 0</text>
  <text x="80" y="170" class="label-small" text-anchor="middle">safe</text>

  <circle cx="200" cy="120" r="22" class="unsafe-fill" stroke="#c53030" stroke-width="2"/>
  <text x="200" y="124" class="label label-bold" text-anchor="middle">1</text>
  <text x="200" y="155" class="label-small" text-anchor="middle">f(1) = 1</text>
  <text x="200" y="170" class="label-small" text-anchor="middle">unsafe</text>

  <!-- D(0) = 0 self-loop -->
  <path d="M 65,105 Q 50,80 80,75 Q 110,80 95,105" stroke="#2b6cb0" stroke-width="1.8" fill="none" marker-end="url(#cearr1)"/>

  <!-- D(1) = 0 -->
  <path d="M 178,120 Q 140,90 102,120" stroke="#2b6cb0" stroke-width="1.8" fill="none" marker-end="url(#cearr1)"/>

  <text x="140" y="200" class="label label-bold" text-anchor="middle" fill="#1c5b34">Defense works:</text>
  <text x="140" y="216" class="label-small" text-anchor="middle">D(0)=0, D(1)=0</text>
  <text x="140" y="230" class="label-small" text-anchor="middle">cont, util-pres, complete ✓</text>
</svg>
<p class="diagram-caption">Two isolated points form a disconnected space. The "boundary" is empty — there are no points in $\overline{S_\tau} \setminus S_\tau$, so nothing is forced to be fixed.</p>
</div>

<div class="diagram">
<svg viewBox="0 0 280 240" xmlns="http://www.w3.org/2000/svg">
  <text x="140" y="22" class="label label-bold" text-anchor="middle">Drop continuity</text>
  <text x="140" y="40" class="label-small" text-anchor="middle" font-style="italic">X = [0, 1], f(x) = x, τ = 0.5</text>

  <!-- Axes -->
  <line x1="40" y1="190" x2="240" y2="190" class="axis"/>
  <line x1="40" y1="60" x2="40" y2="190" class="axis"/>

  <!-- Threshold -->
  <line x1="40" y1="125" x2="240" y2="125" class="threshold"/>
  <text x="34" y="128" class="label-small" text-anchor="end">0.5</text>

  <!-- f(x) = x: thin diagonal as background -->
  <line x1="40" y1="190" x2="240" y2="60" stroke="#999" stroke-width="1" stroke-dasharray="2,2"/>
  <text x="245" y="64" class="label-small" fill="#999">f(x)=x</text>

  <!-- D(x): identity for x < 0.5, jump to 0 for x >= 0.5 -->
  <line x1="40" y1="190" x2="140" y2="125" stroke="#2b6cb0" stroke-width="2.5"/>
  <circle cx="140" cy="125" r="3" fill="white" stroke="#2b6cb0" stroke-width="1.5"/>
  <line x1="140" y1="190" x2="240" y2="190" stroke="#2b6cb0" stroke-width="2.5"/>
  <circle cx="140" cy="190" r="3" fill="#2b6cb0"/>

  <!-- Jump arrow -->
  <line x1="140" y1="125" x2="140" y2="187" stroke="#c53030" stroke-width="1" stroke-dasharray="2,2"/>
  <text x="148" y="160" class="label-small" fill="#c53030">jump</text>

  <text x="140" y="216" class="label label-bold" text-anchor="middle" fill="#1c5b34">D(x) = x for x &lt; 0.5,</text>
  <text x="140" y="230" class="label-small" text-anchor="middle">D(x) = 0 for x ≥ 0.5: complete ✓</text>
</svg>
<p class="diagram-caption">A discontinuous defense can collapse the entire unsafe region to a safe point in one jump. Continuity is the only thing that prevents this.</p>
</div>

<div class="diagram">
<svg viewBox="0 0 280 240" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="cearr3" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="#2b6cb0" />
    </marker>
  </defs>

  <text x="140" y="22" class="label label-bold" text-anchor="middle">Drop utility preservation</text>
  <text x="140" y="40" class="label-small" text-anchor="middle" font-style="italic">D(x) = x₀ (constant safe point)</text>

  <!-- Domain: half safe, half unsafe -->
  <rect x="40" y="80" width="100" height="100" class="safe-fill" stroke="#38a169" stroke-width="1.5"/>
  <text x="90" y="105" class="label-small" text-anchor="middle" fill="#1c5b34">S_τ</text>

  <rect x="140" y="80" width="100" height="100" class="unsafe-fill" stroke="#c53030" stroke-width="1.5"/>
  <text x="190" y="105" class="label-small" text-anchor="middle" fill="#742a2a">U_τ</text>

  <!-- Single target point x_0 -->
  <circle cx="70" cy="150" r="6" fill="#2d3748"/>
  <text x="80" y="154" class="label-small">x₀</text>

  <!-- Many arrows from various inputs to x_0 -->
  <line x1="100" y1="135" x2="76" y2="148" stroke="#2b6cb0" stroke-width="1.5" marker-end="url(#cearr3)"/>
  <line x1="115" y1="170" x2="78" y2="153" stroke="#2b6cb0" stroke-width="1.5" marker-end="url(#cearr3)"/>
  <line x1="170" y1="120" x2="80" y2="150" stroke="#2b6cb0" stroke-width="1.5" marker-end="url(#cearr3)"/>
  <line x1="200" y1="155" x2="80" y2="153" stroke="#2b6cb0" stroke-width="1.5" marker-end="url(#cearr3)"/>
  <line x1="220" y1="100" x2="82" y2="148" stroke="#2b6cb0" stroke-width="1.5" marker-end="url(#cearr3)"/>
  <line x1="180" y1="170" x2="80" y2="155" stroke="#2b6cb0" stroke-width="1.5" marker-end="url(#cearr3)"/>

  <text x="140" y="210" class="label label-bold" text-anchor="middle" fill="#1c5b34">Constant defense:</text>
  <text x="140" y="226" class="label-small" text-anchor="middle">cont, complete, but destroys utility</text>
</svg>
<p class="diagram-caption">A constant map sends every prompt to a fixed safe point. Continuous, complete, but no longer utility-preserving — every prompt produces the same response.</p>
</div>

</div>

## The three counterexamples in detail

<div class="thm">
<div class="thm-title">Counterexample 1 — Removing connectedness</div>

$X = \{0, 1\}$ discrete, $f(0) = 0$, $f(1) = 1$, $\tau = 0.5$. Define $D(0) = 0$, $D(1) = 0$.

- ✅ **Continuous** (every function on a discrete space is continuous).
- ✅ **Utility-preserving** ($D(0) = 0$, the only safe input).
- ✅ **Complete** ($f(D(0)) = 0 < 0.5$ and $f(D(1)) = 0 < 0.5$).

The theorem fails because $X$ is disconnected: $S_\tau = \{0\}$ is *clopen*, so the chain in [step 3](/boundary-proof) of the proof breaks.
</div>

<div class="thm">
<div class="thm-title">Counterexample 2 — Removing continuity</div>

$X = [0, 1]$, $f(x) = x$, $\tau = 0.5$. Define
$$D(x) = \begin{cases} x & x < 0.5 \\ 0 & x \geq 0.5 \end{cases}$$

- ❌ **Discontinuous** at $x = 0.5$ (jumps from $0.5$ to $0$).
- ✅ **Utility-preserving** ($D(x) = x$ on $[0, 0.5)$).
- ✅ **Complete** ($f(D(x)) < 0.5$ for all $x$).

The theorem fails because the fixed-point set of $D$ is $\{0\} \cup [0, 0.5)$, which is *not closed* — closure would include $0.5$, but $D(0.5) = 0 \neq 0.5$. [Step 1](/boundary-proof) of the proof requires Hausdorff + continuity to close the fixed-point set; without continuity, that closure fails.
</div>

<div class="thm">
<div class="thm-title">Counterexample 3 — Removing utility preservation</div>

Any space $X$ with a fixed safe point $x_0 \in S_\tau$. Define $D(x) = x_0$ for all $x$.

- ✅ **Continuous** (constant maps are continuous).
- ❌ **Not utility-preserving** ($D(x) \neq x$ for $x \neq x_0$).
- ✅ **Complete** ($f(D(x)) = f(x_0) < \tau$).

The theorem fails because the fixed-point set is just $\{x_0\}$, which doesn't contain $S_\tau$. [Step 2](/boundary-proof) of the proof requires utility preservation to push $S_\tau$ inside $\mathrm{Fix}(D)$; without it, there's no need for any boundary fixation.

::: warning But this is not a real defense
A constant defense returns the same response for *every* prompt — every safe query collapses to $x_0$ as well. The reason the paper uses utility preservation rather than just $D(S_\tau) \subseteq S_\tau$ is exactly to rule out this trivial "defense": see Remark 4.5 (relaxed utility preservation).
:::
</div>

## The point of these counterexamples

Without any of the three hypotheses, a complete defense exists. With all three, none does. The hypotheses are individually necessary — meaning we cannot drop any of them and still get the impossibility.

This is the difference between a *robust* impossibility theorem and a *fragile* one. The boundary fixation theorem is robust: it isolates the **minimal** set of conditions that force failure. Each is independently load-bearing, and dropping any single one provides a concrete escape.

::: tip Designing around the impossibility
Each counterexample is also an *escape route* for defense designers:

1. **Discontinuous defense**: hard blocklists, classifier-based reject systems.
2. **Disconnected prompt space**: not realistic for language, but applies to discrete-token settings with strict tokenizer-level filtering.
3. **Defenses that sacrifice utility**: aggressive paraphrasing, conservative refusals.

The paper's [engineering prescription](/engineering) makes this concrete: don't try to satisfy all three properties; pick the one to give up.
:::
