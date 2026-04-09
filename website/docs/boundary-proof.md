# Boundary Fixation: The Proof Chain

The proof of Theorem 4.1 is two independent chains of reasoning that converge on the same conclusion. One chain extracts a closed set from continuity + utility preservation; the other extracts a non-closed set from connectedness. The contradiction at the meeting point produces the fixed boundary point.

<div class="diagram">

<svg viewBox="0 0 760 460" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <marker id="arr" markerWidth="10" markerHeight="10" refX="9" refY="5" orient="auto">
      <polygon points="0 0, 10 5, 0 10" fill="currentColor" />
    </marker>
  </defs>

  <!-- Title bar -->
  <text x="380" y="22" class="label label-bold" text-anchor="middle" font-size="13">
    Theorem 4.1: Two chains converge on the boundary
  </text>

  <!-- LEFT CHAIN: closure -->
  <g>
    <rect x="40" y="50" width="280" height="60" rx="8" fill="#d4f5dd" stroke="#38a169" stroke-width="1.5" />
    <text x="180" y="74" class="label label-bold" text-anchor="middle" fill="#1c5b34">Hausdorff space X</text>
    <text x="180" y="92" class="label-small" text-anchor="middle">Distinct points are separable</text>

    <line x1="180" y1="110" x2="180" y2="130" stroke="#38a169" stroke-width="2" marker-end="url(#arr)" color="#38a169" />

    <rect x="40" y="135" width="280" height="60" rx="8" fill="#d4f5dd" stroke="#38a169" stroke-width="1.5" />
    <text x="180" y="158" class="label label-bold" text-anchor="middle" fill="#1c5b34">Fix(D) is closed</text>
    <text x="180" y="178" class="label-small" text-anchor="middle">Diagonal is closed → preimage is closed</text>

    <line x1="180" y1="195" x2="180" y2="215" stroke="#38a169" stroke-width="2" marker-end="url(#arr)" color="#38a169" />

    <rect x="40" y="220" width="280" height="60" rx="8" fill="#d4f5dd" stroke="#38a169" stroke-width="1.5" />
    <text x="180" y="243" class="label label-bold" text-anchor="middle" fill="#1c5b34">S_τ ⊆ Fix(D)</text>
    <text x="180" y="263" class="label-small" text-anchor="middle">By utility preservation D|_S = id</text>

    <line x1="180" y1="280" x2="180" y2="300" stroke="#38a169" stroke-width="2" marker-end="url(#arr)" color="#38a169" />

    <rect x="40" y="305" width="280" height="60" rx="8" fill="#d4f5dd" stroke="#38a169" stroke-width="2" />
    <text x="180" y="328" class="label label-bold" text-anchor="middle" fill="#1c5b34">cl(S_τ) ⊆ Fix(D)</text>
    <text x="180" y="348" class="label-small" text-anchor="middle">Closure of subset of closed set</text>
  </g>

  <!-- RIGHT CHAIN: non-closedness -->
  <g>
    <rect x="440" y="50" width="280" height="60" rx="8" fill="#fbe2e2" stroke="#c53030" stroke-width="1.5" />
    <text x="580" y="74" class="label label-bold" text-anchor="middle" fill="#742a2a">Connected X</text>
    <text x="580" y="92" class="label-small" text-anchor="middle">Only clopens are ∅ and X</text>

    <line x1="580" y1="110" x2="580" y2="130" stroke="#c53030" stroke-width="2" marker-end="url(#arr)" color="#c53030" />

    <rect x="440" y="135" width="280" height="60" rx="8" fill="#fbe2e2" stroke="#c53030" stroke-width="1.5" />
    <text x="580" y="158" class="label label-bold" text-anchor="middle" fill="#742a2a">S_τ is open</text>
    <text x="580" y="178" class="label-small" text-anchor="middle">Preimage of (−∞, τ) under continuous f</text>

    <line x1="580" y1="195" x2="580" y2="215" stroke="#c53030" stroke-width="2" marker-end="url(#arr)" color="#c53030" />

    <rect x="440" y="220" width="280" height="60" rx="8" fill="#fbe2e2" stroke="#c53030" stroke-width="1.5" />
    <text x="580" y="243" class="label label-bold" text-anchor="middle" fill="#742a2a">S_τ ≠ ∅, S_τ ≠ X</text>
    <text x="580" y="263" class="label-small" text-anchor="middle">Both safe and unsafe inputs exist</text>

    <line x1="580" y1="280" x2="580" y2="300" stroke="#c53030" stroke-width="2" marker-end="url(#arr)" color="#c53030" />

    <rect x="440" y="305" width="280" height="60" rx="8" fill="#fbe2e2" stroke="#c53030" stroke-width="2" />
    <text x="580" y="328" class="label label-bold" text-anchor="middle" fill="#742a2a">S_τ is NOT closed</text>
    <text x="580" y="348" class="label-small" text-anchor="middle">Else clopen → ∅ or X (contradiction)</text>
  </g>

  <!-- Convergence arrows -->
  <line x1="180" y1="365" x2="350" y2="405" stroke="#b0413e" stroke-width="2.5" marker-end="url(#arr)" color="#b0413e" />
  <line x1="580" y1="365" x2="410" y2="405" stroke="#b0413e" stroke-width="2.5" marker-end="url(#arr)" color="#b0413e" />

  <!-- Bottom box: conclusion -->
  <rect x="240" y="410" width="280" height="42" rx="8" fill="rgba(176, 65, 62, 0.18)" stroke="#b0413e" stroke-width="2" />
  <text x="380" y="430" class="label label-bold" text-anchor="middle" fill="#b0413e">cl(S_τ) ⊋ S_τ</text>
  <text x="380" y="446" class="label-small" text-anchor="middle">∃ z ∈ cl(S_τ) ∖ S_τ:  f(z) = τ,  D(z) = z</text>
</svg>

<p class="diagram-caption">
  Two chains of reasoning, one extracting closedness from Hausdorff and utility preservation, the other extracting non-closedness from connectedness. Both target <code>S_τ</code>, and the gap between them — closed superset minus the open original — is exactly the boundary, where the defense must have fixed points.
</p>

</div>

## The five formal steps

<div class="thm">
<div class="thm-title">Theorem 4.1 — Boundary Fixation</div>

Let $X$ be a connected Hausdorff space. Let $f\colon X \to \mathbb{R}$ be continuous with $S_\tau, U_\tau \neq \emptyset$, and let $D\colon X \to X$ be continuous with $D|_{S_\tau} = \mathrm{id}$. Then there exists $z \in X$ with $f(z) = \tau$ and $D(z) = z$.
</div>

**Step 1.** *Hausdorff $\Rightarrow$ fixed-point set is closed.* The set $\mathrm{Fix}(D) = \{x : D(x) = x\}$ is the preimage of the diagonal $\Delta \subset X \times X$ under the continuous map $x \mapsto (D(x), x)$. In a Hausdorff space, $\Delta$ is closed, so $\mathrm{Fix}(D)$ is closed.

**Step 2.** *Utility preservation $\Rightarrow$ safe region $\subseteq$ fixed points.* By assumption $D(x) = x$ on $S_\tau$, so $S_\tau \subseteq \mathrm{Fix}(D)$. Since $\mathrm{Fix}(D)$ is closed, $\overline{S_\tau} \subseteq \mathrm{Fix}(D)$.

**Step 3.** *Connectedness $\Rightarrow$ safe region is not closed.* $S_\tau = f^{-1}((-\infty, \tau))$ is open (preimage of an open interval under continuous $f$). If it were also closed, it would be clopen — but in a connected space the only clopen sets are $\emptyset$ and $X$. Since both $S_\tau$ and $U_\tau$ are nonempty, $S_\tau$ is not closed.

**Step 4.** *Boundary point exists.* From steps 2 and 3: $\overline{S_\tau} \supsetneq S_\tau$, so there exists $z \in \overline{S_\tau} \setminus S_\tau$. Continuity of $f$ gives $f(z) \leq \tau$ (limit of values $< \tau$); $z \notin S_\tau$ gives $f(z) \geq \tau$. Hence $f(z) = \tau$.

**Step 5.** *Defense fixes the boundary point.* Since $z \in \overline{S_\tau} \subseteq \mathrm{Fix}(D)$, we have $D(z) = z$ and $f(D(z)) = f(z) = \tau$.

::: info Mechanically verified
This proof is checked in Lean 4 as `epsilon_robust_impossibility` in [`MoF_11_EpsilonRobust.lean`](https://github.com/mbhatt1/stuff/blob/main/ManifoldProofs/ManifoldProofs/MoF_11_EpsilonRobust.lean). No `sorry` statements; depends only on `propext`, `Classical.choice`, and `Quot.sound`.
:::

## Why each hypothesis is load-bearing

- **Drop Hausdorff:** $\mathrm{Fix}(D)$ might not be closed. The closure step in chain (1) fails.
- **Drop continuity (of $D$):** Same problem — the preimage of the diagonal might not be closed.
- **Drop utility preservation:** $S_\tau$ is no longer guaranteed to be inside $\mathrm{Fix}(D)$. Chain (1) collapses.
- **Drop connectedness:** $S_\tau$ might be clopen. Chain (2) collapses (the red chain hits a wall at step 3).

See the [counterexamples page](/counterexamples) for explicit instances of each failure.
