# The Engineering Prescription

The results do not say defense is valueless. They say *complete* defense is impossible under continuity + utility preservation. The engineering goal shifts from elimination to **management**, ordered from most to least actionable.

<div class="diagram">

<svg viewBox="0 0 760 420" xmlns="http://www.w3.org/2000/svg">
  <!-- Vertical axis: actionability -->
  <text x="35" y="220" class="label label-bold" text-anchor="middle" transform="rotate(-90, 35, 220)">Actionability →</text>

  <!-- Strategy 1: highest -->
  <rect x="80" y="40" width="640" height="80" rx="10" fill="rgba(56, 161, 105, 0.1)" stroke="#38a169" stroke-width="2"/>
  <circle cx="120" cy="80" r="22" fill="#38a169"/>
  <text x="120" y="86" class="label label-bold" text-anchor="middle" fill="white" font-size="16">1</text>
  <text x="160" y="68" class="label label-bold" font-size="13">Make the boundary shallow</text>
  <text x="160" y="88" class="label-small">Set τ so that boundary-level behavior is benign. If f(z) = τ yields a polite refusal,</text>
  <text x="160" y="103" class="label-small">the impossibility is mathematically true but practically harmless.</text>
  <text x="710" y="113" class="label-small" text-anchor="end" font-style="italic" fill="#1c5b34">GPT-5-Mini exemplifies this</text>

  <!-- Strategy 2 -->
  <rect x="80" y="135" width="640" height="80" rx="10" fill="rgba(214, 158, 46, 0.1)" stroke="#d69e2e" stroke-width="2"/>
  <circle cx="120" cy="175" r="22" fill="#d69e2e"/>
  <text x="120" y="181" class="label label-bold" text-anchor="middle" fill="white" font-size="16">2</text>
  <text x="160" y="163" class="label label-bold" font-size="13">Reduce the Lipschitz constant L</text>
  <text x="160" y="183" class="label-small">Smoother f tightens ℓ ≤ L, narrowing the persistent region.</text>
  <text x="160" y="198" class="label-small">Tradeoff: spreads vulnerabilities over wider but more easily monitored regions.</text>

  <!-- Strategy 3 -->
  <rect x="80" y="230" width="640" height="80" rx="10" fill="rgba(176, 65, 62, 0.1)" stroke="#b0413e" stroke-width="2"/>
  <circle cx="120" cy="270" r="22" fill="#b0413e"/>
  <text x="120" y="276" class="label label-bold" text-anchor="middle" fill="white" font-size="16">3</text>
  <text x="160" y="258" class="label label-bold" font-size="13">Reduce the effective dimension d</text>
  <text x="160" y="278" class="label-small">Defense cost grows as N^d. Constraining the prompt interface (formats, API params,</text>
  <text x="160" y="293" class="label-small">context length) shrinks d, making the behavioral space tractable.</text>

  <!-- Strategy 4 -->
  <rect x="80" y="325" width="640" height="80" rx="10" fill="rgba(43, 108, 176, 0.1)" stroke="#2b6cb0" stroke-width="2"/>
  <circle cx="120" cy="365" r="22" fill="#2b6cb0"/>
  <text x="120" y="371" class="label label-bold" text-anchor="middle" fill="white" font-size="16">4</text>
  <text x="160" y="353" class="label label-bold" font-size="13">Monitor, don't eliminate, the boundary</text>
  <text x="160" y="373" class="label-small">Transversal crossings persist under fine-tuning and recur every turn. Deploy runtime</text>
  <text x="160" y="388" class="label-small">monitoring that detects approach to the boundary using the Lipschitz radius bound.</text>
</svg>

<p class="diagram-caption">
  Four strategies for managing the boundary, ordered from most to least actionable. The top three reshape the alignment surface itself; the fourth accepts that boundary failures are inevitable and instruments around them.
</p>

</div>

## Strategy 1: Make the boundary shallow

**The cleanest escape.** If you choose your safety threshold $\tau$ so that *behavior at exactly $f(x) = \tau$* is benign — e.g., a polite refusal rather than harmful compliance — then boundary fixation still happens, but the fixed boundary point produces benign output. The theorem is true; its consequence is harmless.

**Cost:** none, if the model can be made to refuse politely at the boundary. This is what GPT-5-Mini achieves: its peak observed AD is exactly $\tau = 0.5$, which corresponds to refusal-style outputs. The unsafe region is empty under that threshold, and the impossibility theorem stays silent.

## Strategy 2: Reduce the Lipschitz constant

The persistence theorem requires $G > \ell(K+1)$, where $G$ is the directional gradient at the boundary and $\ell$ is the defense-path Lipschitz constant. Smaller $L$ for the alignment surface means smaller possible $\ell$ — a narrower persistent region.

**Tradeoff:** smoother surfaces have *wider* ε-bands. Vulnerabilities don't disappear; they spread over a larger area. The advantage is that wider regions are easier to monitor with fewer probe points.

::: tip How to make L smaller in practice
Training-time techniques that flatten the alignment surface — regularization, gradient penalties, smoothness-aware losses — directly reduce $L$. Adversarial training also tends to smooth the surface near the decision boundary.
:::

## Strategy 3: Reduce the effective dimension

The cost asymmetry theorem (Thm A.6) gives:

$$\text{defense cost} = N^d, \quad \text{attack cost} \leq 1/\delta$$

Defense cost is exponential in dimension; attack cost is dimension-independent. At $d = 2$, $N = 25$, $\delta = 0.01$, the ratio is $6.25$. At $d = 10$, it climbs to $\sim 10^{12}$.

**The actionable lever:** constrain the prompt interface itself.

- Standardized formats reduce free-form input dimensionality.
- Restricted API parameters reduce the attack surface.
- Bounded context lengths reduce $d$ multiplicatively.

This shifts the defense from "search a 10D behavioral space" to "search a 2D one." The same number of grid probes covers vastly more of the space.

## Strategy 4: Monitor, don't eliminate

Transversal crossings persist under fine-tuning (Thm A.7, Crossing Preservation) and recur every turn (Thm 9.1, Multi-Turn Impossibility). Trying to eliminate them is fighting topology. Instead:

- Deploy **runtime AD estimators** at the model's input.
- Use the Lipschitz radius bound (Thm A.6.1): if $f(p) > \tau$, then a ball of radius $(f(p) - \tau)/L$ around $p$ is also unsafe. This gives a *computable* distance-to-boundary from any observed AD value.
- When the radius shrinks, the input is approaching the boundary — escalate to a stricter mode (refusal, human review, alternate model).

## What NOT to attempt

The paper rules out a specific class of defenses. Here is what's *not* covered, and therefore not subject to the impossibility:

| Mechanism | Why it escapes |
|---|---|
| **Training-time alignment** (RLHF, DPO, constitutional AI training) | Modifies $f$, not $D$. The theorem is silent on what alignment is achievable, only on what wrappers around a fixed model can achieve. |
| **Architectural changes** | Changes the model itself, not its wrapper. |
| **Discontinuous defenses** (hard blocklists, classifier reject systems) | Drops continuity → counterexample 2. |
| **Defenses that sacrifice utility** (aggressive paraphrase, conservative refusals) | Drops utility preservation → counterexample 3. |
| **Multi-component systems with rejection** | Not a single map $D : X \to X$. |
| **Output-side filters** | Apply after the model, not as a wrapper around its input. |
| **Human-in-the-loop review** | Not a continuous function. |

::: warning But each escape has its own cost
Discontinuous defenses are brittle (small input perturbations may flip the classification). Refusal-heavy defenses degrade utility. Output filters require reliable post-hoc detection. The impossibility theorem is not a recommendation to abandon defenses — it's a statement that the *clean* form of wrapper defense doesn't exist, so you must explicitly choose which property to give up.
:::

## Summary

| Strategy | Property reshaped | When it works |
|---|---|---|
| 1. Shallow boundary | $\tau$ chosen so τ-level is benign | When the model can refuse cleanly |
| 2. Smaller L | $f$ flattened by training | When training-time techniques are available |
| 3. Smaller d | Prompt interface constrained | When the application supports it |
| 4. Runtime monitor | Distance-to-boundary tracked | Always (instrumentation is cheap) |

→ The full mechanically verified theory backing all of this is on the [Lean artifact page](/lean-artifact).
