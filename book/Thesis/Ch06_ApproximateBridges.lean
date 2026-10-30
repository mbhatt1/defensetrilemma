import VersoManual
import Thesis.Ch01_Diagonal
-- The quantitative results of this chapter are statements about real intervals,
-- so unlike the diagonal chapters it elaborates against `Mathlib`.
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "Approximate Bridges to Real Models" =>

The impossibility theorems of Chapter 3 are exact. They assume confidence that
is a perfect biconditional function of correctness, a probe that never misfires,
a confidence field crossing the truth boundary cleanly. No deployed system meets
any of these.

That reaction is wrong, and this chapter is the argument. The strict statement
is the `ε = 0` corner of a family of quantitative statements, each assuming only
an error budget and each surviving it with a weakened but nonempty conclusion.
The contradiction does not evaporate as the idealizations relax.

Everything is verified in two developments: the calibration bridges in
`HoF_12_Approximate`, the metric degradation law in
`F_09_QuantitativeDegradation`. Both import Mathlib, so the theorems are cited
by verified name and proved here in prose; genuinely finite fragments carry the
prefix `c6_` and are elaborated as this document builds.

Why the effort is worth it: a skeptic can dismiss a theorem about a model that
does not exist, but not one whose hypotheses are an error budget their own model
satisfies. Once calibration is granted only within `ε`, coverage only outside a
band, and universality only up to a distance, the hypotheses become measurable
properties of a shipped system rather than idealizations, and the conclusion
transfers to it. That is the difference between a result in a seminar and one in
a deployment review.

# What the exact theorems assume

A model is `M : Q → A × ℝ`, with answer `(M q).1` and confidence `(M q).2`.
Correctness is a signed _truth-distance field_ `δ : Q × A → ℝ`, negative when
the answer is correct, positive when wrong, zero on the boundary; write `δ(q)`
for `δ(q, (M q).1)`. Fix a threshold `c`, running value `1/2`.

_Strict calibration_ is the biconditional `conf(q) > c ↔ δ(q) < 0` and `conf(q) < c ↔ δ(q) > 0`,
verified as `StrictCalibrated`. _Faithfulness_ says `conf(q) ≥ c → δ(q) < 0`,
verified as `TrilemmaFaithful`. _Coverage_ says the truth-distance takes both
signs, verified as `TrilemmaCovering`.

Under these, plus continuity of the confidence map and connectedness of `Q`, the
strict trilemma derives `False`: coverage forces confidence above and below `c`,
continuity forces a crossing at `conf = c`, and there calibration and
faithfulness give incompatible signs for `δ`.

Two hypotheses a practitioner will defend are worth defending before weakening.
Continuity is not exotic: a confidence computed from a softmax over logits
smooth in a continuous embedding is continuous in that embedding, and the drift
a deployment sees — paraphrase, added context, distribution shift — moves
through embedding space rather than teleporting. Connectedness is subtler and is
what Chapter 4 spends its effort on; the short version is that after embedding,
the reachable region is path-connected often enough for the IVT to bite.

The sign convention drives every inequality. Negative truth-distance is good,
and `|δ(q)|` is how far the answer sits from the boundary, so a large negative
value is confidently correct and a value near zero is on the knife's edge.
Confidence runs the same way relative to `c`. Calibration claims the two axes
agree in sign, and this chapter is about how much they may disagree near the
origin of both.

# Two-sided ε-calibration

Real calibration curves do not flip at a point. Close to `δ = 0` the model is
genuinely uncertain, confidence hovers near `c`, and small perturbations move it
across the threshold with no reliable relation to correctness. The honest
weakening demands nothing in that neighborhood.

*Definition 6.1 (Two-sided ε-calibration).* _Fix `ε ≥ 0`. `M` is_ ε-calibrated _at
`c` if `δ(q) < -ε → conf(q) > c + ε` and `δ(q) > ε → conf(q) < c - ε`, for all
`q`. The verified predicate is `EpsCalibrated M δ c ε`._

*Proposition 6.2 (Contrapositives).* _ε-calibration is equivalent to
`conf(q) ≤ c + ε → δ(q) ≥ -ε` together with `conf(q) ≥ c - ε → δ(q) ≤ ε`._

_Proof._ Each line is the contrapositive of one clause, and contraposition over a
linear order is an equivalence. ∎

*Remark 6.3.* At `ε = 0` the clauses become the two forward implications of strict
calibration, the half the IVT argument uses. The verified
`strictCalibrated_to_epsCalibrated_zero_half` shows `StrictCalibrated` implies
`EpsCalibrated M δ (1/2) 0`, so nothing is lost by working in the weaker
vocabulary from the start.

*Example 6.4 (Reading an ε off a calibration table).* Bin a model's answers by
measured accuracy and reported confidence, normalized so `c = 0.5`. If every
answer below truth-distance `-0.1` reports confidence above `0.6`, and every
answer above `0.1` reports below `0.4`, the model is `ε`-calibrated with `ε = 0.1`.
Inside those bands the table may be ragged; the definition demands nothing
there.

*Definition 6.5 (ε-coverage).* _`M` is_ ε-covering _if some `q_t` has `δ(q_t) < -ε`
and some `q_f` has `δ(q_f) > ε`. The verified predicate is `EpsCovering M δ ε`._

The subscripts read "true" and "false": questions the model gets solidly right
and solidly wrong, both far enough from the boundary that ε-calibration applies.
At `ε = 0` this is ordinary coverage.

*Example 6.5b (Coverage bounds usable ε).* If the easiest true question sits at
`-0.3` and the easiest false one at `0.3`, ε-coverage holds for any `ε < 0.3`.
But if the domain is hard and the most solidly-true question is only at `-0.08`,
you cannot claim ε-coverage for `ε ≥ 0.08`, and the bridge runs only with a
smaller slack than your calibration might support.

# The approximate trilemma

*Theorem 6.6 (Approximate Hallucination Trilemma).* _Let `Q` be connected, the
confidence continuous, and `ε ≥ 0`. If `M` is ε-covering, ε-calibrated at `c`,
and threshold-inclusive faithful, then some `q₀` has `conf(q₀) = c` and `δ(q₀) ∈ [-ε, 0)`._

_Proof._ Coverage gives `q_t` with `δ(q_t) < -ε` and `q_f` with `δ(q_f) > ε`.
Calibration turns these into `conf(q_t) > c + ε` and `conf(q_f) < c - ε`, so the
continuous confidence is above and below `c` and the IVT lands `q₀` with
`conf(q₀) = c`. Calibration's contrapositive at `q₀` gives `δ(q₀) ≥ -ε`;
faithfulness, applicable since `conf(q₀) = c ≥ c`, gives `δ(q₀) < 0`. ∎

*Remark 6.7 (Why the interval is half-open).* The lower end is attained in
principle; the upper end is not. The strict `< 0` comes from faithfulness, which
forbids confident correctness from touching the boundary; the weak `≥ -ε` comes
from calibration, which only bounds how far below the boundary a low-confidence
question sits. The asymmetry is what lets `ε → 0` recover a genuine
contradiction rather than a degenerate point.

*Example 6.8 (A concrete margin).* With `c = 0.5` and the `ε = 0.1` model, Theorem
6.6 guarantees a question where the model reports confidence exactly `0.5` and
is correct with truth-distance in `[-0.1, 0)` — right, but only just, while
reporting a coin flip's confidence. Improving to `ε = 0.03` tightens the margin
without removing the question.

*Example 6.8b (Tracing the intermediate value step).* On `[0,1]` let
`conf(q) = 1 - q` and `δ(q) = q - 0.55`, with `c = 0.5`, `ε = 0.1`. Coverage
holds at `q = 0` (`δ = -0.55 < -0.1`) and `q = 1` (`δ = 0.45 > 0.1`). Confidence
hits `c` at `q = 0.5`, where `δ = -0.05`, which lies in `[-0.1, 0)` exactly as
the theorem predicts: correct by five hundredths while reporting a coin flip.

# Recovering the exact contradiction

*Theorem 6.9 (Exact contradiction from the approximate bridge).* _Under Theorem
6.6's hypotheses at `ε = 0`, one derives `False`. Verified as
`exact_from_approx`._

_Proof._ Theorem 6.6 returns `δ(q₀) ∈ [0, 0)`, which is empty. ∎

*Theorem 6.10 (Strict calibration through the bridge).* _Strict biconditional
calibration, ordinary coverage, and threshold-inclusive faithfulness on a
connected space with continuous confidence give `False`. Verified as
`exact_from_strictCalibrated_via_approx`._

_Proof._ Convert to zero-slack approximate hypotheses by Remark 6.3 and apply
Theorem 6.9. ∎

*Remark 6.11.* Theorem 6.10 needs continuity only of the confidence map, not of the
answer or truth field, because the IVT step is applied to confidence alone. This
economy is a direct benefit of factoring through the bridge, which exposes
exactly which map must be continuous.

*Remark 6.11b (The diagonal is still underneath).* It can look as though the bridge
traded the diagonal for the IVT and self-reference left the room. It did not.
The forced `q₀` is the `liar_query` witness `a₀` in analytic clothes. There,
`a₀` is the index where the self-verdict must equal its own negation, impossible
because negation has no fixed point. Here, `q₀` is where confidence must equal
the threshold, the one fixed point of the real complement. Same object, two
controllers.

# The tightening principle

*Theorem 6.12 (Tightening principle).* _If `M` is faithful, ε-covering, and both
`ε₁`- and `ε₂`-calibrated with `0 ≤ ε₂ ≤ ε₁`, the forced question from the `ε₂`
bridge has `δ ∈ [-ε₂, 0) ⊆ [-ε₁, 0)`. Improving calibration cannot loosen the
bound, and any strict improvement strictly tightens it._

```lean
theorem c6_tightening (ε₁ ε₂ : ℝ) (h : ε₂ ≤ ε₁) :
    Set.Ico (-ε₂) 0 ⊆ Set.Ico (-ε₁) 0 := by
  intro x hx
  exact ⟨by linarith [hx.1], hx.2⟩

theorem c6_margin_bound (ε₂ x : ℝ)
    (hx : x ∈ Set.Ico (-ε₂) 0) :
    |x| ≤ ε₂ := by
  rw [abs_of_neg hx.2]
  linarith [hx.1]
```

_Proof._ The interval inclusion is {lean}`c6_tightening` and the margin bound
{lean}`c6_margin_bound`, both pure order arithmetic. ∎

*Remark 6.13 (Calibration and faithfulness are not independent dials).* A tempting
mental model treats them as separate knobs each tunable to perfection.
Faithfulness fixes the sign of `δ(q₀)` and calibration fixes its magnitude, and
together they pin `δ(q₀)` into a shrinking interval the strict theorem shows
must eventually be empty. You cannot hold faithfulness fixed and drive
calibration to perfection.

*Example 6.14 (Spending the budget).* A program halving `ε` each quarter — `0.1`,
`0.05`, `0.025`, `0.0125` — tracks the guaranteed margin down the same sequence.
After a year the model is superbly calibrated and its forced fence-sitting
question is correct by at most `0.0125` while reporting exactly threshold
confidence. The program did not eliminate the question; it manufactured one on
which the model is correct by an amount too small to matter.

*Remark 6.14b (Where the naive optimization goes).* A team optimizing calibration
alone drives `ε` down until the shell `[-ε, 0)` is thinner than the resolution
of the training signal, at which point further calibration cannot be achieved by
more of the same. The bridge predicts the wall before the team hits it.

# Localization to the transition band

*Proposition 6.15 (Localization).* _Under Theorem 6.6's hypotheses, every forced
`q₀` lies outside `{conf > c + ε}` and `{conf < c - ε}`, hence in the transition
band `{c - ε ≤ conf ≤ c + ε}`._

```lean
theorem c6_localization (c ε : ℝ) (hε : 0 ≤ ε) :
    c ∈ Set.Icc (c - ε) (c + ε) ∧ ¬ (c > c + ε) ∧ ¬
    (c < c - ε) :=
  ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
```

_Proof._ `conf(q₀) = c`, and {lean}`c6_localization` places `c` in the band and
outside both decisive regions. ∎

Localization is what makes the margin actionable. The forced question is not
scattered anywhere in the space; it sits where the model reports near-threshold
confidence, which is a region a deployment can monitor.

# The discrete band constraint

*Theorem 6.16 (Discrete band constraint).* _On any sets, with no topology and no
finiteness, if `M` is ε-calibrated at `c` and threshold-inclusive faithful, then
any `q` with `c ≤ conf(q) ≤ c + ε` has `δ(q) ∈ [-ε, 0)`. Verified as
`discrete_approx_bridge`._

```lean
theorem c6_band (dq confq c eps : Int)
    -- ε-calibration, lower clause
    (hcal : dq < -eps → confq > c + eps)
    -- c-faithfulness
    (hfaith : confq ≥ c → dq < 0)
    -- upper half of the band
    (hge : confq ≥ c)
    -- not above the band
    (hle : confq ≤ c + eps) :
    -eps ≤ dq ∧ dq < 0 := by
  refine ⟨?_, hfaith hge⟩
  rcases Int.lt_or_le dq (-eps) with h | h
  · have := hcal h; omega
  · exact h
```

_Proof._ Faithfulness gives `δ(q) < 0`. For the lower bound, if `δ(q) < -ε` then
calibration forces `conf(q) > c + ε`, contradicting the band. The integer
transcription is {lean}`c6_band`, whose proof is two cases and `omega`. ∎

*Corollary 6.17 (No boundary point in the upper band).* _No `q` with
`c ≤ conf(q) ≤ c + ε` has `δ(q) = 0`. Verified as `no_boundary_in_upper_band`._

```lean
theorem c6_exact (dq confq c : Int)
    (hcal : dq < 0 → confq > c)
    (hfaith : confq ≥ c → dq < 0)
    (hge : confq ≥ c)
    (hle : confq ≤ c) : False := by
  have h1 : dq < 0 := hfaith hge
  have h2 : confq > c := hcal h1
  omega
```

_Proof._ Theorem 6.16 gives `δ(q) < 0`. At `ε = 0` the band collapses to
`conf(q) = c` and the constraint becomes the contradiction {lean}`c6_exact`. ∎

The discrete bridge matters because it needs no connectedness and no continuity.
It does not manufacture the band-crossing question; it constrains any question
that happens to land there. Where the continuous bridge derives the forced
question and then bounds it, the discrete one bounds whatever the deployment
observes.

# Two-slack separation

Confidence and truth-distance live in different units, and a single `ε`
conflates them.

*Definition 6.18 (Two-slack separation).* _Fix a truth slack `ε` and a confidence
margin `γ`. `M` is_ two-slack separating _at `c` if `δ(q) < -ε → conf(q) > c + γ`
and `δ(q) > ε → conf(q) < c - γ`. The verified predicate is
`TwoSlackSeparating`, with `EpsCalibrated` the case `γ = ε`._

*Theorem 6.19 (Two-slack coupling).* _On a connected space with continuous
confidence, if `M` is ε-covering, two-slack separating with `γ ≥ 0`, and
threshold-inclusive faithful, some `q₀` has `conf(q₀) = c` and `δ(q₀) ∈ [-ε, 0)`.
Verified as `two_slack_approx_coupling`._

_Proof._ Identical in shape to Theorem 6.6, with `γ` doing on the confidence side
what `ε` did. ∎

*Example 6.19b (Two slacks with numbers).* Report confidence on `0` to `100` with
`c = 50`, and truth-distance on a `0` to `1` semantic scale. If clearly-true
questions score above `70` and clearly-false ones below `30`, the model is
two-slack separating with `ε = 0.1` and `γ = 20`. The two numbers live in
different worlds, and keeping them separate is what lets each be measured in its
own units.

*Theorem 6.20 (The truth slack must be positive).* _Under two-slack separation with
any `γ ≥ 0`, ε-coverage, and threshold-inclusive faithfulness on a connected
space with continuous confidence, `ε > 0`. Verified as
`truth_slack_must_be_positive`._

_Proof._ At `ε = 0` Theorem 6.19 returns `δ(q₀) ∈ [0, 0)`, empty. ∎

This is the budget statement. A system keeping a threshold-inclusive guarantee
must carry a strictly positive margin of correctness on the confident side, and
the infimum of feasible slack is a measurable width of its truth boundary.

*Theorem 6.21 (Two-slack band bridge).* _On any sets, under two-slack separation and
threshold-inclusive faithfulness, any `q` with `c ≤ conf(q) ≤ c + γ` has `δ(q) ∈ [-ε, 0)`.
Verified as `two_slack_band_bridge`, with
`no_boundary_in_upper_band_two_slack`._

_Proof._ Theorem 6.16 with `c + γ` for `c + ε`. ∎

*Remark 6.22 (Axioms).* The two-slack results each print `#print axioms`. They rest
on the classical and quotient axioms Mathlib's real analysis uses and nothing
model-specific. The discrete bridges, being pure order arithmetic, are lightest;
the continuous ones inherit the IVT's dependencies. The core-Lean `c6_`
fragments use none beyond computation.

# The quantitative degradation law

*Definition 6.23 (ε-approximate universality).* _`M` is ε-approximately universal if
for every target `g` some prompt `a` has `dist (M a b) (g b) ≤ ε` for all `b`.
The verified predicate is `ApproxUniversal M ε`._

At `ε = 0` in a metric space this is ordinary curried surjectivity. For `ε > 0`
it is the honest claim: the system can be steered near any behavior, not onto
it.

*Theorem 6.24 (Approximate Lawvere).* _If `M` is ε-approximately universal, every
`t : Y → Y` has an approximate self-fixed-point: some `a` with `dist (M a a) (t (M a a)) ≤ ε`.
Verified as `approx_lawvere`._

_Proof._ Apply ε-universality to the diagonal target `g b = t (M b b)` and
instantiate at `b = a`. ∎

*Theorem 6.25 (Quantitative degradation).* _Let `M` be ε-approximately universal,
let `dist (M a a) (introspect a) ≤ δ` for all `a`, and let `t` be `1`-Lipschitz.
Then some `a` has `dist (introspect a) (t (introspect a)) ≤ ε + 2δ`. Verified as
`quantitative_trilemma`._

```lean
theorem c6_triangle_bound
    (goal d1 d2 d3 eps del : Int)
    (htri : goal ≤ d1 + d2 + d3)
    (hd1 : d1 ≤ del) (hd2 : d2 ≤ eps) (hd3 : d3 ≤ del) :
    goal ≤ eps + 2 * del := by omega
```

_Proof._ Three legs: from `introspect a` to `M a a` costs `δ`, from there to
`t (M a a)` costs `ε` by Theorem 6.24, and from there to `t (introspect a)`
costs `δ` again since `t` is `1`-Lipschitz. The arithmetic is
{lean}`c6_triangle_bound`. ∎

*Theorem 6.26 (Achievable region).* _If additionally
`dist (introspect a) (t (introspect a)) > γ` for all `a`, then `γ < ε + 2δ`. The
achievable triples lie in `{γ ≤ ε + 2δ}`. Verified as `achievable_region_bound`,
with `quantitative_impossibility` when `γ ≥ ε + 2δ`._

_Proof._ Theorem 6.25 gives an `a` where the distance is at most `ε + 2δ`, and the
hypothesis says it exceeds `γ`. ∎

*Theorem 6.27 (Strict limit).* _At `ε = δ = 0`, any nontrivial `γ > 0` gives `False`.
Verified as `strict_limit_recovers_trilemma`._

```lean
theorem c6_strict_collapse
    (goal margin : Int)
    (hbound : goal ≤ 0 + 2 * 0)
    (hmargin : goal > margin) :
    margin < 0 := by omega
```

_Proof._ Substituting into Theorem 6.26 gives `γ < 0`, the collapse
{lean}`c6_strict_collapse`. ∎

*Remark 6.27b (What a K-Lipschitz controller costs).* If `t` is `K`-Lipschitz, the
middle leg is bounded by `Kδ` rather than `δ`, so the budget becomes `ε + (1 + K)δ`,
recovering `ε + 2δ` at `K = 1`. A controller amplifying differences has a larger
achievable region, which is to say it is easier to satisfy and correspondingly
says less.

*Remark 6.28 (Two shapes of the same fact).* The calibration bridge and the
degradation law relax different idealizations and produce differently-shaped
budgets, an interval and a half-space, but the mechanism is one: take the exact
diagonal, insert a slack at each idealized equality, and carry the slacks
through by linear arithmetic to a conclusion nonempty for positive slack and
contradictory at zero.

# From existence to measure

*Example 6.29 (A risk estimate with numbers).* Take the `ε = 0.05` model, so any
forced question is correct by at most `0.05` and sits in the band `conf ∈ [0.45, 0.55]`.
If Chapter 5's geometry reports that the band has basin volume `2%` of the input
space and the deployment's query distribution puts `0.5%` of its mass there,
then roughly one query in two hundred lands in the band, and there the model is
correct by a margin no larger than `0.05` while reporting a coin flip.

*Remark 6.30 (What the composite can and cannot claim).* The estimate bounds a very
specific quantity, the incidence and severity of forced threshold-confidence
questions. It is not a claim about all model errors. Errors far from the band
are ordinary mistakes the bridge says nothing about. What it captures is the
irreducible residue: errors existing not because the model is undertrained but
because faithfulness, calibration, coverage, and continuity cannot all hold.

*Example 6.29b (The adversarial reading).* Benignly, a random query lands in the band
with the concentration probability. Adversarially, an attacker does not wait for
random traffic but steers, and Chapter 5's hitting-time and gradient bounds say
how cheaply an input can be nudged from a confidently-handled region into the
band. The bridge's localization tells the attacker exactly where to aim, which
is why the benign incidence figure is the wrong number for a security case.

*Remark 6.31 (The whole bridge in one sentence).* The exact impossibility is the
zero-slack corner of a quantitative law; the law's conclusion is a nonempty
margin rather than a contradiction; the margin tightens as the model improves
rather than vanishing; it is localized to the transition band rather than spread
everywhere; and Chapter 5's geometry turns the located margin into a rate.

# The reading is where the work is

Every theorem here has the same shape: a hypothesis that is an error budget, a
conclusion that is a bound, and a limit at zero slack that recovers the exact
statement. What the chapter does not do is tell you what `ε`, `γ`, or `δ` are
for your system. Those are measurements, and the bridge is only as informative
as they are honest.

# Historical notes

The strategy of relaxing an exact impossibility to a quantitative law with a
recoverable limit is standard in approximation theory and in the
robust-statistics tradition, and the specific bridges here are the companion
libraries' `HoF_12_Approximate` and `F_09_QuantitativeDegradation`. The
approximate Lawvere theorem is the metric shadow of Chapter 1's engine, and the
`ε + 2δ` budget is a triangle inequality with the diagonal in the middle leg.
Where prose and Lean differ, the Lean is authoritative.
