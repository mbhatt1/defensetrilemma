import VersoManual
import TrilemmaBook.Ch01_Diagonal
-- The quantitative results of this chapter are statements about real intervals,
-- so unlike the diagonal chapters it elaborates against `Mathlib`.
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "Approximate Bridges to Real Models" =>

The impossibility theorems of Chapter 3 are exact. They assume a model whose
confidence is a perfect biconditional function of its correctness, a probe that
never misfires, a truth boundary that the confidence field crosses cleanly. No
deployed system meets any of these assumptions. A practitioner who reads the
strict trilemma and then measures a real model will find calibration curves that
wobble, confidence that is only roughly monotone in accuracy, coverage that is
statistical rather than guaranteed. The natural reaction is to conclude that the
theorem is about an idealization and says nothing about the thing on the bench.

That reaction is wrong, and this chapter is the argument for why. The strict
statement is the `ε = 0` corner of a family of quantitative statements, each of
which assumes only an error budget and each of which survives that budget with a
weakened but nonempty conclusion. The exact contradiction does not evaporate as
the idealizations relax. It turns into a margin: a forced question on which the
model is correct, but correct by no more than the calibration error it was
allowed. Shrinking the error does not remove the forced question. It tightens the
margin toward the exact contradiction. This is the sense in which the idealized
theorem governs the real one.

Everything here is verified in two companion developments. The continuous and
discrete calibration bridges are `HoF_12_Approximate` in the hallucination
library; the metric degradation law is `F_09_QuantitativeDegradation` in the
Foundation library. Both import Mathlib and reason over the reals. The book's own
Lean package has no Mathlib, so the theorems below are cited by their verified
names and proved here in prose. Where a fragment of the argument is genuinely
finite, a small core-Lean illustration is included and elaborated when the book
is built; those carry the prefix `c6_`.

A word on why the effort is worth it. A skeptic can read Chapter 3 and say the
strict trilemma is a theorem about a model that does not exist, and dismiss it. The
same skeptic cannot dismiss a theorem whose hypotheses are an error budget the
skeptic's own model satisfies. Once calibration is granted only to within `ε`,
coverage only outside a band, and universality only up to a distance, the
hypotheses become measurable properties of a shipped system rather than
philosophical idealizations. The conclusion then transfers to that system. This is
the difference between a result that lives in a seminar and a result that lives in
a deployment review, and closing that difference is the whole purpose of the
chapter.

# What the exact theorems assume

It helps to name the idealizations before dismantling them. The strict
Hallucination Trilemma of Chapter 3 concerns a model that answers questions and
reports a confidence, together with a notion of how wrong each answer is.

Write `Q` for the space of questions and `A` for the space of answers. A model is
a map `M : Q → A × ℝ`. Reading `M q = (a, r)`, the answer is `a = (M q).1` and the
reported confidence is `r = (M q).2`, a real number. Correctness is measured by a
_truth-distance field_ `δ : Q × A → ℝ`. The value `δ(q, a)` is a signed distance
from the truth boundary: negative when the answer `a` is on the correct side for
question `q`, positive when it is wrong, zero exactly on the boundary. Throughout
we abbreviate the truth-distance of the model's own answer as `δ(q)`, meaning
`δ(q, (M q).1)`. Fix a threshold confidence `c`; the paper's running value is
`c = 1/2`, the point at which a report stops being a lean toward "no" and becomes
a lean toward "yes".

The strict theorem rests on three hypotheses.

_Strict calibration_ is a biconditional: `conf(q) > c ↔ δ(q) < 0` and
`conf(q) < c ↔ δ(q) > 0`. In words, the model reports above-threshold confidence
exactly when it is correct, and below-threshold confidence exactly when it is
wrong. This is the verified predicate `StrictCalibrated`.

_Faithfulness_ says the model does not confidently assert falsehoods: whenever
`conf(q) ≥ c`, the answer is on the correct side, `δ(q) < 0`. This is
`TrilemmaFaithful`.

_Coverage_ says the model is not trivial: some question is answered correctly and
some is answered wrongly, so the truth-distance field takes both signs. This is
`TrilemmaCovering`.

Under these three, plus continuity of the confidence map and connectedness of the
question space, the strict trilemma derives `False`. The mechanism is the one
from Chapter 1 read through the intermediate value theorem of Chapter 4: coverage
forces confidence above `c` somewhere and below `c` somewhere, continuity forces a
crossing where `conf = c`, and at that crossing calibration and faithfulness give
incompatible signs for `δ`. The verified endpoint is that the three corners
cannot all hold.

Two of these hypotheses are the ones a practitioner will instinctively defend, and
it is worth saying why they are reasonable before weakening them. Continuity of the
confidence map is not an exotic assumption. A confidence score computed from a
softmax over logits that are themselves smooth functions of a continuous embedding
is continuous in that embedding, and the input drift a deployment actually sees,
paraphrase, added context, distribution shift, moves through the embedding space
rather than teleporting across it. Connectedness of the question space is the
subtler assumption and the one Chapter 4 spends its effort on; the short version is
that after embedding, the reachable region of inputs is path-connected often enough
that the intermediate value theorem has something to bite on. The discrete bridge
below is the fallback for when it does not.

The sign convention deserves one more sentence, because it drives every inequality
that follows. Negative truth-distance is good: `δ(q) < 0` means the answer is on
the correct side of the boundary. Positive is bad. The magnitude `|δ(q)|` is how
far the answer sits from the truth boundary, so a large negative value is a
confidently correct answer and a value near zero is an answer on the knife's edge.
Confidence runs the same direction relative to `c`: above `c` is a lean toward
asserting, below `c` is a lean toward declining. Calibration is the claim that
these two axes agree in sign, and the whole chapter is about how much they are
allowed to disagree near the origin of both.

Now weaken each idealization by a budget and watch the contradiction bend rather
than break.

# Two-sided ε-calibration

Strict calibration is a biconditional pinned at a single point `c`. It demands
that the instant correctness flips sign, confidence flips side of the threshold,
with no tolerance. Real calibration curves do not behave like that near the
boundary. Close to `δ = 0` the model is genuinely uncertain, its confidence
hovers near `c`, and small perturbations of the question move confidence back and
forth across the threshold without any reliable relation to correctness. The
honest weakening is to stop demanding anything in that neighborhood and to keep
the demand only where the model has real signal.

**Definition 6.1 (Two-sided ε-calibration).** _Fix a slack `ε ≥ 0`. A model `M`
is_ ε-calibrated _at threshold `c` if_

- `δ(q) < -ε → conf(q) > c + ε` _for all `q`, and_
- `δ(q) > ε → conf(q) < c - ε` _for all `q`._

_The verified predicate is `EpsCalibrated M δ c ε`._

Read the first clause aloud. If an answer is _very_ correct, its truth-distance
below `-ε`, then its confidence must be _clearly_ above threshold, above `c + ε`.
The second clause is the mirror: very wrong answers get confidence clearly below
threshold. The band `δ(q) ∈ [-ε, ε]` is exempt. Inside it the model may report
any confidence at all. The band `conf(q) ∈ [c - ε, c + ε]` is where the model is
allowed to be confused.

Two features of this definition earn the word "honest".

First, it is one-directional. Strict calibration is a biconditional; ε-calibration
keeps only the direction the argument needs. It says correctness forces
confidence, not that confidence guarantees correctness. That is exactly the
direction a well-meaning model designer can hope to certify. You can imagine
measuring, on a held-out set, that answers you know to be very correct do come
with high confidence. You cannot as easily certify the converse, that every
high-confidence answer is correct, because that is a claim about the tails you
have not seen. Keeping only the certifiable direction is what makes the weakening
usable.

Second, the same `ε` sits on both the truth side and the confidence side. Very
correct means truth-distance beyond `ε`; clearly above means confidence beyond
`c + ε`. Using one parameter for both is a simplification, and Section
"Two-slack separation" below shows how to split it into a truth slack and a
confidence slack when the two live in different units. For now the single
parameter keeps the statements clean.

It helps to see why strict calibration is not merely inconvenient but empirically
false, so that the weakening reads as a correction rather than a retreat. A
reliability diagram bins predictions by reported confidence and plots, against
each bin, the observed frequency of correctness. Perfect strict calibration would
be the diagonal of that plot, and it would additionally require the crossing at
`c` to be exact: the confidence that separates correct from incorrect would have to
be a single sharp value with correctness flipping the instant confidence crosses
it. Real diagrams are never that. They sag or bow away from the diagonal, and near
the decision threshold they flatten, because that is exactly the region where the
model has the least signal and its confidence carries the least information about
correctness. The flat region near `c` is the empirical face of the exempt band.
ε-calibration is the diagram read honestly: it commits to the tails, where the
curve is informative, and stays silent in the middle, where it is not. A modeler
who has drawn a reliability diagram has already measured an `ε`; the definition
just names it.

There is a subtle trap the one-directional form avoids. If you demanded the full
biconditional even in ε form, you would be asserting that every high-confidence
answer is correct, which is a claim about the model's worst high-confidence
mistakes, the confident hallucinations. Those are precisely the events safety work
is trying to bound and cannot yet certify. ε-calibration never asks you to certify
them. It asks only the reverse, that answers you have independently verified to be
very correct come with high confidence, which you can check directly on a labeled
set. The theorem extracts its force from the certifiable direction and leaves the
uncertifiable direction alone, which is why its hypotheses survive contact with a
real evaluation.

Estimating `ε` from data is then a concrete procedure, and stating it makes the
whole chapter operational. Take a labeled evaluation set. For each example you know
the truth-distance sign and magnitude, at least in bins, and you observe the
reported confidence. Find the smallest `ε` such that every example with
truth-distance below `-ε` reports confidence above `c + ε`, and every example with
truth-distance above `ε` reports confidence below `c - ε`. That smallest `ε` is the
model's calibration budget on that set, the tightest slack the two clauses of
Definition 6.1 will tolerate. It is an empirical quantity, computable by scanning
the evaluation, and it is exactly the number the bridge consumes. A caveat rides
along: this `ε` is an estimate from a finite sample, so it inherits the usual
statistical uncertainty, and a prudent deployment inflates it to a high-confidence
upper bound before feeding it to the bridge. The bridge is monotone in `ε` in the
safe direction, a larger `ε` gives a weaker but still valid conclusion, so
over-estimating the budget never invalidates the guarantee; it only widens the
margin interval `[-ε, 0)` you have to live with.

The two clauses are most useful in their contrapositive form, and the verified
file records them as such.

**Proposition 6.2 (Contrapositives).** _ε-calibration is equivalent to the pair_

- `conf(q) ≤ c + ε → δ(q) ≥ -ε`, _and_
- `conf(q) ≥ c - ε → δ(q) ≤ ε`.

_Proof._ Each line is the contrapositive of one clause of Definition 6.1, and
contraposition over a linear order is an equivalence: `P → Q` is equivalent to
`¬Q → ¬P`, and the negation of `conf > c + ε` is `conf ≤ c + ε`, the negation of
`δ < -ε` is `δ ≥ -ε`. No arithmetic beyond trichotomy of `<` on `ℝ` is used. ∎

The contrapositive is the form the bridge theorems consume. It says: a question
whose confidence has not risen clearly above threshold cannot have been very
correct, its truth-distance is at least `-ε`. That is a lower bound on `δ`
extracted purely from a confidence observation, and it is the entire content of
the lower half of the approximate trilemma.

**Remark 6.3.** At `ε = 0` the two clauses become `δ(q) < 0 → conf(q) > c` and
`δ(q) > 0 → conf(q) < c`. These are precisely the two forward implications of
strict calibration, the half the intermediate value argument actually uses. The
verified `strictCalibrated_to_epsCalibrated_zero_half` shows that
`StrictCalibrated` implies `EpsCalibrated M δ (1/2) 0`, so strict calibration is
the zero-slack instance of the approximate notion and nothing is lost by working
in the weaker vocabulary from the start.

**Example 6.4 (Reading an ε off a calibration table).** Suppose you bin a model's
answers by measured accuracy and reported confidence, with confidence normalized
so `c = 0.5`. You find that every answer whose accuracy places it at
truth-distance below `-0.1` reports confidence above `0.6`, and every answer at
truth-distance above `0.1` reports confidence below `0.4`. Then the model is
`ε`-calibrated with `ε = 0.1`: the truth band is `[-0.1, 0.1]` and the confidence
band is `[0.4, 0.6]`. Inside those bands the table may be ragged and the
certificate says nothing. Outside them the certificate holds. A model with a
tighter table, say the same behavior already forced at truth-distance `0.03` and
confidence `0.53`, is `ε`-calibrated with `ε = 0.03`. Smaller `ε` is a better
model, and the whole point of the next sections is what "better" costs it.

# ε-coverage

Coverage also needs a budget. The strict version asks only that some answer is
correct and some is wrong. Near the boundary that is too weak to drive an
approximate argument, because a "correct" answer at truth-distance `-0.001`
carries essentially no confidence signal under ε-calibration. The approximate
argument needs witnesses that sit _outside_ the exempt band, where the
calibration clauses have teeth.

**Definition 6.5 (ε-coverage).** _A model `M` is_ ε-covering _if there is a
question `q_t` with `δ(q_t) < -ε` and a question `q_f` with `δ(q_f) > ε`. The
verified predicate is `EpsCovering M δ ε`._

The subscripts read as "true" and "false": `q_t` is a question the model gets
solidly right, `q_f` one it gets solidly wrong, both far enough from the boundary
that ε-calibration applies to them. At `ε = 0` this is ordinary coverage, and
`trilemmaCovering_to_epsCovering_zero` records that `TrilemmaCovering` implies
`EpsCovering M δ 0`.

The requirement is mild. Any model deployed on a domain broad enough to contain
both easy true instances and easy false instances is ε-covering for the `ε` that
separates them from the boundary. The failure mode is a model that only ever
operates in its own confused band, and such a model has no claim to being useful
in the first place.

**Example 6.5b (Coverage sets an upper bound on usable ε).** There is a hidden
interaction between the two witnesses that constrains how large an `ε` you may
claim. If the easiest true question you can find sits at truth-distance `-0.3` and
the easiest false one at `0.3`, then ε-coverage holds for any `ε < 0.3`, and you
are free to pick the `ε` that your calibration actually supports. But if your
domain is hard, so that the most solidly-true question you have is only at `-0.08`,
then you cannot claim ε-coverage for any `ε ≥ 0.08`, and the bridge can only be run
with `ε < 0.08`. This matters because coverage and calibration pull the usable `ε`
in opposite directions. Calibration wants `ε` large enough that the tails are
clean; coverage wants witnesses beyond `ε`. The bridge fires at any `ε` that
satisfies both, and the interval of admissible `ε` is a compact summary of how much
room the model leaves between its confusion band and its clearest examples. A model
with no admissible `ε` is one whose confusion reaches all the way to its best
cases, which is a model in trouble for reasons the bridge does not even need to
invoke.

# The approximate trilemma

Now the central theorem. It takes the three ingredients above, adds continuity
and connectedness from Chapter 4, and returns not a contradiction but a located
question with a two-sided bound on its truth-distance.

**Theorem 6.6 (Approximate Hallucination Trilemma).** _Let `Q` be a connected
space, let the confidence map `q ↦ conf(q)` be continuous, and let `ε ≥ 0`.
If `M` is ε-covering, ε-calibrated at `c`, and faithful in the threshold-inclusive
sense that `conf(q) ≥ c → δ(q) < 0`, then there is a question `q₀` with_

`conf(q₀) = c` _and_ `δ(q₀) ∈ [-ε, 0)`.

_This is the verified `approx_trilemma`._

_Proof._ Start from the two coverage witnesses. Since `M` is ε-covering there is
`q_t` with `δ(q_t) < -ε` and `q_f` with `δ(q_f) > ε`. Feed each to the matching
clause of ε-calibration. The first clause turns `δ(q_t) < -ε` into
`conf(q_t) > c + ε`, and since `ε ≥ 0` this gives `conf(q_t) > c`. The second
clause turns `δ(q_f) > ε` into `conf(q_f) < c - ε`, hence `conf(q_f) < c`. So the
continuous confidence map is strictly above `c` at `q_t` and strictly below `c`
at `q_f`.

The question space is connected and confidence is continuous, so the image of
confidence is an interval containing both `conf(q_f) < c` and `conf(q_t) > c`.
That interval contains `c`. The intermediate value theorem, the connected-domain
engine of Chapter 4, produces a question `q₀` with `conf(q₀) = c`. In the verified
proof this is the `intermediate_value₂` step applied on the universal set, using
the continuity of the confidence map against the constant map at `c`.

It remains to bound `δ(q₀)` on both sides.

Upper bound, `δ(q₀) < 0`. At `q₀` we have `conf(q₀) = c`, so in particular
`conf(q₀) ≥ c`. Faithfulness applies and gives `δ(q₀) < 0` directly. The model is
correct at the forced question.

Lower bound, `δ(q₀) ≥ -ε`. Suppose not, so `δ(q₀) < -ε`. Then the first clause of
ε-calibration fires and gives `conf(q₀) > c + ε`. But `conf(q₀) = c` and `ε ≥ 0`,
so `c > c + ε` forces `ε < 0`, contradicting `ε ≥ 0`. Hence `δ(q₀) ≥ -ε`. In the
verified proof this is the final `by_contra`/`linarith` pair: assume the negation,
apply the calibration clause, and let linear arithmetic close the gap.

Combining, `δ(q₀) ∈ [-ε, 0)`. ∎

The conclusion deserves slow reading. The theorem does not say the model fails. It
says there is a question `q₀` where three things hold at once. Confidence sits
exactly at threshold, `conf(q₀) = c`. The answer is genuinely correct,
`δ(q₀) < 0`. And the answer is correct by a hair, `δ(q₀) ≥ -ε`, no further from
the boundary than the calibration slack allows. The forced question is one the
model gets right while sitting on the fence about it, and the margin of
rightness is capped by `ε`.

This is the honest shadow of the strict theorem. The strict theorem said such a
`q₀` cannot exist because `δ(q₀)` would have to be both `< 0` and `≥ 0` at once.
The approximate theorem says `q₀` does exist once you grant a slack, and the price
of the slack is visible in the width of the interval `[-ε, 0)` that traps its
truth-distance.

**Remark 6.7 (Why the interval is half-open).** The lower end `-ε` is attained in
principle; the upper end `0` is not. The strict inequality `δ(q₀) < 0` comes from
faithfulness, which forbids confident correctness from touching the boundary. The
weak inequality `δ(q₀) ≥ -ε` comes from calibration, which only bounds how far
below the boundary a low-confidence question can sit. The asymmetry is not
cosmetic. It is what lets `ε → 0` recover a genuine contradiction rather than a
degenerate point, as the next section shows.

**Example 6.8 (A concrete margin).** Take `c = 0.5` and the `ε = 0.1` model of
Example 6.4, deployed on a domain with both solidly-true and solidly-false
questions, so ε-coverage holds. Theorem 6.6 guarantees a question `q₀` where the
model reports confidence exactly `0.5` and whose answer is correct with
truth-distance somewhere in `[-0.1, 0)`. Concretely, the model could be right at
`q₀` by a truth-distance of `-0.07`: correct, but only just, and reporting a coin
flip's confidence about it. If you improve the model to `ε = 0.03`, the same
theorem still fires, and now the forced question's truth-distance lies in
`[-0.03, 0)`. The margin of correctness at the forced question has shrunk from at
most `0.1` to at most `0.03`. You did not remove the fence-sitting question. You
sharpened how precariously it sits on the fence.

**Example 6.8b (Tracing the intermediate value step).** It is instructive to watch
the proof run on a toy model where the arithmetic is visible. Let the question
space be the interval `[0, 1]`, connected, and let confidence be the continuous
map `conf(q) = 1 - q`, so confidence slides from `1` at `q = 0` down to `0` at
`q = 1`. Set `c = 0.5` and `ε = 0.1`. Suppose the truth field along the interval is
`δ(q) = q - 0.55`, so the model is correct for `q < 0.55` and wrong beyond it.
Check the hypotheses. Coverage: at `q = 0` we have `δ = -0.55 < -0.1` and
`conf = 1 > 0.6`; at `q = 1` we have `δ = 0.45 > 0.1` and `conf = 0 < 0.4`. So
`q_t = 0` and `q_f = 1` are ε-coverage witnesses. Faithfulness: `conf(q) ≥ 0.5`
means `1 - q ≥ 0.5`, that is `q ≤ 0.5`, where `δ(q) = q - 0.55 ≤ -0.05 < 0`, so
the model is correct whenever it is confident. Now the intermediate value step:
confidence equals `c = 0.5` at `q₀ = 0.5`. There `δ(q₀) = 0.5 - 0.55 = -0.05`,
which lands in `[-0.1, 0)` exactly as Theorem 6.6 promises. The forced question is
`q₀ = 0.5`, the model is correct there by a truth-distance of `0.05`, and it
reports confidence exactly `0.5`. Push `ε` toward `0` by sharpening the model so
its confidence tracks truth more tightly, and the forced `q₀` migrates toward the
true boundary `q = 0.55`, where `δ = 0` and faithfulness fails. The toy makes the
migration concrete: the fence-sitting question walks toward the boundary as
calibration improves, and only reaches it in the impossible limit.

# Recovering the exact contradiction at ε = 0

The claim that the approximate theorem contains the exact one is not a slogan. It
is a corollary obtained by substituting `ε = 0`.

**Theorem 6.9 (Exact contradiction from the approximate bridge).** _Under the
hypotheses of Theorem 6.6 with `ε = 0`, that is `0`-coverage, `0`-calibration, and
threshold-inclusive faithfulness on a connected space with continuous confidence,
one derives `False`. This is the verified `exact_from_approx`._

_Proof._ Apply Theorem 6.6 with `ε = 0`. It returns `q₀` with `conf(q₀) = c` and
`δ(q₀) ∈ [-0, 0)`, that is `0 ≤ δ(q₀) < 0`. No real number is both at least `0`
and strictly less than `0`, so linear arithmetic closes to `False`. ∎

The half-open interval is exactly what makes this work. At `ε = 0` the trap
`[-ε, 0)` collapses to `[0, 0)`, the empty set, and asserting that `δ(q₀)` lands
in an empty interval is the contradiction. The lower bound `δ(q₀) ≥ -ε` became
`δ(q₀) ≥ 0`, the faithfulness bound `δ(q₀) < 0` stayed, and the two are
incompatible. The strict trilemma is not a separate theorem. It is the endpoint of
the approximate one where the two bounds cross.

It is worth seeing the collapse as a picture, because it explains why the recovery
is not a coincidence of notation. Plot the guaranteed region for `δ(q₀)` as a
function of `ε`. For each `ε > 0` it is the half-open segment from `-ε` up to but
not including `0`, a triangle in the `(ε, δ)` plane with its hypotenuse along
`δ = -ε` and its flat top along `δ = 0` removed. As `ε` decreases the triangle
narrows to the single boundary point `δ = 0`, which the removed top excludes. At
`ε = 0` the region is the point `δ = 0` intersected with the open condition
`δ < 0`, which is empty. The exact contradiction is the vertex of the triangle,
the place where its two bounding constraints meet and the open one wins. This is
the same geometry as the achievable half-space `γ ≤ ε + 2 δ` of the degradation
law collapsing to `γ ≤ 0` at the origin: a full-dimensional region of legal
slacks pinched to nothing as the slacks vanish. Impossibility is what a
positive-measure achievable region looks like at its boundary.

There is a second route to the same place that starts from the biconditional
rather than from `0`-calibration, and the verified library records it because it
shows the strict paper hypotheses feeding the approximate machinery unchanged.

**Theorem 6.10 (Strict calibration through the bridge).** _If `M` satisfies strict
biconditional calibration, ordinary coverage, and threshold-inclusive
faithfulness on a connected space with continuous confidence, then `False`. This
is the verified `exact_from_strictCalibrated_via_approx`._

_Proof._ Convert the strict hypotheses into zero-slack approximate ones. Strict
calibration at `c = 1/2` implies `EpsCalibrated M δ (1/2) 0` by
`strictCalibrated_to_epsCalibrated_zero_half`: the forward direction of each
biconditional is one clause of `0`-calibration. Ordinary coverage implies
`EpsCovering M δ 0` by `trilemmaCovering_to_epsCovering_zero`. Feed both to
Theorem 6.9. ∎

**Remark 6.11.** Theorem 6.10 needs continuity only of the confidence map, not of
the answer or the truth field, because the intermediate value step is applied to
confidence alone. This is a small economy over some presentations of the strict
trilemma, and it is a direct benefit of having factored the argument through the
approximate bridge: the bridge exposes exactly which map has to be continuous.

**Remark 6.11b (The diagonal is still underneath).** It can look as though the
approximate bridge has traded the diagonal of Chapter 1 for the intermediate value
theorem of Chapter 4, and that the self-reference has quietly left the room. It has
not. The forced question `q₀` is the same object as the `liar_query` witness `a₀`
of Chapter 1, wearing analytic clothes. In the exact reflective-verdict picture,
`a₀` is the index where the system's self-verdict must equal its own negation,
an impossibility because negation has no fixed point. In the calibration picture,
`q₀` is the query where the model's confidence must sit at the threshold that
separates its correct verdicts from its incorrect ones, and faithfulness plus
calibration try to force the truth-distance to be both negative and nonnegative
there. The `no_reflective_verdict` collapse of Chapter 1 and the `exact_from_approx`
collapse of this chapter are the same contradiction; the intermediate value theorem
is only the tool that locates the diagonal witness when the domain is connected
rather than self-indexing. The margin `ε` is what you get by refusing to demand the
contradiction exactly and asking instead how close to it the system is driven.

# The tightening principle

The most consequential reading of Theorem 6.6 for a practitioner is not that a bad
question exists. It is how the bad question responds to effort. The instinct
behind calibration work is that a better-calibrated model is a safer model, that
if you push `ε` down far enough the obstruction becomes negligible. Theorem 6.6
says the opposite. Pushing `ε` down does not weaken the obstruction. It
concentrates it.

**Theorem 6.12 (Tightening principle).** _Let `M` be faithful and ε-covering, and
suppose it is both `ε₁`-calibrated and `ε₂`-calibrated at `c` with `0 ≤ ε₂ ≤ ε₁`.
Then the forced question `q₀₂` obtained from the `ε₂` bridge satisfies_
`δ(q₀₂) ∈ [-ε₂, 0)`, _an interval contained in the `ε₁` interval `[-ε₁, 0)`. The
margin of correctness at the forced question is bounded by `ε₂ ≤ ε₁`: improving
calibration cannot loosen the bound, and any strict improvement `ε₂ < ε₁` strictly
tightens it._

The two ingredients are the containment of the guaranteed intervals and the
bound on the margin, and both elaborate here.

```lean
theorem c6_tightening (ε₁ ε₂ : ℝ) (h : ε₂ ≤ ε₁) :
    Set.Ico (-ε₂) 0 ⊆ Set.Ico (-ε₁) 0 := by
  intro x hx
  exact ⟨by linarith [hx.1], hx.2⟩

theorem c6_margin_bound (ε₂ x : ℝ) (hx : x ∈ Set.Ico (-ε₂) 0) :
    |x| ≤ ε₂ := by
  rw [abs_of_neg hx.2]
  linarith [hx.1]
```

The first says improving calibration cannot loosen the guarantee, since the
tighter interval sits inside the looser one. The second says the forced
question's margin of correctness is bounded by the slack it was obtained from.
Together they are the tightening principle: the theorem below supplies the
forced question at each slack, and these two lemmas say what shrinking the slack
does to it.

_Proof._ Theorem 6.6 applies at each slack for which `M` is calibrated and
covering, since faithfulness does not depend on `ε`. At slack `ε₂` it returns
`q₀₂` with `δ(q₀₂) ∈ [-ε₂, 0)`. Because `ε₂ ≤ ε₁`, the containment
`[-ε₂, 0) ⊆ [-ε₁, 0)` holds by monotonicity of the left endpoint.
The upper bound `δ(q₀₂) < 0`
is fixed by faithfulness and does not move with `ε`. The lower bound `-ε₂` is the
one that migrates, and it migrates toward `0`, so `|δ(q₀₂)| ≤ ε₂`. Hence the
worst-case margin `sup |δ|` over the guaranteed interval equals `ε` and is
monotone nondecreasing in `ε`. ∎

The proof is short; the content is not. Read what it forbids. It forbids the
existence of a model that is arbitrarily well calibrated and also comfortably
correct at its threshold-confidence questions. The better calibrated the model,
the closer its forced fence-sitting question is pinned to the truth boundary. In
the limit of perfect calibration the forced question sits exactly on the boundary
and the model is, by faithfulness, unable to be there. That limit is Theorem 6.9.

This is why the section title of the thin draft called it "the single most
important consequence for practice". A calibration improvement that would seem to
be pure progress is instead a movement along a trade-off. You bought a smaller
band of confusion at the cost of a more precisely located point of failure. The
failure did not go away. It sharpened.

**Remark 6.13 (Calibration and faithfulness are not independent dials).** A
tempting mental model treats calibration and faithfulness as separate knobs, each
tunable toward perfection on its own. Theorem 6.12 refutes the independence.
Faithfulness fixes the sign of `δ(q₀)` and calibration fixes its magnitude, and
the two together pin `δ(q₀)` into a shrinking interval that the strict theorem
shows must eventually be empty. You cannot hold faithfulness fixed and drive
calibration to perfection, because the joint conclusion is a nonempty interval
that calibration is trying to empty and faithfulness is refusing to let touch
zero. One of the two hypotheses, or coverage, or continuity, has to give. The
theorem does not say which. It says the four cannot coexist in the limit, and that
in the pre-limit they coexist only inside a budget you are actively spending.

**Example 6.14 (Spending the budget).** Return to the `ε = 0.1` model and imagine
a research program that halves `ε` each quarter: `0.1`, then `0.05`, then `0.025`,
then `0.0125`. Theorem 6.12 tracks the guaranteed forced-question margin down the
same sequence. After a year the model is superbly calibrated, its confusion band a
quarter of what it was, and its forced fence-sitting question is now correct by at
most `0.0125` of truth-distance while reporting exactly threshold confidence. The
program has not eliminated the question. It has manufactured a question on which
the model is right by an eyelash and unsure to the point of a coin flip. Whether
that is progress depends entirely on what happens near that question, which is the
subject of the final section.

The trade-off is easier to feel as a table read in prose. At `ε = 0.1` the forced
question is correct by up to `0.1` and its confidence sits in `[0.4, 0.6]`. At
`ε = 0.05` the margin ceiling drops to `0.05` and the confidence band tightens to
`[0.45, 0.55]`. At `ε = 0.025` the ceiling is `0.025` and the band is
`[0.475, 0.525]`. At `ε = 0.0125` the ceiling is `0.0125` and the band is
`[0.4875, 0.5125]`. Two things move together down this sequence. The confidence
band shrinks, which is the reported gain, the model is confused over a smaller
region. The margin ceiling shrinks in lockstep, which is the hidden cost, the
forced question is squeezed against the boundary. A safety reviewer who reads only
the first column congratulates the team; a reviewer who reads both sees that the
team has been trading breadth of confusion for depth of precariousness, and that
the product of the two, roughly the area of the danger region in the
confidence-by-truth plane, is not obviously improving at all. The bridge does not
tell you the product is constant. It tells you the two factors are coupled and that
you cannot drive either to zero without the other, or one of the standing
hypotheses, giving way.

**Remark 6.14b (Where the naive optimization goes).** Suppose a team ignores the
coupling and optimizes calibration alone, driving `ε` down as far as compute
allows. The bridge predicts the failure they will eventually hit. As `ε` shrinks,
the forced question's truth-distance is pinned into `[-ε, 0)`, so the model is
being asked to be correct within an ever-thinner shell of the boundary while
reporting threshold confidence. At some `ε` the shell is thinner than the
resolution of the training signal, and further calibration cannot be achieved
without either sacrificing faithfulness, letting the confident answer drift to the
wrong side, or sacrificing coverage, refusing to answer near the boundary at all.
Both sacrifices are visible failures with names in the applied literature, overconfident
hallucination and excessive abstention. The bridge says they are not independent
pathologies to be separately patched; they are the two doors the obstruction can
walk out of once the calibration door is shut.

# Localization to the transition band

Theorem 6.6 asserts existence, and a fair worry is that existence is toothless if
the forced question could be anywhere. A theorem that says "somewhere in your
enormous input space there is a bad point" is hard to act on. The approximate
bridge does better than bare existence, because the location of `q₀` is pinned by
where confidence crosses the threshold.

Consider a model that is clearly right in-distribution and clearly wrong far out
of distribution. In-distribution, truth-distance is solidly negative and, by
ε-calibration, confidence is solidly above `c + ε`. Far out of distribution,
truth-distance is solidly positive and confidence is solidly below `c - ε`. The
forced question `q₀` has `conf(q₀) = c` exactly. It cannot be in the
in-distribution region, where confidence exceeds `c + ε > c`. It cannot be far out
of distribution, where confidence is below `c - ε < c`. It has to sit in the
transition band between the two, the region where confidence descends through the
threshold as the input drifts from familiar to unfamiliar.

**Proposition 6.15 (Localization).** _Under the hypotheses of Theorem 6.6, every
forced question `q₀` with `conf(q₀) = c` lies outside both the high-confidence
region `{q : conf(q) > c + ε}` and the low-confidence region
`{q : conf(q) < c - ε}`. It lies in the transition band
`{q : c - ε ≤ conf(q) ≤ c + ε}`._

```lean
theorem c6_localization (c ε : ℝ) (hε : 0 ≤ ε) :
    c ∈ Set.Icc (c - ε) (c + ε) ∧ ¬ (c > c + ε) ∧ ¬ (c < c - ε) :=
  ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
```

_Proof._ Three applications of `linarith` from `0 ≤ ε`. ∎

The companion `no_boundary_in_upper_band` proves a related but distinct
statement, that no question can be both at or above threshold and exactly on the
truth boundary, so it is not cited here as a counterpart to this one.

_Proof._ Immediate from `conf(q₀) = c` and `ε ≥ 0`: the value `c` satisfies both
`c ≤ c + ε` and `c ≥ c - ε`, so `q₀` is in the closed confidence band and in
neither open region flanking it. ∎

The proposition is arithmetically trivial and practically not. It says the
theorem does not predict trouble uniformly across the input space. It predicts
trouble exactly at the seam where in-distribution behavior gives way to
out-of-distribution behavior. That is the region practitioners already watch,
because it is where a model's competence is changing fastest. The approximate
bridge gives a reason the seam is special that is independent of any particular
dataset: it is the only place a forced threshold-confidence question can live.

The localization also explains why the transition band cannot be made empty by
better engineering. Suppose you tried to eliminate the band by making confidence
jump discontinuously from above `c + ε` to below `c - ε`, with no intermediate
values. Then confidence would not be continuous, and Theorem 6.6's hypotheses
would fail; but a discontinuous confidence map is a different pathology, and
Chapter 4 already argued that real models, built from continuous components, do
not have it on a connected input space. On a connected domain a continuous
confidence map that is high somewhere and low somewhere else must pass through
every value between, and `c` is between. The band is where the passage happens.

The localization has a practical corollary for evaluation design. If the forced
question can only live in the transition band, then an evaluation set that samples
uniformly from the input space will hit the forced question only in proportion to
how much of the space the band occupies, which for a sharp model is very little.
Uniform evaluation therefore systematically under-tests the exact region the
theorem points to. The remedy is to sample by confidence: deliberately gather
questions whose reported confidence is near `c` and stress-test those. This is not
a new idea in practice, active learning and uncertainty sampling already target
the same region, but the bridge gives it a theorem-shaped justification. The band
near `conf = c` is not merely where the model is unsure; it is the only place a
forced correct-but-barely question can be, so it is where the irreducible residue
of the impossibility concentrates. An evaluation that ignores it is blind to
precisely the failures the mathematics guarantees.

One more consequence is worth stating because it defuses a common objection. A
reader might grant the theorem and still say the transition band is so small that
it does not matter. The bridge's own tightening principle answers this. Making the
band small, small `ε`, does not make the forced question harmless; it makes the
forced question more precisely correct-by-a-hair and no less forced. Smallness of
the band is a statement about the model's sharpness, not about the severity of what
lives in the band. To learn whether the small band is dangerous you need the
geometry of the final section, which measures how much traffic and how much
adversarial pressure the band actually receives.

# The discrete band constraint

The intermediate value theorem needs a connected domain. Real input spaces are
often not connected in any useful sense; token sequences are discrete, and the
question space may be a finite corpus. Chapter 4 argued that connectedness is
frequently available after the right embedding, but it is worth having a bridge
that assumes no topology at all. The discrete version drops the existence half of
the argument and keeps the arithmetic half.

**Theorem 6.16 (Discrete band constraint).** _On any sets `Q` and `A`, with no
topology and no finiteness assumption, suppose `M` is ε-calibrated at `c` and
threshold-inclusive faithful. Let `q` be any question whose confidence lands in
the upper confidence band,_ `c ≤ conf(q) ≤ c + ε`. _Then_
`δ(q) ∈ [-ε, 0)`. _This is the verified `discrete_approx_bridge`._

_Proof._ Two bounds, each from one hypothesis.

Upper bound, `δ(q) < 0`. Since `conf(q) ≥ c`, faithfulness gives `δ(q) < 0`.

Lower bound, `δ(q) ≥ -ε`. Suppose `δ(q) < -ε`. Then the first clause of
ε-calibration gives `conf(q) > c + ε`, contradicting the assumption
`conf(q) ≤ c + ε`. Hence `δ(q) ≥ -ε`. ∎

The difference from Theorem 6.6 is precisely the intermediate value step. There,
connectedness and continuity _produced_ a question with `conf = c`. Here, no such
question is guaranteed to exist; instead, _if_ one exists whose confidence sits in
the upper band `[c, c + ε]`, the same arithmetic pins its truth-distance to
`[-ε, 0)`. On a connected continuous space the two theorems agree, because the
intermediate value theorem supplies the band question for free. On a discrete
space the constraint is conditional on there being a question in the band, which
is a statement you check against the model rather than derive.

This conditional character is a feature, not a weakness, once you see what it buys.
The continuous bridge proves an existence claim you then have to trust the topology
for; the discrete bridge proves an implication you can check against a concrete
corpus. If your evaluation set contains any question whose reported confidence lands
in `[c, c + ε]`, and most nontrivial evaluation sets do, then Theorem 6.16 applies
to that question directly, with no appeal to connectedness or continuity, and tells
you its truth-distance is trapped in `[-ε, 0)`. You can go find the question, look
at it, and confirm the model is correct-but-barely exactly where the theorem says.
The discrete bridge is the version you can audit by hand. It also degrades
gracefully to the fully finite setting: on a finite question space every hypothesis
is a finite conjunction of inequalities, decidable in principle, which is why the
core-Lean fragment below can carry the whole logical content over the integers with
no analysis at all.

The arithmetic core of the discrete bridge is finite and needs no reals to
convey. Here it is over the integers, scaled so that truth-distances and
confidences are whole numbers, elaborated when the book is built:

```lean
theorem c6_band (dq confq c eps : Int)
    (hcal : dq < -eps → confq > c + eps)   -- ε-calibration, lower clause
    (hfaith : confq ≥ c → dq < 0)          -- c-faithfulness
    (hge : confq ≥ c)                      -- upper half of the band
    (hle : confq ≤ c + eps) :              -- not above the band
    -eps ≤ dq ∧ dq < 0 := by
  refine ⟨?_, hfaith hge⟩
  rcases Int.lt_or_le dq (-eps) with h | h
  · have := hcal h; omega
  · exact h
```

The proof is two cases on whether `dq` is below `-eps`. If it is, the calibration
implication and `omega` derive a contradiction with the band assumption; if it is
not, the goal is the case hypothesis. The real-valued `discrete_approx_bridge`
does the same work with `linarith` over `ℝ`; the logical skeleton is identical.

An immediate consequence is that no question in the upper band sits exactly on the
truth boundary.

**Corollary 6.17 (No boundary point in the upper band).** _Under ε-calibration and
threshold-inclusive faithfulness, no question `q` with `c ≤ conf(q) ≤ c + ε` has
`δ(q) = 0`. This is the verified `no_boundary_in_upper_band`._

_Proof._ Theorem 6.16 gives `δ(q) < 0`, which excludes `δ(q) = 0`. ∎

The zero-slack collapse is again a one-liner. At `ε = 0` the upper band is the
single value `conf(q) = c`, and Theorem 6.16 would force `δ(q) ∈ [0, 0)`, empty.
So on a discrete space, `0`-calibration and faithfulness forbid any question from
reporting exactly threshold confidence while being correct. The finite core:

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

Faithfulness makes the answer correct, `dq < 0`; the zero-slack calibration clause
then forces confidence strictly above `c`; but the band caps it at `c`. Three
lines and `omega` finishes. This is the same shape as `liar_query` from Chapter 1,
where the diagonal question satisfied `f a₀ a₀ = !(f a₀ a₀)`: an object forced to
be on both sides of a line at once. The discrete calibration constraint is that
paradox rendered in inequalities instead of booleans.

# Two-slack separation: truth units and confidence units

Definition 6.1 used a single `ε` for both the truth side and the confidence side.
That is convenient and slightly dishonest, because truth-distance and confidence
are measured in different units and can be rescaled independently. A model whose
confidence is reported on a `0` to `100` scale rather than `0` to `1` has its
confidence slack multiplied by a hundred without anything about its truthfulness
changing. A clean formulation separates the two.

**Definition 6.18 (Two-slack separation).** _Fix a truth slack `ε` and a
confidence margin `γ`. A model is_ two-slack separating _at `c` if_

- `δ(q) < -ε → conf(q) > c + γ`, _and_
- `δ(q) > ε → conf(q) < c - γ`.

_The verified predicate is `TwoSlackSeparating M δ c ε γ`, and `EpsCalibrated` is
the special case `γ = ε`, recorded as `epsCalibrated_iff_twoSlack`._

The truth slack `ε` lives in the units of the truth field; the confidence margin
`γ` lives in the units of confidence. The separation makes the invariances
visible. Rescale confidence and only `γ` changes. Rescale the truth field and only
`ε` changes. The conclusions of the theorems should, and do, land their bounds in
the correct units.

**Theorem 6.19 (Two-slack coupling).** _On a connected space with continuous
confidence, if `M` is ε-covering, two-slack separating with margin `γ ≥ 0`, and
threshold-inclusive faithful, then there is `q₀` with `conf(q₀) = c` and
`δ(q₀) ∈ [-ε, 0)`. This is the verified `two_slack_approx_coupling`._

_Proof._ Identical in shape to Theorem 6.6, with `γ` doing the work `ε` did on the
confidence side. Coverage gives `q_t` with `δ(q_t) < -ε` and `q_f` with
`δ(q_f) > ε`. Two-slack separation gives `conf(q_t) > c + γ ≥ c` and
`conf(q_f) < c - γ ≤ c`, using `γ ≥ 0`. The intermediate value theorem produces
`q₀` with `conf(q₀) = c`. Faithfulness gives `δ(q₀) < 0`. And if `δ(q₀) < -ε`, the
first separation clause gives `conf(q₀) > c + γ ≥ c`, contradicting
`conf(q₀) = c`; so `δ(q₀) ≥ -ε`. The conclusion's interval `[-ε, 0)` is in truth
units alone. The confidence margin `γ` appears only in the intermediate value
step and drops out of the final bound. ∎

The final sentence is the reason the separation is worth stating. Whatever
confidence margin the model happens to exhibit, however you scale the confidence
axis, the located truth-distance interval is `[-ε, 0)`, purely in truth units. The
confidence margin powers the crossing but does not survive into the conclusion.

**Example 6.19b (Two slacks with numbers).** Report confidence on a `0` to `100`
scale with threshold `c = 50`, and measure truth-distance on a `0` to `1` semantic
scale. Suppose clearly-true questions, truth-distance below `-0.1`, always score
above `70`, and clearly-false ones, above `0.1`, always score below `30`. Then the
model is two-slack separating with truth slack `ε = 0.1` and confidence margin
`γ = 20`. The two numbers live in different worlds: `0.1` is a semantic distance,
`20` is a fraction of the confidence scale. Theorem 6.19 fires and returns a forced
question whose confidence is exactly `50` and whose truth-distance is in
`[-0.1, 0)`, in semantic units, with the `20` nowhere in the answer. Rescale
confidence to `0` to `1` and the margin becomes `γ = 0.2` while the conclusion
interval `[-0.1, 0)` is untouched. If you had used the single-parameter Definition
6.1 you would have been forced to reconcile a truth slack of `0.1` with a confidence
slack of `20` as though they were the same number, which they are not. The two-slack
form is what keeps the units honest, and Theorem 6.20 then tells you that of the
two, it is the truth slack `0.1` that provably cannot be pushed to zero.

The separation also isolates which slack must be positive for a real model to
exist at all.

**Theorem 6.20 (The truth slack must be positive).** _On a connected space with
continuous confidence, if `M` is two-slack separating with any margin `γ ≥ 0`,
ε-covering with `ε ≥ 0`, and threshold-inclusive faithful, then `ε > 0`. This is
the verified `truth_slack_must_be_positive`._

_Proof._ Suppose `ε = 0`. Then Theorem 6.19 applies with `ε = 0` and returns `q₀`
with `δ(q₀) ∈ [-0, 0) = [0, 0)`, which is empty, a contradiction. So `ε > 0`. ∎

This is the sharpest way to say what the strict theorem forbids. It is not the
confidence margin that has to be sacrificed; a model can have as clean a
confidence separation as you like. It is the _truth_ slack that cannot be zero.
Any faithful, covering model on a connected space with a continuous confidence map
must leave a genuinely positive band of truth-distance uncertified around its
boundary. The band can be narrow. It cannot be a point. Zero truth slack is the
exact contradiction of the strict trilemma, now attributed to the correct
parameter.

The discrete two-slack version mirrors Theorem 6.16 with the band measured in
confidence units.

**Theorem 6.21 (Two-slack band bridge).** _On any sets, under two-slack separation
and threshold-inclusive faithfulness, any question with `c ≤ conf(q) ≤ c + γ` has
`δ(q) ∈ [-ε, 0)`. The confidence band is in confidence units, the conclusion band
in truth units. This is the verified `two_slack_band_bridge`, and its boundary-free
corollary is `no_boundary_in_upper_band_two_slack`._

_Proof._ As in Theorem 6.16, replacing `c + ε` by `c + γ` in the calibration
step. Faithfulness gives `δ(q) < 0` from `conf(q) ≥ c`; if `δ(q) < -ε` then
separation gives `conf(q) > c + γ`, contradicting `conf(q) ≤ c + γ`. ∎

**Remark 6.22 (Axioms).** The verified two-slack results carry an explicit axiom
audit: `two_slack_approx_coupling`, `truth_slack_must_be_positive`,
`two_slack_band_bridge`, and `no_boundary_in_upper_band_two_slack` are each printed
with `#print axioms`. They rest on the classical and quotient axioms Mathlib's
real analysis uses, and on nothing model-specific. The discrete bridges, being
pure order arithmetic, are the lightest; the continuous ones inherit the
intermediate value theorem's dependencies. The core-Lean `c6_` fragments above use
no axioms beyond the kernel, since they are decidable integer statements.

# The quantitative degradation law

The calibration bridges relax the confidence-versus-truth idealization. A
different idealization is universality itself: the assumption from Chapter 1 that
the system can name every behavior exactly. Real systems approximate behaviors,
they do not reproduce them. The Foundation library's `F_09_QuantitativeDegradation`
relaxes universality to an ε and runs the whole diagonal through a metric, ending
in a single clean inequality. It is the same phenomenon as the calibration bridge,
seen through the Mirror Trilemma corner rather than the Hallucination corner.

The setting is a system `M : A → A → Y` valued in a pseudometric space `Y`, with a
distance `dist`. Three parameters relax three idealizations. The choice of a
pseudometric rather than a metric is deliberate: a pseudometric allows distinct
behaviors to sit at distance zero, which models a system that cannot distinguish
certain outputs, and the theorems below never need the separation axiom that would
promote it to a metric. Only at `ε = 0`, when we want approximate universality to
mean exact surjectivity, does the metric axiom `dist x y = 0 → x = y` get used, and
there it is invoked explicitly.

The three parameters, in the notation of `F_09_QuantitativeDegradation`, are `ε`
for universality slack, `δ` for transparency slack, and `γ` for the controller's
demanded margin. Note that this `δ` is a distance budget in `Y`, not the
truth-distance field of the calibration sections; the two developments reuse the
letter for different objects, and the context disambiguates. In this section `δ`
always means the transparency slack `dist (M a a) (introspect a) ≤ δ`.

**Definition 6.23 (ε-approximate universality).** _`M` is ε-approximately
universal if for every target behavior `g : A → Y` there is a prompt `a` with
`dist (M a b) (g b) ≤ ε` for all queries `b`. The verified predicate is
`ApproxUniversal M ε`._

At `ε = 0` in a genuine metric space this is ordinary curried surjectivity, since
`dist x y = 0` forces `x = y`. For `ε > 0` it is the honest claim: the system can
imitate any behavior to within `ε`, not reproduce it.

The Lawvere diagonal survives the relaxation. Instead of an exact self-fixed-point
it yields an approximate one.

**Theorem 6.24 (Approximate Lawvere).** _If `M` is ε-approximately universal then
every endomap `t : Y → Y` has an ε-approximate self-fixed-point: some `a` with
`dist (M a a) (t (M a a)) ≤ ε`. This is the verified `approx_lawvere`._

_Proof._ Apply ε-universality to the diagonal target `g b = t (M b b)`. It returns
a prompt `a` with `dist (M a b) (t (M b b)) ≤ ε` for all `b`. Instantiate at
`b = a` to get `dist (M a a) (t (M a a)) ≤ ε`. ∎

This is exactly `lawvere` from Chapter 1 with the equation `M a a = t (M a a)`
loosened to a distance bound. The diagonal move is unchanged; only the conclusion
carries a budget. Set `ε = 0` and, in a metric space, the distance bound becomes
the exact fixed point of Theorem 1.4.

Now add two more slacks. A system rarely exposes its raw diagonal `M a a`; it
reports a declared self-image `introspect a`. Transparency is the claim that the
declaration matches the diagonal, and it too is approximate.

**Theorem 6.25 (Quantitative degradation).** _Let `M` be ε-approximately
universal, let `introspect : A → Y` satisfy `dist (M a a) (introspect a) ≤ δ` for
all `a`, and let `t : Y → Y` be `1`-Lipschitz. Then there is a prompt `a` with_

`dist (introspect a) (t (introspect a)) ≤ ε + 2 δ`.

_This is the verified `quantitative_trilemma`._

_Proof._ A triangle argument on top of Theorem 6.24. Take the approximate
fixed-point `a` from Theorem 6.24, so `dist (M a a) (t (M a a)) ≤ ε`. Transparency
gives `dist (M a a) (introspect a) ≤ δ`, and `1`-Lipschitz `t` pulls this forward
to `dist (t (M a a)) (t (introspect a)) ≤ δ`. Now walk the path

`introspect a → M a a → t (M a a) → t (introspect a)`.

The three legs are bounded by `δ`, `ε`, and `δ` respectively. Two applications of
the triangle inequality, plus `dist_comm` to orient the first leg, sum them:
`dist (introspect a) (t (introspect a)) ≤ δ + ε + δ = ε + 2 δ`. ∎

The finite skeleton of the triangle bound, over the integers, is standalone:

```lean
theorem c6_triangle_bound
    (goal d1 d2 d3 eps del : Int)
    (htri : goal ≤ d1 + d2 + d3)
    (hd1 : d1 ≤ del) (hd2 : d2 ≤ eps) (hd3 : d3 ≤ del) :
    goal ≤ eps + 2 * del := by omega
```

Here `d1`, `d2`, `d3` are the three leg distances and `htri` is the summed
triangle inequality; `omega` does the bookkeeping `del + eps + del = eps + 2*del`.
The real proof carries the same three legs through `dist_triangle` and `linarith`.

The inequality `dist (introspect a) (t (introspect a)) ≤ ε + 2 δ` is the whole
law. Rephrase it as a constraint on a controller. A controller demands that the
system's self-image be robustly moved by `t`, that `introspect a` and
`t (introspect a)` differ by more than some margin `γ` for every `a`. Theorem 6.25
says such a demand cannot be met beyond the budget `ε + 2 δ`.

**Theorem 6.26 (Achievable region).** _If additionally
`dist (introspect a) (t (introspect a)) > γ` for all `a`, then `γ < ε + 2 δ`. The
achievable triples `(ε, δ, γ)` lie in the half-space `{γ ≤ ε + 2 δ}`. This is the
verified `achievable_region_bound`, with the contradiction form
`quantitative_impossibility` when `γ ≥ ε + 2 δ`._

_Proof._ Theorem 6.25 gives a specific `a` with
`dist (introspect a) (t (introspect a)) ≤ ε + 2 δ`. The controller's demand at
that same `a` gives `γ < dist (introspect a) (t (introspect a))`. Chain the two:
`γ < ε + 2 δ`. If instead `γ ≥ ε + 2 δ` were assumed, the chain yields
`ε + 2 δ ≤ γ < ε + 2 δ`, a contradiction. ∎

The half-space `γ ≤ ε + 2 δ` is the exact analogue of the interval `[-ε, 0)` from
the calibration bridge. Both are the region a real system is allowed to occupy.
Both collapse at the origin of their slacks.

**Theorem 6.27 (Strict limit).** _At `ε = 0` and `δ = 0`, any nontrivial
controller `γ > 0` gives `False`; equivalently `γ ≤ 0`. This is the verified
`strict_limit_recovers_trilemma`._

_Proof._ Substitute `ε = δ = 0` into Theorem 6.26 to get `γ < 0`, contradicting
`γ > 0`. ∎

The collapse over the integers, showing the controller margin forced negative:

```lean
theorem c6_strict_collapse
    (goal margin : Int)
    (hbound : goal ≤ 0 + 2 * 0)
    (hmargin : goal > margin) :
    margin < 0 := by omega
```

Perfect universality and perfect transparency force the achievable controller
margin below zero, so any positive demand is impossible. That is the strict Mirror
Trilemma, recovered as the corner of a quantitative law, exactly as the strict
Hallucination Trilemma was recovered as the corner of the calibration bridge.

**Remark 6.27b (What a K-Lipschitz controller costs).** The `1`-Lipschitz
hypothesis on `t` is the boundary case, and it is worth knowing which way the bound
moves when it is relaxed. If `t` is `K`-Lipschitz instead, the middle leg of the
triangle, `dist (t (M a a)) (t (introspect a))`, is bounded by `K δ` rather than
`δ`, because the Lipschitz constant multiplies the pulled-back transparency gap.
The budget becomes `ε + (1 + K) δ`, which at `K = 1` recovers `ε + 2 δ`. A
controller whose transform amplifies differences, `K > 1`, has a larger achievable
region and so is easier to satisfy; a contracting transform, `K < 1`, has a smaller
one and is harder to satisfy, which matches intuition, since a contraction pulls
self-images toward their `t`-images and leaves less room for a controller to demand
separation. The `1`-Lipschitz case is the natural reference because it is exactly
the class of transforms that neither create nor destroy distance, the metric
analogue of the fixed-point-free flips that drove the exact theorems of Chapter 1.

**Remark 6.28 (Two shapes of the same fact).** The calibration bridge and the
degradation law relax different idealizations and produce differently-shaped
budgets, an interval on one side and a half-space on the other, but the mechanism
is one. Both take the exact diagonal, insert a slack at each idealized equality,
and carry the slacks through the argument by linear arithmetic to a conclusion
that is nonempty for positive slack and contradictory at zero. The calibration
bridge inserts its slack at the calibration biconditional and the coverage
witnesses; the degradation law inserts its slack at universality and transparency.
The `2 δ` in `ε + 2 δ` is the transparency slack counted twice, once going into
the diagonal and once coming out under the Lipschitz map, which is the metric
analogue of the two-sided band `[-ε, 0)` being bounded from two independent
hypotheses.

# From existence to measure

Theorem 6.6 and its relatives assert that a forced question exists and bound how
correct it is. That is an existence-plus-margin statement, and by itself it is not
yet a number a deployment can act on. Knowing that some fence-sitting question
exists does not tell you whether you will ever be asked it, or what happens to
nearby questions, or how hard an adversary has to work to find it. Those are the
questions Chapter 5's geometry answers, and the composition of the two chapters is
where the notes come closest to an actionable risk estimate.

The bridge and the geometry supply complementary halves of a risk figure. The
bridge supplies the _margin_: at the forced question the model is correct by at
most `ε` of truth-distance, and by localization the question lives in the
transition band where confidence crosses `c`. The geometry supplies the
_frequency_ and the _cost_: how large the region around the forced question is,
how often a walk through input space enters it, and what an adversary pays to
steer into it.

Concretely, three geometric quantities from Chapter 5 combine with the bridge.

The _basin volume_ near the boundary, from `MoF_Cost_02_BasinVolume`, measures how
much of the input space lies within a given truth-distance of the boundary. The
bridge says the dangerous questions are those within `ε` of the boundary on the
correct side; the basin volume converts that `ε` into a fraction of inputs. A
small calibration slack `ε` and a thin basin together mean few inputs are at risk;
a small `ε` but a fat basin means the model is precariously balanced across a
large region.

The _hitting time_, from `MoF_Cost_03_HittingTime`, measures how long a random or
gradient-driven walk takes to reach the boundary band. The bridge guarantees the
band is nonempty and localized; the hitting time says how quickly ordinary drift
or deliberate search arrives there. A long hitting time means the forced question
is reachable only rarely; a short one means it is around the corner.

The _concentration_ of measure near the boundary, from
`MoF_Cost_04_Concentration`, measures how much probability mass an input
distribution places in the band. The bridge and the localization put the danger in
the transition band; concentration says how much of your actual traffic lands
there.

The reason these three cannot be read off the bridge alone is that the bridge is
blind to geometry by construction. It is a diagonal argument, and Remark 1.14 of
Chapter 1 already warned that the diagonal is silent on everything quantitative:
not how many forced questions there are, not how hard one is to find, not what it
costs to reach. The bridge adds a margin to that silence, the `ε` that bounds the
forced question's truth-distance, but it says nothing about measure or reachability.
Those are analytic and measure-theoretic facts about the confidence field's
sublevel sets, and they are the content of Chapter 5. The division of labor is
clean. The bridge certifies that a forced question exists, is correct by at most
`ε`, and lives in the transition band. The geometry certifies how big the band is,
how often you enter it, and what it costs an adversary to put you there. Neither
half is a substitute for the other, and a risk estimate needs both.

Put the three together with the margin and you get a schematic risk estimate.
Loosely, the probability that a randomly drawn deployment query is a forced
fence-sitting question scales with the measure concentrated in the transition band,
and the severity of each such event is bounded by the margin `ε`. The unified cost
statement `MoF_Cost_10_UnifiedTheory` is where Chapter 5 assembles the volume,
hitting-time, and concentration bounds into a single expression; feeding the
bridge's `ε` and its localization into that expression yields the composite figure.

Write the schematic estimate out so its parts are visible. Let `P_band` be the
probability mass the deployment distribution places in the transition band
`conf ∈ [c - ε, c + ε]`, a concentration quantity from Chapter 5. Let `S` be the
severity of a forced-question event, which the bridge bounds by the margin, so
`S ≤ ε` on the correct side. Then the expected per-query risk contributed by forced
questions is at most `P_band · S ≤ P_band · ε`. The two factors respond to
different levers. Calibration work drives `ε` down, shrinking `S` by the tightening
principle, but it also reshapes the confidence field and so moves `P_band`, and the
sign of that movement is a geometric fact the bridge does not determine. This is the
honest form of the trade-off: you can drive one factor down, and whether the product
follows depends on what the other factor does, which is measurable only through the
geometry. A deployment that reports `ε` alone, or `P_band` alone, is reporting one
factor of a product and calling it a risk. The composite is the product, and it is
the smallest object that deserves the name.

**Example 6.29 (A risk estimate with numbers).** Take the `ε = 0.05` model, so any
forced question is correct by at most `0.05` of truth-distance and sits in the
transition band `conf ∈ [0.45, 0.55]`. Suppose Chapter 5's geometry, applied to
the model's confidence field, reports that the transition band has basin volume
`2%` of the input space and that the deployment's query distribution concentrates
`0.5%` of its mass there. Then roughly one query in two hundred lands in the band,
and when it does the model is either correct by a margin no larger than `0.05` or,
outside the guaranteed interval, wrong. The bridge does not tell you the split
between those outcomes; it tells you the correct-side ones are correct by an
eyelash and the band is where all the action is. The hitting-time bound then tells
you whether an adversary can drive a chosen input into the band cheaply. If the
band is `0.05` wide in truth-distance and the model is `L`-Lipschitz, reaching it
from a confidently-correct input costs on the order of the boundary distance
divided by `L`, which Chapter 5 makes precise. The composite is a number: a
per-query probability of landing in the forced band, a bounded severity per event,
and an adversarial cost to force one deliberately.

**Remark 6.30 (What the composite can and cannot claim).** The composite risk
estimate is an upper bound on a very specific quantity, the incidence and severity
of forced threshold-confidence questions. It is not a claim about all model
errors. Errors far from the transition band are outside its scope; those are
ordinary mistakes the bridge says nothing about. What the composite captures is
the irreducible residue: the errors that exist not because the model is
undertrained but because faithfulness, calibration, coverage, and continuity
cannot all be perfect at once. Tightening `ε` shrinks the severity per event, by
Theorem 6.12, while possibly moving the geometry; a full accounting tracks both.
The estimate is honest precisely because it separates the part forced by the
diagonal, which no training removes, from the part that is contingent geometry,
which engineering can move.

**Example 6.29b (The adversarial reading).** The frequency factor has a benign
reading and an adversarial one, and the bridge supports both. Benignly, a random
deployment query lands in the transition band with probability given by the
concentration figure, and the composite estimates ordinary incidence. Adversarially,
an attacker does not wait for random traffic; they steer. Chapter 5's hitting-time
and gradient-attack bounds say how cheaply an input can be nudged from a
confidently-handled region into the band. Here the bridge's localization is what
makes the attack well-posed: the attacker has a target, the set `conf ≈ c`, and the
bridge guarantees that target is nonempty and contains a correct-but-barely
question the model will fumble. The margin `ε` bounds how close to the truth
boundary the attacker's found question sits, which in turn bounds how small a
perturbation is needed to tip it across into a confident error. A tighter `ε`,
paradoxically, gives the attacker a question already closer to the edge. The
tightening principle and the attack geometry point the same way: sharper
calibration produces a forced question that is cheaper to weaponize, unless the
geometry around it is correspondingly hardened.

**Remark 6.31 (The whole bridge in one sentence).** Strip away the parameters and
the chapter says this: the exact impossibility is the zero-slack corner of a
quantitative law, the law's conclusion is a nonempty margin rather than a
contradiction, the margin tightens as the model improves rather than vanishing,
the margin is localized to the transition band rather than spread everywhere, and
Chapter 5's geometry turns the located margin into a rate. That is the bridge from
the idealized theorem to the model on the bench.

# The reading is where the work is

Chapter 1 made a claim that carries directly into this chapter: the engine is one
line, and all the effort lives in the reading, in arguing that a real situation
really does instantiate the hypotheses. The approximate bridge inherits that
structure. The theorems of this chapter are short. Whether they apply to a given
system is a modeling question, and the same three readings that Chapter 3 gave the
exact trilemma give the approximate one, now with a margin attached.

**Reading 6.32 (Hallucination, approximate).** The model is a question-answerer, `δ`
is distance from factual truth, and confidence is the model's own reported
certainty. ε-calibration is the reliability-diagram fact that clearly-true answers
draw high confidence and clearly-false ones draw low confidence, with a confused
band in the middle. The forced question is a factual query the model answers at
threshold confidence and gets right by no more than `ε`. As the model's calibration
improves, this query is pinned closer to the factual boundary, the region of claims
that are almost-but-not-quite supported. That region is where confident
hallucination is most dangerous, and the bridge says a sharply calibrated model
cannot vacate it.

**Reading 6.33 (Prompt injection defense, approximate).** Now the "question" is an
input to a defended system, `δ` measures how far the input is from being an attack,
and "confidence" is the defense's score for treating the input as safe. Faithfulness
is the defense's guarantee that it does not wave through clear attacks. Coverage is
the existence of clearly-safe and clearly-malicious inputs. ε-calibration is the
defense's reliability: clearly-safe inputs score clearly safe, clearly-malicious
ones score clearly unsafe. The bridge forces an input at the defense's threshold
that is safe by at most `ε`, sitting in the band where benign and adversarial
inputs are hardest to tell apart. A better-calibrated defense produces a forced
input closer to the true attack boundary, which is exactly the input an adversary
wants to find. The exact version of this is the defense trilemma of Chapter 3; the
approximate version is why no threshold-tuning of a scalar defense score removes the
ambiguous band, it only narrows and sharpens it.

**Reading 6.34 (Truth probes, approximate).** Let the "question" index internal
states of a model and let `δ` measure whether a probed proposition is true, with
"confidence" the probe's reported readout. ε-calibration is the probe's accuracy on
clear cases. The bridge forces a state at the probe's threshold whose proposition
is true by at most `ε`, a claim the probe cannot cleanly place on either side. This
is the truth-boundary coupling of Chapter 3 in quantitative form: a probe that is
accurate on clear cases must have a threshold state it cannot resolve, and
sharpening the probe pins that state to the semantic boundary rather than removing
it. In all three readings the mathematics is identical, `approx_trilemma` applied
to different `M`, `δ`, and `c`. What differs is only what the forced question means,
and in each case it means the same thing the exact `liar_query` of Chapter 1 meant,
an object the system is forced to place on both sides of its own line, now softened
to a margin of width `ε`.

# Historical and bibliographic notes

The move from an exact diagonal to an approximate one is old in spirit. Metric
fixed-point theory, from Banach onward, is entirely about approximate and exact
fixed points coexisting under contraction hypotheses, and the `1`-Lipschitz
condition on `t` in Theorem 6.25 is the boundary case of that theory. The specific
combination used here, an approximate Lawvere diagonal feeding a triangle
inequality, follows the CCH development referenced in the Foundation file's header;
the calibration bridge's use of the intermediate value theorem to force a
threshold crossing is the analytic engine introduced in Chapter 4 and refined by
Chapter 5's geometry.

The idea that calibration and correctness are in tension, rather than jointly
optimizable, appears informally throughout the empirical calibration literature,
usually as the observation that sharpening a model's confidence near its decision
boundary trades against its accuracy there. Theorem 6.12 is a proof of that
tension from the trilemma hypotheses, and it locates the tension at the exact
point the intermediate value theorem forces. The two-slack separation, keeping
truth units and confidence units distinct, is a piece of unit hygiene that matters
once one tries to read `ε` off a real calibration table, since the confidence axis
carries an arbitrary scale.

The practice of recovering a strict theorem as the zero-slack corner of a
quantitative one is a recurring pattern in this book and elsewhere, and it is worth
naming as a method rather than a trick. You take a proof that ends in a
contradiction from an equality, you find the equality and replace it with an
inequality carrying a parameter, and you propagate the parameter through the same
proof steps. If the proof used only order and linear arithmetic, as the diagonal
and the intermediate value arguments do, the propagation is mechanical and the
conclusion is the original contradiction plus a slack term. The strict theorem is
then the parameter's zero. This is why both `HoF_12_Approximate` and
`F_09_QuantitativeDegradation` are short files layered on top of the strict
developments rather than independent efforts: the hard mathematical work was done in
the exact case, and the approximate case is that work read with a budget. The
payoff is disproportionate, because the budgeted version is the one that applies to
anything real.

The machine-checked statements are `HoF_12_Approximate` for the calibration
bridges (`approx_trilemma`, `exact_from_approx`, `discrete_approx_bridge`, the
two-slack family, and the strict-to-approximate reductions) and
`F_09_QuantitativeDegradation` for the metric degradation law (`ApproxUniversal`,
`approx_lawvere`, `quantitative_trilemma`, `achievable_region_bound`,
`quantitative_impossibility`, `strict_limit_recovers_trilemma`). The geometry the
final section composes with is the `ManifoldProofs` cost series surveyed in
Chapter 5. The exact theorems these bridges reduce to are the reflective-verdict
collapse of Chapter 1 and the trilemma readings of Chapter 3; the connected-domain
engine they borrow is Chapter 4's; and the measure that turns their existence claim
into a rate is Chapter 5's. This chapter is the joint of those parts, the place the
qualitative and the quantitative halves of the book are bolted together.

# Exercises

**Exercise 6.1.** Write out the contrapositive of each clause of Definition 6.1
and check by hand that Proposition 6.2 is exactly the pair you obtain. Identify the
single order-theoretic fact about `ℝ` that each contraposition uses.

**Exercise 6.2.** Verify the `ε = 0` reading in Remark 6.3: show that the two
clauses of `0`-calibration are the two forward implications of the strict
biconditional, and that the backward implications are the ones ε-calibration
discards. Explain in a sentence why the intermediate value argument never needs
the backward implications.

**Exercise 6.3.** In Theorem 6.6, exactly one endpoint of the interval `[-ε, 0)`
is closed and one is open. Trace each endpoint to the hypothesis that produces it.
Then explain why swapping which endpoint is open would break the recovery of the
exact contradiction at `ε = 0`.

**Exercise 6.4.** Take `c = 0.5` and `ε = 0.2`. A model is ε-covering, ε-calibrated,
and faithful on a connected space. What is the widest possible interval the forced
question's truth-distance can occupy, and what is the largest confidence the forced
question can report? Now repeat for `ε = 0.02` and comment on the change.

**Exercise 6.5.** Prove the tightening principle's monotonicity claim directly: if
`0 ≤ ε₂ ≤ ε₁` then `[-ε₂, 0) ⊆ [-ε₁, 0)`. Then give a one-line reason why the
upper endpoint `0` does not participate in the tightening.

**Exercise 6.6.** (Independence, refuted.) Construct an informal scenario, no Lean
required, in which a model designer drives `ε` from `0.1` to `0.001` over several
iterations. Describe what happens to the forced question at each step and state, in
one sentence, why the designer cannot reach `ε = 0` while keeping faithfulness,
coverage, and continuity. Which of Theorems 6.9, 6.12, and 6.20 is the cleanest
statement of the obstruction?

**Exercise 6.7.** Prove Proposition 6.15 from scratch and then strengthen it: show
that if the confidence map is strictly monotone along some path from an
in-distribution point to an out-of-distribution point, the forced question on that
path is unique. Relate the non-uniqueness in general to Exercise 1.7 of Chapter 1.

**Exercise 6.8.** In the discrete bridge (Theorem 6.16), the conclusion is
conditional on a question existing in the upper band. Give an example of a discrete
model, faithful and ε-calibrated, for which _no_ question has confidence in
`[c, c + ε]`, and explain why the theorem is then vacuously satisfied and yet says
nothing useful. What extra hypothesis on the discrete model would force the band to
be nonempty?

**Exercise 6.9.** Re-elaborate `c6_band` from the text with `eps` replaced by a
_negative_ integer and observe how the proof behaves. What does a negative slack
mean, and why does Definition 6.1's hypothesis `ε ≥ 0` matter for the intended
reading even though the arithmetic still typechecks?

**Exercise 6.10.** Rescale confidence in Definition 6.18 by a factor of `100`,
mapping `c` and `γ` accordingly, and check that Theorem 6.19's conclusion interval
`[-ε, 0)` is unchanged while the confidence band `[c - γ, c + γ]` scales. Use this
to explain in one paragraph why the single-parameter Definition 6.1 is a
convenience rather than a canonical choice.

**Exercise 6.11.** Prove Theorem 6.24 (approximate Lawvere) as a direct
modification of the `lawvere` proof from Chapter 1: identify the single line where
the exact equality `f a₀ = d` becomes a distance bound, and confirm that
instantiating at the diagonal input is the only step that changes. Then state what
`approx_lawvere` becomes at `ε = 0` in a genuine metric space.

**Exercise 6.12.** In Theorem 6.25 the transparency slack `δ` appears with
coefficient `2` and the universality slack `ε` with coefficient `1`. Walk the path
`introspect a → M a a → t (M a a) → t (introspect a)` and attribute each unit of
the budget to a specific leg. Where exactly is the `1`-Lipschitz hypothesis used,
and what happens to the coefficient of `δ` if `t` is instead `K`-Lipschitz?

**Exercise 6.13.** (Composition.) Using Example 6.29's numbers, write down the
schematic risk figure as a product of a per-query band-incidence probability and a
per-event severity bound, and identify which factor Theorem 6.12 moves when `ε` is
halved and which factor Chapter 5's geometry controls. State one deployment
decision the figure could inform and one it cannot.

**Exercise 6.14.** (Harder, open-ended.) The calibration bridge produces an
interval `[-ε, 0)` and the degradation law produces a half-space `γ ≤ ε + 2 δ`.
Formulate a single abstract statement, with a slack inserted at each idealized
equality of a diagonal argument, that specializes to both. What would its
`ε → 0` corner be, and which theorem of Chapter 1 would that corner reproduce?

**Exercise 6.15.** Redo Example 6.8b with the truth field `δ(q) = q - 0.55`
replaced by `δ(q) = 2(q - 0.55)`, keeping `conf(q) = 1 - q`, `c = 0.5`, and
`ε = 0.1`. Recompute the coverage witnesses, verify faithfulness, find the forced
`q₀`, and report its truth-distance. Explain why the located `q₀` is the same
question as before but its truth-distance is different, and connect this to the
unit-separation point of Section "Two-slack separation".

**Exercise 6.16.** (Reading, harder.) Take the prompt-injection reading of Reading
6.33. State precisely what ε-coverage, ε-calibration, faithfulness, continuity, and
connectedness each assert about a real defended system, and for each one give a
concrete way it could fail in practice. Then identify which single failure a
determined adversary would most want to induce, and argue using Theorem 6.20 that
even a defense that avoids that failure still leaves a positive truth-slack band the
adversary can aim at.

**Exercise 6.17.** In Remark 6.27b the budget for a `K`-Lipschitz controller was
`ε + (1 + K) δ`. Rederive it by rewalking the triangle in Theorem 6.25 and
identify the exact leg whose bound changes from `δ` to `K δ`. Then determine the
threshold value of `K` below which perfect universality and perfect transparency
(`ε = δ = 0`) still permit a strictly positive controller margin, and interpret
that value.

**Exercise 6.18.** (Synthesis.) The chapter recovers two exact impossibilities as
zero-slack corners: the Hallucination Trilemma via `exact_from_approx` and the
Mirror Trilemma via `strict_limit_recovers_trilemma`. Write a one-page essay
identifying, for each, (i) which idealization was relaxed, (ii) which slack
parameter measured the relaxation, (iii) the shape of the achievable region, and
(iv) the geometric event, vertex or face, that the exact contradiction becomes at
the origin. Conclude with the single structural feature both share.
