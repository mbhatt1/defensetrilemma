import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "From Logic to Analysis" =>

The diagonal needs a system rich enough to name its own behaviors, and many real
models do not meet `∀ g, ∃ a, f a = g` literally. A trained network carries no
index for every function from prompts to confidences; its reachable states are a
bounded region, not a set closed under naming its own predicates.

The second engine runs on different fuel. It asks that the space be _connected_
and the maps _continuous_, and from those it extracts the same boundary object:
a question where confidence sits exactly at threshold while the answer sits
exactly on the truth boundary. The tool is the intermediate value theorem.

Code here is core Lean 4, elaborated as this document builds. The analytic
theorems live over `ℝ` and use topology, so their machine-checked forms are in
the companion `HallucinationProofs` library. Verified names appear in plain
type; the prose proofs are complete on their own terms and the names are
pointers, not omissions.

# Why a second engine

The engines answer different objections. Against a system that names its own
behaviors the diagonal is decisive. Against a system on a manifold of
activations it has no purchase, because no index need recover the diagonal
behavior. What such a system has is shape: a connected representation space,
continuous confidence, continuously varying correctness. That is enough.

In one sentence: self-reference forces a fixed point because a flip has nowhere
to hide on the diagonal; connectedness forces a crossing because a continuous
quantity negative somewhere and positive somewhere cannot pass between without
visiting zero. Both trap a value, one with a naming equation and one with a
topological wall. The trapped value is the same, and a later section makes that
identity exact.

Concretely: a proof-checker accepting the code of any predicate, or an
in-context learner promptable to any behavior, is close to the diagonal
hypothesis. A trained classifier reading truth off residual-stream activations
is not; it carries no index for every function from activations to confidences.
Yet its activations form a connected region, by the manifold hypothesis and the
modeling of embedding spaces as `ℝ^d` or connected submanifolds, and its probe
and confidence heads are continuous.

The analytic engine also carries metric content the diagonal cannot. With a
distance and Lipschitz maps, the crossing is not a bare witness but the centre
of a band of computable width. Chapter 5 is entirely about those quantities.

# A topology primer

*Definition 4.1 (Topological space).* A _topological space_ is a set `X` with a
collection of _open_ subsets including `∅` and `X`, closed under arbitrary
unions and finite intersections. A set is _closed_ when its complement is open.

*Definition 4.2 (Continuity).* `f : X → Y` is _continuous_ when the preimage of every
open set is open; equivalently, of every closed set is closed.

The preimage form is the same idea as epsilon-delta and easier to use, and it
makes continuity a statement about two topologies, which is the level at which
connectedness lives. The fact used repeatedly is that compositions of continuous
maps are continuous. The verified proofs build on Mathlib's `Continuous.comp`
and the product rule `Continuous.prodMk`, which is how `q ↦ δ(q, (M q).1)` is
shown continuous in `model_truth_boundary_nonempty`.

The _closure_ of `S` is the smallest closed set containing it; `S` is _dense_
when its closure is everything. Density is the topological form of the strongest
coverage condition, verified as `DenseCoverage` in `HoF_05_Coverage`, with
`denseCoverage_closure_eq_univ`. The main theorem uses only the mild two-sided
coverage of Definition 4.12.

_Metric spaces and paths._ A metric gives open balls, and the metric topology's
opens are the sets containing a ball around each point. Continuity in the
preimage sense agrees with epsilon-delta. The standing example is `ℝ^d`; the
verified sphere instantiation uses `EuclideanSpace ℝ (Fin d)`, and the
quantitative results use `PseudoMetricSpace` with explicit Lipschitz hypotheses.

A _path_ from `x` to `y` is a continuous `γ : [0,1] → X` with `γ 0 = x`, `γ 1 = y`,
and `X` is _path-connected_ when any two points are joined. Path-connected
implies connected: a path from one side of a separation to the other pulls it
back to a separation of `[0,1]`, which is connected. The converse can fail in
general but holds for the convex regions and manifolds of the applications.

Paths matter because interpolating hidden states from a true statement to its
negation traces a path, along which the realized truth-distance starts negative
and ends positive, so the one-variable theorem gives a crossing on the path
itself. That is `path_crosses_truth_boundary` in `HoF_03_BoundaryCrossing`, and
it is what an experiment actually walks along.

_Products._ If `X` and `Y` are connected so is `X × Y`: fix a base point, note
each slice through it is a continuous image of a connected space, and observe
that a union of slices meeting a common point cannot be separated. By induction
a finite product of connected spaces is connected. So if a single-turn space `Q`
is connected, the multi-turn space `Q^T` is too, and every argument transports
unchanged, since the only property used was connectedness.

*Definition 4.3 (Connected space).* `X` is _disconnected_ when open `U, V` exist with
`U ∪ V = X`, `U ∩ V = ∅`, both nonempty; _connected_ when nonempty and not
disconnected.

*Definition 4.4 (Preconnected set).* `S ⊆ X` is _preconnected_ when no open `U, V`
satisfy `S ⊆ U ∪ V`, `S ∩ U ∩ V = ∅`, `S ∩ U ≠ ∅`, and `S ∩ V ≠ ∅` at once. It
is _connected_ when also nonempty.

The distinction is only whether the empty set is admitted. Mathlib keeps them
apart because the intermediate value theorem is cleanest for preconnected sets,
and the verified files call that form. `isPreconnected_univ` is the first line
of every IVT application in `HoF_03_BoundaryCrossing` and `HoF_07_TrilemmaCore`.

Two examples fix the idea. Any interval of `ℝ` is connected, by completeness:
given a split, the supremum of the left part lies in neither piece without
contradicting openness. A two-point discrete space is disconnected.

*Proposition 4.5 (Continuous image of a preconnected set).* _If `S` is preconnected
and `f` continuous on `S`, then `f(S)` is preconnected._

_Proof._ A separation of `f(S)` by `U, V` pulls back to `f⁻¹(U)`, `f⁻¹(V)`, open by
continuity, covering `S`, missing `S` in their intersection, and each meeting
`S`. That separates `S`. ∎

This is `IsPreconnected.image` in Mathlib, and the companion proofs call it. It
is the load-bearing beam: connectedness is preserved by continuous maps, and
applied to a real-valued map that becomes the intermediate value theorem once we
know the connected subsets of the line.

*Proposition 4.6 (Connected subsets of the line are intervals).* _A subset of `ℝ` is
preconnected iff it is an interval._

_Proof._ If `S` omits `c` with `a < c < b` in `S`, the open rays about `c` separate it.
Conversely, let `S` be an interval separated by `U, V`, with `a ∈ S ∩ U`, `b ∈ S ∩ V`,
`a < b`. Let `m` be the supremum of points of `[a,b] ∩ U` below `b`, which
exists since the set is nonempty and bounded. As `S` is an interval, `m ∈ S`, so
`m ∈ U` or `m ∈ V`. If `m ∈ U`, openness pushes points of `U` above `m`,
contradicting the bound. If `m ∈ V`, openness puts points just below `m` in `V`
and not `U`, contradicting leastness. ∎

In Mathlib the forward direction is `IsPreconnected.ordConnected` and the
converse for a closed interval is `isPreconnected_Icc`.

*Theorem 4.7 (Intermediate value theorem).* _Let `X` be connected and `c : X → ℝ`
continuous. If `c` takes a value below `r` and one above `r`, it takes `r`._

_Proof._ The image is preconnected by Proposition 4.5, hence an interval by
Proposition 4.6, and it contains values on both sides of `r`. ∎

The library uses the two-function form `IsPreconnected.intermediate_value₂`,
comparing continuous `f` and `g` on a preconnected set: if `f a ≤ g a` and `g b ≤ f b`
then `f x = g x` somewhere. Theorem 4.7 is the case `g` constant. Every IVT call
in `HoF_03_BoundaryCrossing`, `HoF_05_Coverage`, and `HoF_07_TrilemmaCore` is
this form with `g = continuous_const`; the interval case via
`isPreconnected_Icc` is `confidence_path_crosses_half`.

*Remark 4.8 (What the theorem does not say).* It asserts existence, not uniqueness or
location. This is the analytic mirror of the diagonal's silence in Remark 1.18.
Both engines produce a witness with no built-in address, and metric content is
an extra ingredient added in Chapter 5.

## Connectedness as analytic self-reference

In Chapter 1 the diagonal took a flip with no fixed point and derived a
contradiction from universality, because a universal system must name `a ↦ t (f a a)`.
The engine is that self-application leaves the flip no room.

Connectedness plays the same role. A continuous quantity on a connected space
that is negative somewhere and positive somewhere is a flip with no room: a jump
would split the space into the negative and positive parts, two nonempty open
sets separating a space assumed unseparable. So it passes through zero.

The correspondences, each of which becomes a theorem: self-reference ↔
connectedness; the flip `t` ↔ a continuous field taking both signs; the forced
fixed point ↔ the forced zero; Boolean negation ↔ the real complement `y ↦ 1 - y`;
the liar index of Proposition 1.14 ↔ the boundary question.

The analogy is tight rather than loose. In both engines there is a set of
candidate outputs, a transformation on them, and a structural hypothesis leaving
the transformation nowhere to sit but a distinguished value. For the diagonal,
the outputs are the values `f a a`, the transformation is `t`, and the
hypothesis is that every behavior is named.

There is a shared failure mode. Remove the structural hypothesis and both
collapse the same way. A non-universal system can carry a fixed-point-free flip
with no contradiction, since the diagonal behavior may be unnamed.

# The model, analytically

*Definition 4.9 (Model).* For topological spaces `Q` of questions and `A` of answers,
a _model_ is `M : Q → A × ℝ`, with answer `(M q).1` and _confidence_ `(M q).2`.
It is _continuous_ when both components are.

Softmax outputs, probe readouts, and calibrated logits are continuous candidates
for the confidence; hard argmax decoding is not, a point priced in the discrete
section.

*Definition 4.10 (Signed truth-distance).* A _truth-distance_ is a continuous
`δ : Q × A → ℝ`, negative on strictly correct answers, positive on strictly
wrong ones, zero on the _truth boundary_. The _realized_ truth-distance is `q ↦ δ(q, (M q).1)`.

The sign convention is fixed: negative good, positive bad, zero the wall. A
linear probe `w·x - b` is a candidate `δ`, and whether its boundary tracks
semantic truth away from the fitted data is an empirical premise, not a theorem.
Continuity of the realized composite follows from the composition and product
rules.

*Definition 4.11 (Faithful).* A model is _faithful_ when `(M q).2 ≥ 1/2` implies
`δ(q, (M q).1) < 0`. The verified predicate is `TrilemmaFaithful`. The strict `< 0`
does the work; a weaker `≤ 0` admits the boundary case and dissolves the
theorem.

*Definition 4.12 (Covering).* A model is _covering_ when some `q` has
`δ(q, (M q).1) < 0` and some has `> 0`. The verified predicate is
`TrilemmaCovering`, also `Covering` in `HoF_05_Coverage`. It is the mildest
nontriviality assumption: any model ever correct and ever incorrect satisfies
it.

*Definition 4.13 (Calibrated).* A model is _strictly calibrated_ when for every `q`,
`(M q).2 > 1/2 ↔ δ(q, (M q).1) < 0` and `(M q).2 < 1/2 ↔ δ(q, (M q).1) > 0`. The
verified predicate is `StrictCalibrated`.

This pointwise biconditional is much stronger than statistical calibration,
which is an averaged claim compatible with being wrong on any particular
high-confidence question. Strict calibration constrains every single question.
It is the idealization a perfect truth probe used as confidence would meet,
which is why the empirical work builds the confidence from a probe and asks how
close reality comes.

Read the three on the linear-probe picture and none is a strawman. Covering says
the model answers on both sides of a hyperplane, which any model on a real
workload does. Calibration says a confidence head trained on a disjoint split
agrees with the probe about sides, which a well-trained head approximates.

Calibration is a biconditional because it claims the confidence is an honest
readout; faithfulness is one-way because a promise is one-directional. Neither
is at fault alone. Their conjunction on a connected covering model is.

## Separation with slack

Fix a threshold `τ`, truth slack `ε ≥ 0`, and confidence margin `γ ≥ 0`. A model
is _`(ε, γ)`-separating at `τ`_ when `δ < -ε` implies confidence `> τ + γ` and
`δ > ε` implies confidence `< τ - γ`. The slack is in truth-distance units and
the margin in confidence units, so the condition survives rescaling either
field.

Slack is not cosmetic: the main theorem is that with a threshold-inclusive
guarantee the truth slack cannot be zero. Using `1/2` for `τ` is a convention
the coupling results never depend on; every theorem has a general-`τ`
counterpart in the defense-side files.

## The defense reading

Reread `Q` as inputs a system might face including adversarial ones, `(M q).2`
as a _safety score_, and `δ` as a harm measure. Faithful becomes "a high safety
score certifies real safety," covering becomes "some inputs are safe and some
are not," calibration becomes "the score tracks the probe." The coupling theorem
then says a defense with a continuous safety score on a connected input space
owns an input scored exactly at threshold and lying exactly on the harm
boundary. This is `boundary_coupling` in `HoF_13_BoundaryCoupling`.

# The topological proof of the trilemma

Three steps. Coverage plus connectedness forces a confidence crossing.
Calibration pins the truth-distance to zero there. Faithfulness demands it be
strictly negative, and the two collide.

*Lemma 4.14 (Boundary existence).* _Let `Q` be connected, the answer map and
truth-distance continuous, and the model covering. Then some `q₀` has `δ(q₀, (M q₀).1) = 0`._

_Proof._ The realized truth-distance `F` is continuous, being a composite of the
continuous `q ↦ (q, (M q).1)` with `δ`. Coverage gives points where `F` is
negative and positive. Theorem 4.7 at value `0` gives `q₀`. ∎

This is `model_truth_boundary_nonempty` in `HoF_03_BoundaryCrossing`, packaged
with its coverage hypothesis as `covering_yields_truth_boundary_point` in
`HoF_05_Coverage`. It uses no confidence and no calibration: pure topology. The
boundary question exists before any safety condition enters. The wall is a fact
about the shape of the model's correctness, not about how it reports its
reliability.

Two structural facts, both verified and both independent of connectedness. The
boundary is closed, being the preimage of `{0}` under a continuous map, which is
`model_truth_boundary_isClosed` and holds over any topological spaces. And every
continuous path from a strictly-correct question to a strictly-wrong one crosses
it, which is `path_crosses_truth_boundary`.

*Lemma 4.15 (Confidence crossing).* _Let `Q` be connected and the confidence
continuous. If some question has confidence below `1/2` and some above, then
some `q₀` has `(M q₀).2 = 1/2`._

_Proof._ Theorem 4.7 applied to the confidence at `1/2`. ∎

This is `confidence_half_nonempty` and `model_confidence_half_set_nonempty`.
Alone it concerns the confidence field only; it becomes half the trilemma once
calibration ties the confidence witnesses to the coverage witnesses.

*Theorem 4.16 (Boundary-confidence coupling).* _Let `Q` be connected, all three maps
continuous, and the model covering and strictly calibrated. Then some `q₀`
satisfies_ `(M q₀).2 = 1/2` _and_ `δ(q₀, (M q₀).1) = 0`.

_Proof._ Coverage gives `q_t` with negative and `q_f` with positive truth-distance.
Calibration converts these into confidences above and below `1/2`. Lemma 4.15
gives `q₀` with confidence exactly `1/2`. Read calibration backward at `q₀`: a
negative truth-distance would force confidence above `1/2`, a positive one
below, both contradicting equality. So the truth-distance is `0`. ∎

This is `hallucination_trilemma_strict` in `HoF_07_TrilemmaCore`, with the
defense twin `boundary_coupling`. It mentions no faithfulness. It is a coupling
statement: a covering calibrated continuous model on a connected space owns a
question where the confidence is exactly ambiguous and the answer exactly on the
wall. The point is real regardless of any safety policy.

*Theorem 4.17 (Analytic hallucination trilemma).* _No continuous model on a connected
question space is simultaneously faithful, covering, and strictly calibrated._

_Proof._ Theorem 4.16 gives `q₀` with confidence `1/2` and truth-distance `0`.
Faithfulness applies there, since `1/2 ≥ 1/2`, and demands the truth-distance be
strictly negative. It is zero. ∎

This is `hallucination_trilemma`, with `hallucination_trilemma_unfolded`
alongside. The verified proof is the two-line composition: extract the coupled
point, apply faithfulness, observe the sign clash with `linarith`.

The policy reading makes this a taxonomy. Faithfulness as stated is
_threshold-inclusive_, triggering at confidence at least `1/2`, so it triggers
at the coupled point. A _threshold-exclusive_ guarantee triggers only strictly
above and so does not fire there.

This is why Theorem 4.16 is stated separately from Theorem 4.17. The coupling
theorem mentions no guarantee, so the coupled point exists under any threshold
policy. The guarantee only selects which clause applies.

## The forced question is the analytic liar

The coupled point is the analytic twin of the liar index of Proposition 1.14.
There the liar was an index whose self-application equalled its own negation;
here `q₀` is a question whose confidence equals the threshold and whose answer
sits on the boundary.

Both witnesses are non-unique for the same reason. If the diagonal behavior has
two names, both are liars; if the confidence crosses `1/2` more than once, every
crossing landing on the boundary is a coupled point. The witness is guaranteed
to exist and left unaddressed in both engines.

# A worked instance on the interval

Take `Q = [0,1]`, read `t` as a position interpolating from a question answered
truly at `0` to one answered falsely at `1`, and let the realized truth-distance
be `F(t) = 2t - 1`. The model is covering, with `F(0) = -1` and `F(1) = 1`.

Lemma 4.14 applies: `F` has a zero, here exactly `t = 1/2`. Strict calibration
forces confidence above `1/2` for `t < 1/2` and below for `t > 1/2`, so by Lemma
4.15 the continuous confidence crosses `1/2`, and only at `t = 1/2`. That is the
coupled point, exactly as Theorem 4.16 promises.

Add faithfulness and it breaks: at the coupled point the confidence is exactly
`1/2`, so faithfulness demands `F(1/2) < 0`, but `F(1/2) = 0`. If the confidence
tries to avoid `1/2` by jumping, it is not continuous, and dropping continuity
is a named escape priced in the discrete section.

The instance also shows what the exclusive guarantee buys. With the strict
antecedent the guarantee does not trigger at `t = 1/2` and no contradiction
arises. The model is consistent, but it owns a question on the truth boundary
about which its guarantee is silent. The wall did not move; the guarantee
stopped promising there.

# Quantitative shadows

*Theorem 4.17b (Approximate coupling).* _Let `Q` be connected, the confidence
continuous, and the model `ε`-covering, `(ε, γ)`-separating at `τ`, with a
threshold-inclusive guarantee. Then some `q₀` has `(M q₀).2 = τ` and `-ε ≤ δ(q₀, (M q₀).1) < 0`._

_Proof sketch._ The `ε`-coverage witnesses have truth-distance below `-ε` and above
`ε`, and separation turns these into confidence witnesses above `τ + γ` and
below `τ - γ`. The IVT lands `q₀` at confidence `τ`. Separation with slack no
longer pins the truth-distance to zero but confines it to `|δ| ≤ ε`, where
neither strict clause fires. The guarantee forces it strictly negative, giving
`[-ε, 0)`. ∎

The verified statement is `two_slack_approx_coupling` in `HoF_12_Approximate`,
carrying `ε` and `γ` as separate parameters. Theorem 4.16 is the `ε = 0` limit,
recovered as `exact_from_approx`.

*Corollary 4.17c (Positive slack is mandatory).* _Under those hypotheses the truth
slack cannot be zero._

_Proof._ At `ε = 0` the coupled point would lie in `[0, 0)`, which is empty, but the
IVT produced one. ∎

This is `truth_slack_must_be_positive`. Read it as a budget: a system keeping a
threshold-inclusive guarantee must keep a strictly positive margin of
correctness on the confident side, and the infimum of feasible slack is a
measurable width of the truth boundary. No question with confidence between `τ`
and `τ + γ` can sit exactly on the boundary, which is
`no_boundary_in_upper_band_two_slack`.

# Symmetry in place of coverage

*Definition 4.18 (Antipodal action).* An _antipodal action_ on `Q` is a continuous
self-inverse fixed-point-free `σ : Q → Q`. A real `g` is _odd_ under `σ` when `g (σ q) = -g q`.

Verified as `AntipodalAction` and `AntipodalOdd` in `HoF_08_BorsukUlam`. Layer
normalization places transformer states on a sphere-like shell, and semantic
negation is a candidate antipode, so oddness idealizes a truth-distance flipping
sign under negation.

*Theorem 4.19 (Odd fields vanish).* _Let `Q` be connected with an antipodal action
`σ`. Any continuous `g : Q → ℝ` odd under `σ` has a zero._

_Proof._ Pick `q`. If `g q = 0` we are done. Otherwise `g (σ q) = -g q` has the
opposite sign, so `g` takes both signs and Theorem 4.7 gives a zero. ∎

This is `antipodal_odd_has_zero`, and no coverage was assumed: oddness supplies
the two signs for free. A single question and its negation already straddle
zero.

There is a pleasant inversion. Equivariance is usually a design virtue, built in
so a network treats a question and its negation consistently. Here it is the
engine of the obstruction: a model respecting negation has an odd
truth-distance, and an odd continuous field on a connected symmetric space must
vanish. The better behaved the symmetry, the more inescapable the wall.

*Theorem 4.20 (Antipodal trilemma).* _Let `Q` be connected with an antipodal action,
the model continuous and strictly calibrated at `1/2`, and the realized
truth-distance odd. Then some `q` has `(M q).2 = 1/2` and `δ(q, (M q).1) = 0`._

_Proof._ Theorem 4.19 gives a zero `q`. Calibration then pins the confidence: above
`1/2` would force the truth-distance negative, below would force it positive. ∎

This is `antipodal_hallucination_trilemma`. Adding faithfulness produces the
same contradiction as Theorem 4.17, now with no coverage assumption anywhere.

The two engines' nontriviality demands differ instructively. Coverage is an
assumption about the model's _outputs_. The antipodal hypothesis is about the
_space and the field_.

The antipodal engine is robust to approximate symmetry, which matters because
real negation does not reflect truth directions exactly. If `|g (σ q) + g q| ≤ ε`
for all `q`, then some `q` has `|g q| ≤ ε/2`, recovering exact vanishing at `ε = 0`.
The verified robust form is `approx_odd_near_zero`, and the sphere instantiation
for `d ≥ 2`, using Mathlib's `isConnected_sphere`, is `sphere_odd_has_zero`.

The dimension hypothesis `d ≥ 2` is where connectedness of the sphere comes
from; the zero-dimensional sphere is two points and disconnected, the same
degeneracy that makes the diagonal the right tool for a two-point outcome set.
For any representation dimension used in practice the sphere is connected. The
one honest caveat is that exact oddness is an idealization; the measured defect
is nonzero but small, smallest for the strongest model, and
`approx_odd_near_zero` keeps a near-boundary point in existence under it.

# The discrete core

The topology does exactly one job: it manufactures a boundary question.
Everything after is arithmetic. The verified home is `HoF_10_PureDiscrete`.

This matters because token spaces are finite and one may object that
connectedness does illegitimate work. The discrete analysis prices the objection
exactly: without topology we must assume the boundary witness rather than derive
it. That is the entire cost.

Pricing an objection is the honest way to handle an idealization. A theorem with
a strong hypothesis invites the reader to reject it and walk away; the
disciplined response is to show how much of the conclusion survives without it.
Connectedness is a good model of an ambient representation space over which
probes are deployed at interpolated points, and a poor model of a scattered
token-driven reachable set.

```lean
theorem c4_flip_no_fixed_point : ∀ b : Bool, (!b) ≠ b :=
  by decide
```

Model confidence and truth-distance as integers with threshold `0`, calibration
as two biconditionals, faithfulness as the implication that non-negative
confidence forces a strictly negative truth-distance.

```lean
theorem c4_boundary_question_impossible
    (conf truth : Int)
    (cal_pos : 0 < conf ↔ truth < 0)
    (cal_neg : conf < 0 ↔ truth > 0)
    (faithful : 0 ≤ conf → truth < 0)
    (boundary : truth = 0) : False := by
  have hnp : ¬ (0 < conf) := by
    intro h; have := cal_pos.mp h; omega
  have hnn : ¬ (conf < 0) := by
    intro h; have := cal_neg.mp h; omega
  have hz : conf = 0 := by omega
  have hlt : truth < 0 := faithful (by omega)
  omega
```

This is the integer transcription of `boundary_question_impossible`. Read it
against Theorem 4.17: the two `have` blocks are calibration pinning the
confidence, the step Theorem 4.16 performed with the IVT replaced by an assumed
boundary value; the last lines are faithfulness and the sign clash. No topology
appears. Both the continuous and antipodal trilemmata factor through this core.

How would a discrete world produce a boundary value? Along a finite path the
truth-distance need not hit zero; it can jump across between adjacent steps.

```lean
theorem c4_discrete_sign_change (g : Nat → Int) :
    ∀ n, g 0 < 0 → 0 ≤ g n → ∃ i, i < n ∧ g i < 0 ∧ 0 ≤ g
    (i + 1) := by
  intro n
  induction n with
  | zero => intro h0 hn; exact absurd hn (by omega)
  | succ m ih =>
    intro h0 hn
    by_cases hm : 0 ≤ g m
    · obtain ⟨i, hlt, hneg, hpos⟩ := ih h0 hm
      exact ⟨i, Nat.lt_succ_of_lt hlt, hneg, hpos⟩
    · exact ⟨m, Nat.lt_succ_self m, by omega, hn⟩
```

A discrete field negative at the start and non-negative at the end has an
adjacent pair where it is still negative and has just become non-negative. It
never claims a step where the field is exactly zero. That gap is the whole
difference between settings: the continuum upgrades the straddle into an exact
witness. The verified counterpart is `discrete_sign_change`.

Two consequences, both verified. A model faithful and strictly calibrated with
witnesses for strictly correct, exactly boundary, and strictly wrong answers is
impossible with no topological hypothesis, which is
`discrete_hallucination_trilemma`; it trades connectedness for a stronger
coverage hypothesis. And, more revealingly, faithfulness is _equivalent_ to
boundary-freeness under calibration: `faithful_iff_boundary_free`.

## Adding randomness

A stochastic model does not dodge the obstruction, in two verified ways.

On expected fields, averaging is continuous, so the averaged confidence and
truth-distance are continuous on the connected space and the coupling theorem
applies verbatim, giving a question with expected confidence `1/2` and expected
truth-distance `0`. This is `stochastic_coupling_expected`.

The second converts expectation into samples and is the one place the theory
derives outright falsehood. Let the truth-distance have mean zero, let
sample-faithfulness hold almost everywhere, and let the confidence be at least
`1/2` with positive probability. Then the truth-distance is strictly positive
with positive probability. This is `stochastic_dichotomy`.

_Proof sketch._ If the truth-distance were almost never positive, then on the confident
event, of positive probability, faithfulness makes it strictly negative, and it
is non-positive elsewhere. Such a quantity has strictly negative mean,
contradicting mean-zero. ∎

Randomization spreads the boundary across samples instead of removing it. The
wall is either a point you pass through or a positive-probability event you
incur.

# Where the two engines meet

The claim is that the diagonal and the IVT locate the _same_ boundary object,
and that the Boolean flip and the real complement are two descriptions of one
wall. This is recorded as a theorem in `Foundation.F_04`.

In Chapter 1 the engine needed a flip with no fixed point, and for Booleans that
is negation. For real confidences the natural flip is the _complement
controller_ `y ↦ 1 - y`, which is not fixed-point-free: it has exactly one fixed
point, at `1/2`. This is `half_complement_fixed_point`, with the off-threshold
form `complement_no_fp_off_half`.

That single fixed point is the entire difference, and the reason both engines
reach the same place. The Boolean flip has none, so Lawvere's theorem, which
always produces a fixed point of the flip, produces a contradiction. The real
complement has one, so Lawvere run with it produces not a contradiction but a
point: a diagonal question where the confidence equals `1/2`.

Compare the routes. The IVT reaches `1/2` by connectedness: the confidence is
below and above, so it crosses. The diagonal reaches it by self-reference: the
confidence names a behavior complementing its own diagonal value, so it equals
its own complement.

What is shared is the boundary object and the final clash. What differs is the
hypothesis manufacturing the object, and neither implies the other. A finite
discrete model can be universal and carry no topology; a smooth model on a
manifold can be connected while naming almost none of its own behaviors.

There is a categorical way to say the shared part. Lawvere's theorem holds
cleanest for a _section_, and that form is true verbatim in any cartesian closed
category. The complement controller is an endomap of the reals with a single
fixed point, and Lawvere applied to a section of a real-valued self-prediction
delivers it on the diagonal.

The unification is packaged at two levels:
`hallucination_unification_documentation` and its lemmas in `Foundation.F_04`,
and `trilemmata_unified` with `hallucination_master_theorem` in
`F_13_UnifiedTrilemmata`.

One geometric remark closes the meeting point. When the truth-distance is a
linear probe the boundary is an affine hyperplane of codimension one, a
translate of the probe's kernel, by rank-nullity: `linear_probe_boundary_coset`
and `linear_probe_boundary_dim`. For a differentiable nonlinear probe it is a
hyperplane to first order at every regular point, with the tangent hyperplane
the kernel of the derivative, verified as `nonlinear_boundary_tangent` and
`tangent_hyperplane_dim`, and every regular point is itself a sign crossing
generating local coverage for free, `regular_point_is_crossing`.

# Where the two engines diverge

The diagonal gives a witness and nothing quantitative: not how many liars there
are, how hard one is to find, or what a search would cost. It cannot, because a
naming equation has no notion of distance, width, or margin.

The IVT alone is equally silent. The difference is that the analytic engine can
be fed more. Add a distance and Lipschitz maps and the bare crossing becomes
quantitative: the decisive regions are held apart by a distance controlled by
the Lipschitz constant and the margin, the coupled point sits at the centre of a
tube of computable radius, and truth-side slack must be strictly positive with a
measurable infimum.

Use the diagonal when the system names itself and you want the cleanest
existence proof with the smallest trust story. Use the IVT when the system lives
on a connected space, and if you also have a metric, keep going into Chapter 5.
Both reach the boundary; only the second measures it.

The engines also differ in what they say about escape. The diagonal is escaped
by breaking universality, which is hard to arrange without crippling a system
meant to handle arbitrary inputs. The analytic engine is escaped by breaking
connectedness, coverage, continuity, or exact separation, and each is a concrete
design lever.

# The engine in one page

Four moves. _Continuity:_ the realized truth-distance and confidence are
continuous, being built from continuous pieces by composition and pairing. _The
intermediate value theorem:_ on a connected space a continuous real field taking
values on both sides of a threshold takes the threshold; this is the only
analytic input, verified as `IsPreconnected.intermediate_value₂`.

Every variant is a substitution. The antipodal variant replaces coverage with a
symmetry supplying both signs. The discrete core keeps the last two moves and
assumes the boundary question.

# Historical notes

The intermediate value theorem is Bolzano's, and the formulation as preservation
of connectedness is standard. The reading of it as an impossibility engine for
learning systems is recent, and the machine-checked development is
`HallucinationProofs`, with the topological core in `HoF_03`, `HoF_05`,
`HoF_07`, the antipodal variant in `HoF_08`, and the discrete core in `HoF_10`.
The unification with the diagonal is `Foundation.F_04`.

The statistical inevitability results run on a different track: they argue a
calibrated model must hallucinate on rarely-seen facts, or that hallucination is
undecidable, and conclude that confident falsehood is unavoidable in aggregate.
The engine here is topological, localizes at a specific boundary question, and
is more modest, since the deterministic theorems yield uncertainty rather than
confident error. Only the stochastic dichotomy derives falsehood, and it needs
mean-zero to do it.
