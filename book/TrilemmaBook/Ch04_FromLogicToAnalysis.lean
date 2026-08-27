import VersoManual
import TrilemmaBook.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "From Logic to Analysis" =>

The diagonal of Chapter 1 needs a system rich enough to name its own behaviors.
The hypothesis `∀ g, ∃ a, f a = g` is a strong demand, and many real models do
not meet it in that literal form. A trained network does not carry an index for
every function from prompts to confidences. Its reachable states are a bounded
region, not a set closed under naming its own predicates. If the only engine we
had were the diagonal, half the impossibilities in these notes would sit outside
its reach.

There is a second engine, and it runs on different fuel. Instead of asking that a
space describe itself, it asks that the space be _connected_ and that the maps on
it be _continuous_. From those two analytic hypotheses it extracts the same
boundary object the diagonal extracts from self-reference: a question at which a
model's confidence sits exactly on the threshold while its answer sits exactly on
the truth boundary. The tool that does the extracting is the intermediate value
theorem, and this chapter is a full account of how it works, what it needs, and
why it lands on the same point the diagonal lands on.

The code blocks here are core Lean 4, self-contained and elaborated when the book
is built, exactly as in Chapter 1. The analytic theorems themselves live over the
real numbers and use topology, so their machine-checked forms are in the
companion `HallucinationProofs` library, which is built against Mathlib. Whenever
a result in this chapter has a verified counterpart there, its Lean name appears
in plain type, and the reader who wants the kernel-level guarantee can open the
named file. The prose proofs are complete on their own terms; the names are
pointers, not omissions.

# Why a second engine

The two engines answer different objections. Against a system that genuinely
names its own behaviors, the diagonal is decisive and needs nothing else. Against
a system that lives on a manifold of activations and computes with continuous
fields, the diagonal has no purchase, because there may be no index whose
self-application recovers the diagonal behavior. What such a system does have is
shape. Its representation space is a connected region, its confidence is a
continuous function of the input, and its correctness varies continuously as the
input moves. That shape is enough.

The move is worth stating in one sentence before we make it precise. Self-
reference forces a fixed point because a flip has nowhere to hide on the diagonal;
connectedness forces a crossing because a continuous quantity that is negative
somewhere and positive somewhere cannot get from one to the other without passing
through zero. Both arguments trap a value. One traps it with a naming equation,
the other with a topological wall. The trapped value is the same, and the later
sections make that identity exact rather than suggestive.

It is worth being concrete about which real systems fall to which engine. A
proof-checker that accepts the code of any predicate on proofs, or an in-context
learner promptable to imitate any behavior over prompts, is close to the diagonal
hypothesis, because it can be handed a description of the very behavior that would
refute it. A trained classifier reading truth off residual-stream activations is
not. It does not carry an index for every function from activations to confidences,
and there is no reason its reachable states are closed under naming their own
predicates. Yet its activations form a connected region, by the manifold hypothesis
and the way ambient embedding spaces are modeled as `ℝ^d` or connected submanifolds,
and its probe and confidence heads are continuous. The diagonal has nothing to grip
here, and the analytic engine has everything it needs. The two hypotheses carve the
space of systems differently, and a system that escapes one may sit squarely inside
the other.

There is a second reason to build the analytic engine carefully. It carries
metric content the diagonal cannot. Once the space has a distance and the maps are
Lipschitz, the crossing point is not a bare witness but the center of a band of
computable width, with decisive regions held a computable distance apart. The
diagonal never sees any of this. Chapter 5 is entirely about those quantities, and
it is available only because the engine we build here runs on geometry.

# A topology primer

This section develops just enough point-set topology to state and prove the
intermediate value theorem, and then explains why connectedness is the analytic
analogue of self-reference. A reader who knows the material can skim to the last
subsection, where the analogy is drawn. A reader who does not will find every
term defined before it is used.

## Open sets, continuity, and the shape of a space

A _topology_ on a set `X` is a choice of which subsets count as _open_. The
choice is not arbitrary. It must contain the empty set and all of `X`, it must be
closed under arbitrary unions, and it must be closed under finite intersections.
These axioms are the distilled content of "nearness" without a distance. In a
metric space the open sets are the usual ones, the sets that contain a small ball
around each of their points, but the axioms make sense with no metric at all, and
that generality is what lets the same theorems cover activation spaces, product
spaces, and spheres in one stroke.

**Definition 4.1 (Topological space).** A _topological space_ is a set `X`
together with a collection of subsets, called the _open sets_, that includes `∅`
and `X`, is closed under arbitrary unions, and is closed under finite
intersections. A set is _closed_ when its complement is open.

**Definition 4.2 (Continuity).** A map `f : X → Y` between topological spaces is
_continuous_ when the preimage `f⁻¹(U)` of every open set `U` in `Y` is open in
`X`. Equivalently, the preimage of every closed set is closed.

The preimage formulation looks abstract next to the epsilon-delta definition, but
it is the same idea and it is easier to use. For real-valued functions on a metric
space the two agree exactly. What the preimage form buys us is that continuity
becomes a statement about the interaction of two topologies, which is precisely
the level at which connectedness lives. The single fact we will use repeatedly is
that a composition of continuous maps is continuous, which is immediate from the
definition: if `f` and `g` are continuous then `(g ∘ f)⁻¹(U) = f⁻¹(g⁻¹(U))` is
open whenever `U` is. The verified proofs lean on exactly this closure property,
built from Mathlib's `Continuous.comp` and the product rule `Continuous.prodMk`,
which is how the composite `q ↦ δ(q, (M q).1)` is shown continuous in
`model_truth_boundary_nonempty`.

Two closure notions we will need later belong here. The _closure_ of a set `S` is
the smallest closed set containing it, the set of points every neighborhood of
which meets `S`. A set is _dense_ when its closure is the whole space, meaning
every point is approximable by members of the set. Density is the topological form
of the strongest coverage condition, where the model's answers come arbitrarily
close to every answer, and the verified predicate `DenseCoverage` in
`HoF_05_Coverage` is exactly this, with `denseCoverage_closure_eq_univ` recording
that a dense answer image has closure equal to everything. We use the mild two-
sided coverage of Definition 4.12 for the main theorem and mention density only to
place it on the same scale.

## Metric spaces, balls, and paths

Most spaces in the applications carry a distance, and it is worth seeing how the
abstract topology specializes to that case, because the quantitative results of
Chapter 5 live there. A _metric_ on a set `X` assigns to each pair of points a
non-negative real distance that is zero exactly for equal points, is symmetric,
and satisfies the triangle inequality. The _open ball_ of radius `r` around a
point `x` is the set of points within distance `r` of `x`. A set is open in the
_metric topology_ when it contains an open ball around each of its points. One
checks directly that these open sets satisfy the axioms of Definition 4.1, so
every metric space is a topological space, and continuity in the preimage sense of
Definition 4.2 agrees with the epsilon-delta sense for maps between metric spaces.

The space `ℝ^d` with the usual Euclidean distance is the standing example. Ambient
embedding spaces and residual streams are modeled as `ℝ^d` or as connected
submanifolds of it, and both are metric spaces, so the abstract theorems apply and
the metric refinements of Chapter 5 become available. The verified sphere
instantiation uses the Euclidean space `EuclideanSpace ℝ (Fin d)`, and the
quantitative results use `PseudoMetricSpace` with explicit Lipschitz hypotheses.

A _path_ in `X` from `x` to `y` is a continuous map `γ` from the unit interval
`[0, 1]` to `X` with `γ 0 = x` and `γ 1 = y`. A space is _path-connected_ when any
two points are joined by a path. Path-connectedness is stronger than
connectedness, and the implication one way is direct: if a path-connected space
split into two separating open sets, a path from a point in one to a point in the
other would pull the separation back to a separation of the interval `[0, 1]`,
which is connected, a contradiction. So path-connected implies connected. The
converse can fail in general, but for the spaces in the applications, which are
convex regions or manifolds, the two coincide and either can be assumed.

Paths matter because the intermediate value theorem has a path form that is often
the concrete face of the connected-space form. Interpolating hidden states from a
true statement to its negation traces a path in representation space, and along
that path the realized truth-distance is a continuous real function that starts
negative and ends positive. The one-variable intermediate value theorem then gives
a boundary crossing on the path itself, which is `path_crosses_truth_boundary` in
`HoF_03_BoundaryCrossing`. The connected-space form of Lemma 4.14 below does not
require a path, but the path form is what an experiment actually walks along, and
it is how the companion paper observes the crossing in real models.

## Products, and staying connected

One construction preserves connectedness and matters for the multi-turn extension
later. If `X` and `Y` are connected, so is the product `X × Y` with the product
topology, in which a set is open when it is a union of products of open sets. The
proof is a two-step slide: fix a base point, note that each horizontal slice and
each vertical slice through it is a continuous image of a connected space and so
connected, and observe that the union of all slices meeting a common point cannot
be separated. By induction a finite product of connected spaces is connected.

The consequence we use is that if a single-turn question space `Q` is connected,
then the multi-turn space `Q^T` of conversation histories of length `T` is
connected as well. Every argument in this chapter transports to `Q^T` unchanged,
because the only property of `Q` any proof used was its connectedness. The verified
statement that interaction does not escape the obstruction is
`multi_turn_history_dependent`. A conversation is not a way out. It is a walk on a
larger connected space, and the same wall is somewhere on it.

## Connected and preconnected spaces

Connectedness is the property of being all one piece. The clean way to say "all
one piece" is negative: a space is disconnected when it splits into two nonempty
open sets that do not meet. Ruling that out is the definition.

**Definition 4.3 (Connected space).** A topological space `X` is _disconnected_
when there exist open sets `U` and `V` with `U ∪ V = X`, `U ∩ V = ∅`, and both
`U` and `V` nonempty. `X` is _connected_ when it is nonempty and not
disconnected.

**Definition 4.4 (Preconnected set).** A subset `S ⊆ X` is _preconnected_ when it
cannot be separated by two open sets of `X`, that is, whenever `U` and `V` are
open, `S ⊆ U ∪ V`, `S ∩ U ∩ V = ∅`, `S ∩ U ≠ ∅`, and `S ∩ V ≠ ∅` all hold at
once, we have a contradiction. A set is _connected_ when it is preconnected and
nonempty.

The distinction between preconnected and connected is only whether the empty set
is admitted. The empty set is preconnected and not connected, since connectedness
demands a point. Mathlib keeps the two apart because the intermediate value
theorem is cleanest as a statement about preconnected sets, and the verified
files call the preconnected form directly. The name to hold onto is
`IsPreconnected`, and the fact that the whole space is preconnected when `X`
carries a `ConnectedSpace` instance is `isPreconnected_univ`, which is the first
line of every IVT application in `HoF_03_BoundaryCrossing` and
`HoF_07_TrilemmaCore`.

Two examples fix the idea. An interval of the real line is connected. Any interval,
open, closed, or half-open, bounded or not, cannot be split into two nonempty
disjoint open pieces, and the proof is the completeness of the reals: given a
split, the supremum of the part on the left is a point that can lie in neither
piece without contradicting openness. A two-point discrete space is disconnected,
since each point is open and the two singletons separate it. The contrast is the
whole story. The reals are connected and the booleans are not, which is exactly
why the analytic engine runs on the reals and the diagonal engine runs on the
booleans, and why the two meet only at the point where a real threshold and a
boolean flip describe the same wall.

**Proposition 4.5 (Continuous image of a preconnected set).** _If `S ⊆ X` is
preconnected and `f : X → Y` is continuous on `S`, then the image `f(S)` is
preconnected in `Y`._

_Proof._ Suppose `f(S)` were separated by open sets `U` and `V` in `Y`. Then
`f⁻¹(U)` and `f⁻¹(V)` are open in `X` by continuity, they cover `S`, their
intersection misses `S`, and each meets `S` because `U` and `V` each meet `f(S)`.
That is a separation of `S`, contradicting preconnectedness. So no separation of
`f(S)` exists. ∎

This is `IsPreconnected.image` in `Mathlib`, and the verified proofs in the
companion libraries call it rather than reproving it.

Proposition 4.5 is the engine's load-bearing beam. Connectedness is preserved by
continuous maps, and that single preservation fact, applied to a real-valued map,
becomes the intermediate value theorem once we know what the connected subsets of
the real line are.

**Proposition 4.6 (Connected subsets of the line are intervals).** _A subset of
`ℝ` is preconnected if and only if it is an interval, meaning that whenever it
contains two points it contains everything between them._

_Proof._ One direction is a construction. If a set `S` omits a point `c` strictly
between two of its members `a < c < b`, then the open rays `(-∞, c)` and `(c, ∞)`
cover `S`, do not meet, and each contains a member of `S`, namely `a` and `b`. That
is a separation, so `S` is not preconnected.

The other direction is where completeness of the reals enters. Suppose `S` is an
interval and, for contradiction, that open sets `U` and `V` separate it. Pick
`a ∈ S ∩ U` and `b ∈ S ∩ V`, and assume `a < b` without loss. Let `m` be the
supremum of the set of points in `[a, b] ∩ U` that lie below `b`. This supremum
exists because the set is nonempty, containing `a`, and bounded above by `b`. Since
`S` is an interval and `a, b ∈ S`, the point `m` lies in `S`, so it lies in `U` or
in `V`. If `m ∈ U`, then `U` open gives a small interval around `m` inside `U`,
which pushes points of `U` above `m` and below `b`, contradicting that `m` is an
upper bound. If `m ∈ V`, then `V` open gives a small interval around `m` inside
`V`, so points just below `m` lie in `V` and not in `U`, contradicting that `m` is
the least upper bound of the `U` side. Either way a contradiction, so no separation
exists and `S` is preconnected. ∎

In `Mathlib` the forward direction is `IsPreconnected.ordConnected` and the
converse for a closed interval is `isPreconnected_Icc`; together they are the
statement above, and the companion libraries use them in that form.

## The intermediate value theorem

Put the two propositions together. A continuous real-valued function on a
connected space has a preconnected image by Proposition 4.5, that image is an
interval by Proposition 4.6, and an interval that contains two values contains
every value between them. That is the intermediate value theorem, and it is the
only analytic input the chapter needs.

**Theorem 4.7 (Intermediate value theorem).** _Let `X` be connected and
`c : X → ℝ` continuous. If `c` takes a value below `r` at some point and a value
above `r` at some point, then `c` takes the value `r` at some point._

_Proof._ Let `x₋` and `x₊` be points with `c(x₋) < r < c(x₊)`. The image `c(X)`
is preconnected by Proposition 4.5, hence an interval by Proposition 4.6. It
contains `c(x₋)` and `c(x₊)`, so it contains every value between them, and `r` is
such a value. Therefore `r ∈ c(X)`, which means `c(x₀) = r` for some `x₀`. ∎

The verified library uses a two-function form that is a little more flexible and
slightly more convenient in proofs. The name is
`IsPreconnected.intermediate_value₂`. Instead of comparing one function to a
constant `r`, it compares two continuous functions `f` and `g` on a preconnected
set: if `f a ≤ g a` at one endpoint and `g b ≤ f b` at the other, then `f x = g x`
at some interior point. Taking `g` to be the constant function with value `r`
recovers Theorem 4.7, because `f a ≤ r` and `r ≤ f b` force `f x = r` somewhere.
Every IVT call in `HoF_03_BoundaryCrossing`, `HoF_05_Coverage`, and
`HoF_07_TrilemmaCore` is this two-function form with `g = continuous_const`, and
the one-dimensional special case, an interval `[a, b]` treated as a preconnected
set via `isPreconnected_Icc`, is `confidence_path_crosses_half`.

**Remark 4.8 (What the theorem does not say).** The intermediate value theorem
asserts existence, not uniqueness and not location. It gives a point where the
value is hit, and says nothing about how many such points there are, where they
sit, or how a search would find one. This is the analytic mirror of the
diagonal's silence in Remark 1.14. Both engines produce a witness with no built-
in address. Metric content is an extra ingredient, added in Chapter 5, and it is
what turns the bare crossing into a band of known width.

## Connectedness as analytic self-reference

Here is the analogy the chapter is built around, stated plainly. In Chapter 1 the
diagonal took a flip `t` with no fixed point and derived a contradiction from
universality, because a universal system must name the behavior `a ↦ t (f a a)`,
and the naming equation then forces `f a₀ a₀ = t (f a₀ a₀)`, a fixed point of a
map that has none. The engine of that argument is that self-application leaves the
flip no room. There is a diagonal, and the flip must land on it.

Connectedness plays the same structural role. A continuous quantity on a connected
space that is negative somewhere and positive somewhere is a flip with no room. It
cannot jump from negative to positive, because a jump would split the space into
the part where the quantity is negative and the part where it is positive, two
nonempty open sets that separate a space we assumed cannot be separated. So the
quantity must pass through zero. The zero is forced by the shape of the space in
exactly the way the fixed point was forced by the naming equation. Where the
diagonal says "the behavior is named, so evaluate at its own index," connectedness
says "the space is one piece, so the sign cannot flip without a crossing."

The parallel is not a metaphor that breaks under pressure. It is an equality of
outputs, and Section "Where the two engines meet" proves it as such. For now, hold
the following table of correspondences, which the rest of the chapter fills in.
Self-reference corresponds to connectedness. The behavior flip `t` corresponds to
a continuous field taking both signs. The forced fixed point corresponds to the
forced zero. The Boolean negation `(!·)` corresponds to the real complement map
`y ↦ 1 - y`. The liar index of Proposition 1.10 corresponds to the boundary
question this chapter constructs. Each row is a theorem, and by the end each will
be one.

It helps to see why the analogy is tight rather than loose, since two arguments
can reach the same conclusion for unrelated reasons. Here the reasons are the same
shape. In both engines there is a set of candidate outputs, a transformation on
those outputs, and a structural hypothesis that leaves the transformation nowhere
to sit except on a distinguished value. For the diagonal the candidate outputs are
the values `f a a` along the diagonal, the transformation is `t`, and the
structural hypothesis is that every behavior is named, so the diagonal behavior
`a ↦ t (f a a)` is itself some `f a₀`, and evaluation forces `f a₀ a₀` onto a
fixed point of `t`. For the intermediate value theorem the candidate outputs are
the values of a continuous field, the transformation is the passage from one sign
to the other, and the structural hypothesis is connectedness, which forbids the
field from changing sign without visiting zero. In each case a hypothesis about the
_domain_, richness of naming or one-piece-ness, constrains the _range_ to hit a
particular value.

There is even a shared failure mode. Remove the structural hypothesis and both
arguments collapse in the same way. A non-universal system can carry a fixed-point-
free flip with no contradiction, since the offending diagonal behavior may simply
be unnamed. A disconnected space can carry a sign-changing continuous field with no
zero, since the field can be negative on one piece and positive on another with a
gap between. This is why abstention breaks the analytic argument. Declining to
answer on an open region deletes that region and can disconnect the correct part
from the incorrect part, which is the topological form of refusing to name the
diagonal behavior. The two engines fail together, under the same move, which is one
more sign that they are two views of a single mechanism.

# The model, analytically

We now set up the object the analytic engine acts on. It is the continuous
counterpart of the reflective verdict of Definition 1.11, and the reader should
watch the three conditions of Chapter 3 reappear here in metric dress.

## The confidence map and the truth-distance

**Definition 4.9 (Model).** Fix a topological space `Q` of _questions_ and a
topological space `A` of _answers_. A _model_ is a map `M : Q → A × ℝ`. For a
question `q`, the answer is `(M q).1` and the _confidence_ is `(M q).2`, a real
number. The model is _continuous_ when both components are continuous, that is
when `q ↦ (M q).1` and `q ↦ (M q).2` are continuous.

Reading `Q` as a space of prompt embeddings or residual-stream states, and `A` as
the space of possible answers, this is the shape of a trained model whose fields
are defined on its representation space. The confidence is a scalar the model
attaches to its answer, an internal estimate of how sure it is. Softmax outputs,
probe readouts, and calibrated logits are all continuous candidates for
`(M q).2`, while hard argmax decoding is not continuous, a point we return to when
the discrete core is priced.

**Definition 4.10 (Signed truth-distance).** A _truth-distance_ is a continuous
map `δ : Q × A → ℝ`. It is a signed measure of correctness: `δ(q, a) < 0` on
strictly correct answers, `δ(q, a) > 0` on strictly wrong ones, and `δ(q, a) = 0`
on the _truth boundary_. The _truth set_ is `{δ ≤ 0}` and the _boundary_ is
`{δ = 0}`. The _realized_ truth-distance of the model is the composite
`q ↦ δ(q, (M q).1)`, the truth-distance of the answer the model actually gives.

The sign convention is a choice and we keep it fixed: negative is good, positive
is bad, zero is the wall between them. A linear truth probe `w·x - b` on
activations is a candidate `δ`, and its zero set is the probe's classification
boundary. Whether that boundary tracks semantic truth away from the fitted data
is an empirical premise, not a theorem, and the results here hold under whatever
`δ` one commits to. The realized composite is the only thing the theorems touch,
and its continuity follows from continuity of `δ` and of the answer map by the
composition and product rules, which is `model_truth_boundary_isClosed`'s first
step.

## Faithful, covering, calibrated

The three conditions of Chapter 3 have exact analytic forms. Each says something
about how the confidence `(M q).2` relates to the realized truth-distance
`δ(q, (M q).1)`, with the threshold set at `1/2`. The threshold is a convention;
any fixed value works and the verified defense results carry a general threshold
`τ`, but `1/2` is the natural center for a confidence that ranges in the unit
interval, so we use it throughout.

**Definition 4.11 (Faithful).** A model is _faithful_ when high confidence
guarantees correctness, in the strong form: for every question `q`, if
`(M q).2 ≥ 1/2` then `δ(q, (M q).1) < 0`. The verified predicate is
`TrilemmaFaithful`, and the strictness of the inequality `< 0` is what does the
work. A weaker `≤ 0` form would admit the boundary case and dissolve the theorem,
which is the whole content of the inclusive-versus-exclusive threshold
distinction discussed below.

**Definition 4.12 (Covering).** A model is _covering_ when it produces answers on
both sides of the boundary: there is a question `q` with `δ(q, (M q).1) < 0` and a
question `q` with `δ(q, (M q).1) > 0`. The model is sometimes right and sometimes
wrong. The verified predicate is `TrilemmaCovering`, also stated as `Covering` in
`HoF_05_Coverage`, and it is the mildest possible non-triviality assumption: any
general-purpose model that is ever correct and ever incorrect satisfies it.

**Definition 4.13 (Calibrated).** A model is _strictly calibrated_ when the side
of the threshold the confidence sits on matches the side of the boundary the
answer sits on, in both directions: for every `q`,

`(M q).2 > 1/2 ↔ δ(q, (M q).1) < 0` and `(M q).2 < 1/2 ↔ δ(q, (M q).1) > 0`.

The verified predicate is `StrictCalibrated`. This is a pointwise biconditional,
much stronger than the statistical calibration of the empirical literature, and it
is one-way strengthened into an equivalence. High confidence and correctness
determine each other, and low confidence and error determine each other, question
by question.

The gap between this pointwise condition and ordinary statistical calibration is
worth naming, because they are easy to confuse. Statistical calibration is an
averaged claim: among all questions the model answers with confidence near `0.7`,
about seventy percent are correct. It is compatible with the model being wrong on
any particular high-confidence question, as long as the frequencies work out.
Strict calibration is not averaged. It constrains every single question. If the
confidence is above the threshold at `q`, the answer at `q` is correct, full stop.
This is a demanding idealization, and it is exactly the idealization a perfect
truth probe used as a confidence signal would meet, which is why the empirical work
builds `(M q).2` from a probe and asks how close reality comes. The slack version
of the condition, introduced below, is the honest relaxation, and the strict form
is its sharp corner.

Read the three conditions together on the linear-probe picture to see they are not
exotic. Let `δ` be a linear probe `w·x - b`, so `δ < 0` on one side of a hyperplane
and `δ > 0` on the other. Covering says the model produces answers on both sides,
which any model used across a real workload does. Calibration says the confidence
head, trained on a disjoint split of the same activations, agrees with the probe
about which side each answer is on, which is what a well-trained confidence head
approximates. Faithfulness says a confident answer is a correct one, which is the
safety promise the whole enterprise wants to keep. None of the three is a strawman.
Each is a target that probing and steering pipelines actively pursue. The chapter's
content is that pursuing all three at once, on a connected space, is pursuing a
contradiction, and the coupled point is where the pursuit fails.

A word on why calibration is stated as a biconditional and faithfulness as a one-
way implication. Calibration is a claim about the confidence being an honest
readout of the truth-distance, so both directions belong to it. Faithfulness is a
safety guarantee, a promise that the model only asserts what is correct, and a
promise is naturally one-directional. The interplay of the strict inequality in
faithfulness with the equality that calibration forces at the boundary is the
contradiction, and it is worth seeing that neither condition alone is at fault.
Each is reasonable. Their conjunction on a connected covering model is not.

## Separation with slack, and the general threshold

The strict biconditional of Definition 4.13 is the sharpest form, and it is what
the impossibility uses, but the applied results are stated with slack so that the
idealization can be relaxed at a named price. Fix a threshold `τ`, a truth slack
`ε ≥ 0`, and a confidence margin `γ ≥ 0`. A model is _`(ε, γ)`-separating at `τ`_
when `δ(q, (M q).1) < -ε` implies `(M q).2 > τ + γ`, and `δ(q, (M q).1) > ε`
implies `(M q).2 < τ - γ`. The slack sits in units of the truth-distance and the
margin in units of confidence, so the condition survives rescaling either field.
Exact separation is the case `ε = γ = 0`. The verified predicate is
`TwoSlackSeparating`, with the equal-slack special case `EpsCalibrated` and the
bridge `epsCalibrated_iff_twoSlack`, and the strict biconditional maps into it by
`strictCalibrated_to_epsCalibrated_zero_half`. Coverage generalizes the same way to
`ε`-coverage, some question with `δ < -ε` and some with `δ > ε`, verified as
`EpsCovering`.

Slack is not cosmetic. The main theorem is that with a threshold-inclusive
guarantee the truth slack cannot be zero, so a model is forced to keep a strictly
positive margin of correctness on the confident side. We state that quantitative
form in a later section. Here the point is only that the strict conditions of
Definitions 4.11 through 4.13 are the `ε = γ = 0` corner of a graded family, and
that using `1/2` for `τ` is a convention the coupling results never depend on. The
biconditional variant sits at `τ = 1/2` because a confidence bounded in the unit
interval has its natural center there, but every theorem below has a general-`τ`
counterpart in the defense-side files.

## The defense reading

The same setup describes a defense rather than a bare model, and the reader should
carry both readings, since Chapter 3 needs the defense form. Reread `Q` as a space
of inputs a system might face, including adversarial ones, `(M q).2` as a _safety
score_ the defense attaches to an input, and `δ` as a _truth probe_ or harm
measure whose sign says whether the input is actually safe. Faithful becomes the
guarantee that a high safety score certifies real safety, covering becomes the fact
that some inputs are safe and some are not, and calibration becomes the safety
score tracking the truth probe. The coupling theorem then says a defense with a
continuous safety score on a connected input space owns an input where the safety
score is exactly at threshold and the input is exactly on the harm boundary. This
is `boundary_coupling` in `HoF_13_BoundaryCoupling`, run on the safety score and
the truth probe rather than on confidence and truth-distance. Prompt injection is
the covering witness on the unsafe side: a family of inputs the defense must score,
carrying both safe and unsafe members, which is exactly what coverage asks for.
Nothing in the mathematics changes. Only the names on `M` and `δ` change.

# The topological proof of the trilemma

We now prove the analytic trilemma in full. The structure is three steps.
Coverage plus connectedness forces a confidence crossing. Calibration pins the
truth-distance to zero at that crossing. Faithfulness demands the truth-distance
be strictly negative there, and the two collide. Each step is a numbered result,
and each has a verified counterpart named in place.

## Step one: coverage forces a confidence crossing

**Lemma 4.14 (Boundary existence).** _Let `Q` be connected, let the answer map
and the truth-distance be continuous, and let the model be covering. Then some
question `q₀` has `δ(q₀, (M q₀).1) = 0`._

_Proof._ The realized truth-distance `F(q) = δ(q, (M q).1)` is continuous, being
the composite of the continuous map `q ↦ (q, (M q).1)` with the continuous `δ`.
Coverage gives a question where `F` is negative and a question where `F` is
positive. By the intermediate value theorem, Theorem 4.7, applied to `F` on the
connected space `Q` at the value `0`, there is a `q₀` with `F(q₀) = 0`. ∎

This is `model_truth_boundary_nonempty` in `HoF_03_BoundaryCrossing`, and its
coverage-hypothesis packaging is `covering_yields_truth_boundary_point` in
`HoF_05_Coverage`. It uses no confidence and no calibration. It is pure topology:
a continuous field that changes sign on a connected space has a zero. Notice that
the boundary question exists before any of the safety conditions enter. The wall
is a fact about the shape of the model's correctness, not about how the model
reports its own reliability.

Two structural facts about this boundary set are worth recording, both verified and
both independent of connectedness. First, the boundary is closed. The set of
questions whose realized truth-distance is zero is the preimage of the closed
singleton `{0}` under the continuous realized truth-distance, and preimages of
closed sets are closed. This is `model_truth_boundary_isClosed`, and it holds over
any topological question and answer spaces, with no connectedness needed. Second,
every continuous path from a strictly-correct question to a strictly-wrong one
crosses the boundary. Along the path the realized truth-distance is a continuous
real function that starts negative and ends positive, so the one-variable
intermediate value theorem gives a crossing on the path, which is
`path_crosses_truth_boundary`. The boundary is not a fragile artifact of one clever
argument. It is a closed set that blocks every route from truth to falsehood, and
Lemma 4.14 is the statement that on a connected space such a route always exists to
be blocked.

There is a companion crossing on the confidence side, proved the same way.

**Lemma 4.15 (Confidence crossing).** _Let `Q` be connected and let the
confidence map be continuous. If some question has confidence below `1/2` and some
has confidence above `1/2`, then some question `q₀` has `(M q₀).2 = 1/2`._

_Proof._ Apply the intermediate value theorem to the continuous confidence map
`q ↦ (M q).2` at the value `1/2`. ∎

This is `confidence_half_nonempty` and `model_confidence_half_set_nonempty` in
`HoF_03_BoundaryCrossing`. On its own it is a statement about the confidence field
alone. It becomes half of the trilemma once calibration ties the confidence
witnesses to the coverage witnesses, which is the next step.

## Step two: calibration pins the truth-distance

The trilemma's core obstruction is the combination of Lemma 4.15 with strict
calibration. Coverage gives a question that is strictly correct and a question
that is strictly wrong. Calibration turns these into confidence witnesses on both
sides of `1/2`. The confidence crossing then lands a question exactly at `1/2`,
and calibration read backward pins its truth-distance to exactly `0`.

**Theorem 4.16 (Boundary-confidence coupling).** _Let `Q` be connected, let the
answer map, confidence map, and truth-distance be continuous, and let the model be
covering and strictly calibrated. Then some question `q₀` satisfies both_
`(M q₀).2 = 1/2` _and_ `δ(q₀, (M q₀).1) = 0`.

_Proof._ Coverage gives `q_t` with `δ(q_t, (M q_t).1) < 0` and `q_f` with
`δ(q_f, (M q_f).1) > 0`. Strict calibration converts these: from
`δ(q_t, (M q_t).1) < 0` and the first biconditional we get `(M q_t).2 > 1/2`, and
from `δ(q_f, (M q_f).1) > 0` and the second biconditional we get
`(M q_f).2 < 1/2`. The confidence map is continuous and takes a value above and a
value below `1/2`, so by Lemma 4.15 there is a `q₀` with `(M q₀).2 = 1/2`.

Now read calibration backward at `q₀`. If `δ(q₀, (M q₀).1)` were negative, the
first biconditional would give `(M q₀).2 > 1/2`, contradicting `(M q₀).2 = 1/2`.
If it were positive, the second biconditional would give `(M q₀).2 < 1/2`, again a
contradiction. The only remaining possibility is `δ(q₀, (M q₀).1) = 0`. ∎

This is `hallucination_trilemma_strict` in `HoF_07_TrilemmaCore`, and its defense-
side twin, run on a safety score and a truth probe, is `boundary_coupling` in
`HoF_13_BoundaryCoupling`. The theorem mentions no faithfulness. It is a coupling
statement: a covering, calibrated, continuous model on a connected space owns a
question where the confidence is exactly ambiguous and the answer is exactly on
the wall. The point is real regardless of any safety policy. What a policy makes
of it is the next step.

## Step three: faithfulness contradicts the boundary

**Theorem 4.17 (Analytic hallucination trilemma).** _No continuous model on a
connected question space can be simultaneously faithful, covering, and strictly
calibrated._

_Proof._ Suppose all three hold. By Theorem 4.16 there is a question `q₀` with
`(M q₀).2 = 1/2` and `δ(q₀, (M q₀).1) = 0`. Faithfulness applies at `q₀`, because
`(M q₀).2 = 1/2 ≥ 1/2`, and it demands `δ(q₀, (M q₀).1) < 0`. But calibration
pinned that same quantity to `0`. A number cannot be both strictly negative and
zero. Contradiction. ∎

This is `hallucination_trilemma` in `HoF_07_TrilemmaCore`, with the fully unfolded
statement `hallucination_trilemma_unfolded` alongside it. The three conditions are
individually sensible and jointly impossible. The verified proof is the two-line
composition the prose describes: extract the coupled point, then apply
faithfulness to it and observe the sign clash with `linarith`.

The policy reading is where this becomes a taxonomy rather than a single
impossibility. Faithfulness as stated is _threshold-inclusive_: it triggers at
confidence at least `1/2`, so it triggers at the coupled point, and the
contradiction follows. A _threshold-exclusive_ guarantee, which triggers only at
confidence strictly above `1/2`, does not trigger at the coupled point, since the
confidence there is exactly `1/2`. Such a guarantee is consistent, but it is
silent exactly where topology guarantees a question exists. The verified forms of
both branches are `closed_guarantee_impossible` and `open_guarantee_silent`. The
lesson is that defining the guarantee with a strict inequality does not dissolve
the obstruction. It only moves the model from "impossible" to "consistent but
silent at a query it is guaranteed to face."

This taxonomy is why the coupling theorem, Theorem 4.16, is stated separately from
the trilemma, Theorem 4.17, rather than folded into it. The coupling theorem
mentions no guarantee at all. It is convention-free, and the coupled point exists
under any threshold policy. The guarantee, inclusive or exclusive, only selects
which clause of the taxonomy applies to that fixed point. An inclusive guarantee
makes the system impossible. An exclusive guarantee makes it possible but silent.
Neither makes the coupled point go away, because the coupled point was constructed
before either guarantee was mentioned. A designer who reaches for the strict
inequality thinking it removes the problem has misread where the problem lives. The
problem lives in the geometry of the confidence and truth-distance fields on a
connected space, and the guarantee is a downstream policy about how to treat a
point that geometry has already fixed. This separation of the existence fact from
the policy is the most useful structural feature of the analytic engine, and it is
why the verified library keeps `hallucination_trilemma_strict` and
`hallucination_trilemma` as distinct theorems.

## The forced question is the analytic liar

The coupled point `q₀` of Theorem 4.16 is not an incidental byproduct. It is the
analytic twin of the liar index `a₀` of Proposition 1.10. In Chapter 1 the liar
was an index whose self-application equalled its own negation, `f a₀ a₀ = !(f a₀ a₀)`,
the exact place where a Boolean verdict system breaks. Here `q₀` is a question
whose confidence equals the threshold and whose answer sits on the boundary, the
exact place where a continuous calibrated model has no faithful answer to give.

Both witnesses are non-unique, and for the same reason. In Chapter 1, if the
diagonal behavior has two names, both are liars, and nothing selects a canonical
one. Here, if the confidence crosses `1/2` more than once, every crossing that
also lands on the boundary is a coupled point, and the intermediate value theorem
names none of them in particular. The witness is guaranteed to exist and left
unaddressed, in both engines. The non-uniqueness is not a defect of the proofs. It
is a faithful report that the obstruction is a region, not a single distinguished
point, which is exactly what the tube results of Chapter 5 make quantitative.

# A worked instance on the interval

It is worth carrying the abstract theorem down to a concrete space once, so the
moving parts are visible. Take `Q` to be the closed interval `[0, 1]`, which is
connected. Read `t ∈ [0, 1]` as a position along an interpolation from a question
the model answers truly at `t = 0` to a question it answers falsely at `t = 1`,
the path an experiment walks when it morphs a true statement into its negation.
Let the realized truth-distance be `F(t) = 2t - 1`, a continuous field that is
negative for `t < 1/2`, zero at `t = 1/2`, and positive for `t > 1/2`. This model
is covering, with `F(0) = -1 < 0` and `F(1) = 1 > 0`.

Lemma 4.14 applies at once. `F` is continuous, negative at `0`, positive at `1`,
so it has a zero, and here the zero is the single point `t = 1/2`. Now suppose the
confidence is calibrated. Strict calibration says the confidence is above `1/2`
exactly where `F` is negative and below `1/2` exactly where `F` is positive. A
continuous confidence meeting this must satisfy `(M t).2 > 1/2` for `t < 1/2` and
`(M t).2 < 1/2` for `t > 1/2`. By Lemma 4.15 the continuous confidence crosses
`1/2`, and it can only do so at `t = 1/2`, since that is the one place calibration
allows. So the coupled point is `t = 1/2`, with confidence exactly `1/2` and
truth-distance exactly `0`, precisely as Theorem 4.16 promises.

Now add faithfulness and watch it break. Faithfulness demands that wherever the
confidence is at least `1/2`, the truth-distance is strictly negative. At the
coupled point the confidence is exactly `1/2`, so faithfulness demands
`F(1/2) < 0`. But `F(1/2) = 0`. The model cannot be built. Any attempt to make the
confidence honest and to keep the safety promise fails at the one point the
interval forces into existence. Notice what happens if the confidence tries to
avoid `1/2` by jumping, say by being `0.6` for `t ≤ 1/2` and `0.4` for `t > 1/2`
with no value in between. That confidence is not continuous, and dropping
continuity is one of the named escapes, priced in the discrete section below. On a
genuinely continuous confidence over a connected interval, there is no jump, and
the coupled point is unavoidable.

The instance also shows what the exclusive-guarantee escape buys. Replace
faithfulness with the strict-antecedent form, triggering only when the confidence
is strictly above `1/2`. At the coupled point the confidence is exactly `1/2`, so
the guarantee does not trigger, and no contradiction arises. The model is
consistent. But it now owns the question `t = 1/2`, sitting on the truth boundary,
about which its guarantee is silent. The wall did not move. The guarantee just
stopped making a promise there.

# Quantitative shadows: approximate coupling and positive slack

Before leaving the coupling theorem, we state the graded version that the slack of
the model setup makes possible, because it is the bridge to Chapter 5 and it shows
that the exact result is the sharp corner of a robust phenomenon. The full metric
development, with tube radii and corridor widths, is the next chapter; here we
state the two results that already follow from connectedness plus separation with
slack, in prose, with the verified names attached.

**Theorem 4.17b (Approximate coupling).** _Let `Q` be connected, let the
confidence be continuous, and let the model be `ε`-covering, `(ε, γ)`-separating at
`τ`, and carry a threshold-inclusive guarantee. Then some question `q₀` has
`(M q₀).2 = τ` and `-ε ≤ δ(q₀, (M q₀).1) < 0`._

_Proof sketch._ The `ε`-coverage witnesses have truth-distance below `-ε` and above
`ε`, and separation turns these into confidence witnesses above `τ + γ` and below
`τ - γ`. The intermediate value theorem lands a `q₀` with confidence exactly `τ`.
Separation with slack no longer pins the truth-distance to zero. Instead it
confines it to the band where neither strict separation clause fires, which is
`|δ(q₀, (M q₀).1)| ≤ ε`. The threshold-inclusive guarantee applies at confidence
`τ`, forcing the truth-distance strictly negative. Combining, the coupled point has
truth-distance in `[-ε, 0)`. ∎

The verified statement is `two_slack_approx_coupling` in `HoF_12_Approximate`,
which carries the truth slack `ε` and the confidence margin `γ` as separate
parameters, exactly as the sketch above uses them.

This is `two_slack_approx_coupling`, and the exact coupling of Theorem 4.16 is the
`ε = 0` limit, recovered as `exact_from_approx`. The immediate corollary is the one
that matters for policy.

**Corollary 4.17c (Positive slack is mandatory).** _Under the hypotheses of
Theorem 4.17b with a threshold-inclusive guarantee, the truth slack `ε` cannot be
zero. Any feasible system carries `ε > 0`._

_Proof._ If `ε` were zero, Theorem 4.17b would place the coupled point at truth-
distance in `[0, 0)`, an empty range. So no coupled point could exist, but the
intermediate value theorem produced one. The only way out is `ε > 0`. ∎

This is `truth_slack_must_be_positive`. Read it as a budget. A system that wants to
keep a threshold-inclusive guarantee must keep a strictly positive margin of
correctness on the confident side, and the infimum of feasible slack is a
measurable width of the system's truth boundary. Under the guarantee, no question
with confidence between `τ` and `τ + γ` can sit exactly on the boundary, which is
`no_boundary_in_upper_band_two_slack`. These are the first quantities the analytic
engine produces that the diagonal cannot, and they are the whole reason Chapter 5
follows this one.

# Symmetry in place of coverage: the antipodal variant

Coverage is a mild hypothesis, but it can be removed entirely when the question
space carries a symmetry. The relevant symmetry is a fixed-point-free continuous
involution, the abstract shadow of the antipodal map `x ↦ -x` on a sphere. Read
it as semantic negation acting on the representation space: a map that sends a
question to its negation, that is its own inverse, and that never fixes a
question.

**Definition 4.18 (Antipodal action).** An _antipodal action_ on a topological
space `Q` is a map `σ : Q → Q` that is continuous, self-inverse
(`σ (σ q) = q` for all `q`), and fixed-point-free (`σ q ≠ q` for all `q`). A real-
valued function `g : Q → ℝ` is _odd_ under `σ` when `g (σ q) = -g q` for all `q`.

The verified structure is `AntipodalAction` and the predicate is `AntipodalOdd`,
both in `HoF_08_BorsukUlam`. The relevant instance is that layer normalization
places transformer states on a sphere-like shell, and semantic negation is a
candidate antipode, so `g` odd under `σ` idealizes a truth-distance that flips
sign under negation.

**Theorem 4.19 (Odd fields vanish, the one-dimensional Borsuk-Ulam analog).**
_Let `Q` be connected and `σ` an antipodal action. Any continuous `g : Q → ℝ` odd
under `σ` has a zero._

_Proof._ Pick any question `q`. If `g q = 0` we are done. Otherwise `g q` is
strictly positive or strictly negative. By oddness `g (σ q) = -g q`, which has the
opposite sign. So `g` takes both signs, at `q` and at `σ q`, and by the
intermediate value theorem on the connected space `Q` it has a zero somewhere
between them. ∎

This is `antipodal_odd_has_zero`. The point to see is that no coverage hypothesis
was assumed. Oddness supplies the two signs for free. A single question and its
negation image already straddle zero, because the field is negative at one and
positive at the other by the sign flip. Where coverage was an assumption that the
model is sometimes right and sometimes wrong, oddness derives that straddle from
the symmetry alone.

There is a pleasant inversion in this. Equivariance under a symmetry is usually a
design virtue, a property one builds into a network on purpose so that it treats a
question and its negation consistently. Here the same property is the engine of the
obstruction. A model that respects negation, so that negating a question negates the
truth-distance, is a model whose realized truth-distance is odd, and an odd
continuous field on a connected symmetric space must vanish. The better behaved the
symmetry, the more inescapable the wall. This is worth keeping in mind against the
intuition that more structure means more freedom. More structure here means less
room for the field to avoid zero.

**Theorem 4.20 (Antipodal trilemma).** _Let `Q` be connected with an antipodal
action `σ`, let the model be continuous and strictly calibrated at `1/2`, and let
the realized truth-distance be odd under `σ`. Then some question `q` has
`(M q).2 = 1/2` and `δ(q, (M q).1) = 0`._

_Proof._ By Theorem 4.19 the odd realized truth-distance has a zero `q`, so
`δ(q, (M q).1) = 0`. Strict calibration at `q` then pins the confidence: if the
confidence were above `1/2` the first biconditional would force the truth-distance
negative, and if below, the second would force it positive, both contradicting the
zero. So `(M q).2 = 1/2`. ∎

This is `antipodal_hallucination_trilemma`. Adding a faithfulness guarantee to its
hypotheses produces the same contradiction as Theorem 4.17, by the same final
step, and now with no coverage assumption anywhere. A negation-closed family of
questions meets the truth boundary by symmetry.

It is worth comparing the two engines' non-triviality demands directly, since that
is the only place they differ. The coverage engine assumes the model is sometimes
right and sometimes wrong, an assumption about the model's outputs. The antipodal
engine assumes the question space has a negation symmetry and the truth-distance
respects it, an assumption about the space and the field, not about the outputs. A
model could be antipodally symmetric and never happen to answer strictly falsely on
any single fixed question one inspects, and the antipodal engine would still force a
boundary point, because oddness guarantees the two signs across each orbit whether
or not any particular question realizes both. Conversely, a covering model on a
space with no useful symmetry falls to the coverage engine and is untouched by the
antipodal one. The two are genuinely different sufficient conditions for the same
conclusion, and a given system may satisfy either, both, or neither. When it
satisfies neither, the obstruction may simply be absent, which is the honest content
of the escape routes.

The antipodal engine is robust to the symmetry being only approximate, which
matters because real negation does not reflect truth directions exactly. If
oddness holds up to a defect `ε`, meaning `|g (σ q) + g q| ≤ ε` for every `q`,
then some question has `|g q| ≤ ε/2`, and at `ε = 0` this recovers exact
vanishing. The verified robust form is `approx_odd_near_zero`, and the concrete
instantiation on the unit sphere of `ℝ^d` for `d ≥ 2`, using Mathlib's
`isConnected_sphere`, is `sphere_odd_has_zero`. The near-boundary point degrades
linearly with the measured defect, which is what lets the experiments of the
companion paper report a nonzero defect and still see the predicted near-crossing.

## The sphere and layer normalization

The antipodal picture has a concrete home. Layer normalization rescales each
transformer state to a fixed norm, which places the states on a sphere-like shell,
up to a learned affine map. The unit sphere of `ℝ^d` for `d ≥ 2` is connected,
which is Mathlib's `isConnected_sphere`, and the antipodal map `x ↦ -x` is a
continuous free involution on it, the geometric antipode. If semantic negation acts
as this antipode, and the truth-distance is odd under it, then a continuous
truth-distance field on the sphere must vanish somewhere on the sphere. This is
`sphere_odd_has_zero`, proved by taking any point, comparing the field there with
its value at the antipode, and running the intermediate value theorem along the
connected sphere between them.

The dimension hypothesis `d ≥ 2` is where connectedness of the sphere comes from,
since the zero-dimensional sphere is two points and disconnected, the same
degeneracy that makes the diagonal engine, not this one, the right tool for a
two-point outcome set. For any representation dimension used in practice the sphere
is connected and the antipodal obstruction applies. The one honest caveat is that
exact oddness is an idealization. The companion paper measures the oddness defect
and finds it nonzero but small, smallest for the strongest model, and
`approx_odd_near_zero` is exactly the theorem that keeps a near-boundary point in
existence under that measured defect. The idealization degrades gracefully rather
than collapsing.

# The discrete core: no topology once a boundary question exists

The topology in the argument does exactly one job. It manufactures a boundary
question, a `q₀` with `δ(q₀, (M q₀).1) = 0`. Everything after that is arithmetic.
This section isolates the arithmetic and shows that once a boundary question is
handed to us, no topology, no continuity, no connectedness, and no finiteness are
needed to finish. The verified home of this observation is `HoF_10_PureDiscrete`.

The reason the discrete core matters is that token spaces are finite and one may
object that connectedness is doing illegitimate work. The discrete analysis prices
the objection exactly. Without topology we must assume the boundary witness rather
than derive it. That is the entire cost. The contradiction machinery is untouched.

It is worth dwelling on what "pricing an objection" means, because it is the honest
way to handle an idealization. A theorem with a strong hypothesis invites the reader
to reject the hypothesis and walk away. The disciplined response is not to defend
the hypothesis to the death but to show exactly how much of the conclusion survives
without it. Connectedness is the idealization here. It is a good model of an ambient
representation space over which probes and steering vectors are deployed at
arbitrary interpolated points, and a poor model of a token-driven reachable set,
which may be scattered. The discrete core is what remains when connectedness is
dropped entirely. The answer is that the whole contradiction remains, and the only
thing lost is the free construction of the boundary question. In the continuum the
boundary question is a theorem. In the discrete world it is a hypothesis. Nothing
else moves. This is a precise accounting, and it is more useful than either
insisting the space is connected or conceding that finiteness ruins everything.

We can state and check the core in self-contained core Lean, over the integers
with the threshold shifted to `0` in place of `1/2`, so no real numbers or
libraries are needed. First the flip, the discrete shadow of the complement map,
proved by the same finite check that settles the Boolean flip in Chapter 1.

```lean
theorem c4_flip_no_fixed_point : ∀ b : Bool, (!b) ≠ b := by decide
```

Next the pinning-and-clash core itself. Model the confidence and the truth-
distance as two integers, with calibration as the two biconditionals around the
threshold `0`, and faithfulness as the implication that non-negative confidence
forces a strictly negative truth-distance. The claim is that a boundary question,
here a truth-distance of exactly `0`, makes the conjunction contradictory. The
proof is pure arithmetic: calibration pins the confidence to `0`, faithfulness
then demands the truth-distance be strictly negative, and that clashes with the
boundary value.

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

This is the integer transcription of `boundary_question_impossible`. Read the
proof against Theorem 4.17. The two `have` blocks are calibration pinning the
confidence to the threshold, exactly the step Theorem 4.16 performed with the
intermediate value theorem replaced by the assumed boundary value. The last two
lines are faithfulness demanding a strict inequality and the sign clash. No
topology appears anywhere. The result {lean}`c4_boundary_question_impossible` is
the trapped logical core, and both the continuous trilemma and the antipodal
trilemma factor through it.

The remaining question is how, in a discrete world, one would ever get a boundary
value to feed the core. Along a finite path of questions the truth-distance does
not have to hit zero. It can jump across it between adjacent steps. That is the
discrete intermediate value theorem, and it produces a straddling pair rather than
a boundary state. The following self-contained result is the discrete sign change,
the honest discrete replacement for the crossing.

```lean
theorem c4_discrete_sign_change (g : Nat → Int) :
    ∀ n, g 0 < 0 → 0 ≤ g n → ∃ i, i < n ∧ g i < 0 ∧ 0 ≤ g (i + 1) := by
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

The statement says that a discrete field negative at the start and non-negative at
the end has an adjacent pair where it is still negative and has just become non-
negative. It never claims a step where the field is exactly zero. That gap is the
whole difference between the discrete and continuous settings, and it is priced
precisely: the continuum upgrades the adjacent straddle into an exact witness, and
the discrete world supplies only the straddle. The verified counterpart is
`discrete_sign_change`. The proof here is a clean induction: the base case is a
contradiction, since a field cannot be both negative and non-negative at the same
index, and the step either recurses on the shorter prefix or, when the field is
already negative at the last interior index, returns that index as the crossing.

Two consequences of the discrete core deserve stating in prose, both verified in
`HoF_10_PureDiscrete`. First, the three-sided version: a model that is faithful
and strictly calibrated and that additionally has witnesses for strictly correct,
exactly boundary, and strictly wrong answers is impossible, with no topological
hypothesis, because the assumed boundary witness feeds the core directly. This is
`discrete_hallucination_trilemma`, and it trades the topological hypothesis of
connectedness for the stronger coverage hypothesis of a supplied boundary point.
Second, and more revealing, faithfulness is _equivalent_ to boundary-freeness
under calibration: a strictly calibrated model is faithful if and only if it has
no boundary questions at all. This is `faithful_iff_boundary_free`, and it says
the obstruction is not incidental. Faithfulness just is the condition of having no
questions on the wall. The continuous engine and the antipodal engine both work by
manufacturing precisely the thing faithfulness forbids.

## Adding randomness

A model can be stochastic, sampling its answer and its confidence rather than
computing them deterministically. One might hope randomness dodges the obstruction,
since a sampled confidence need not equal `1/2` on any single draw. It does not
dodge it. There are two ways to see this, and both are verified.

The first works on expected fields. If the confidence and the truth-distance are
averaged over the sampling, the averages are continuous fields on the connected
question space whenever the underlying fields are, and the coupling theorem applies
to them verbatim. The conclusion is a question where the expected confidence is
`1/2` and the expected truth-distance is `0`, which is `stochastic_coupling_expected`.
Averaging is a continuous operation, so the wall survives it.

The second converts an expectation statement into a statement about samples, and it
is the one place in the whole development where the theory derives outright
falsehood rather than uncertainty. Let the sampling live on a probability space,
let the truth-distance have mean zero, and suppose sample-faithfulness holds almost
everywhere, meaning that whenever the sampled confidence is at least `1/2` the
sampled truth-distance is strictly negative. Suppose also that the confidence is at
least `1/2` with positive probability. Then the truth-distance is strictly positive
with positive probability. In model terms, a system that is faithful on almost
every sample and confident with positive probability at a coupled point must emit
strictly false answers with positive probability. This is `stochastic_dichotomy`,
and its proof is a clean averaging argument.

_Proof sketch of the dichotomy._ Suppose the truth-distance were almost never
positive. On the confident event, which has positive probability, sample-
faithfulness makes it strictly negative, so it is strictly negative on a set of
positive measure and non-positive everywhere else. A quantity that is non-positive
almost everywhere and strictly negative on a set of positive measure has strictly
negative mean. That contradicts the mean-zero hypothesis. So the truth-distance is
strictly positive with positive probability. ∎

Randomization therefore spreads the boundary across samples instead of removing it.
The deterministic theorems yield an ambiguous point; the stochastic dichotomy
yields, from the same premises plus mean-zero truth, positive-probability error.
The wall is either a point you must pass through or a positive-probability event you
must incur, and no amount of sampling escapes both.

# Where the two engines meet

We can now make the analogy of the primer exact. The claim is that the diagonal of
Chapter 1 and the intermediate value theorem of this chapter locate the _same_
boundary object, and that the Boolean flip and the real complement map are two
descriptions of the same wall. This is not a loose resemblance. It is recorded as
a theorem in `Foundation.F_04`, and we reconstruct its content here.

Start with the flip. In Chapter 1 the engine needed an outcome flip with no fixed
point. For Booleans that flip is negation, and {lean}`bool_not_fpf` is the fact
that it has none, which is what turns {lean}`lawvere` into {lean}`cantor` and
through it into every diagonal impossibility. For real confidences the natural
flip is the _complement controller_ `y ↦ 1 - y`. It is not fixed-point-free. It
has exactly one fixed point, and that fixed point is the threshold `1/2`, because
`1 - y = y` holds if and only if `y = 1/2`. This is `half_complement_fixed_point`,
and its off-threshold form, that `y ↦ 1 - y` fixes nothing away from `1/2`, is
`complement_no_fp_off_half`.

The single fixed point is the entire difference between the two engines, and it is
the reason they reach the same place. The Boolean flip has no fixed point, so
Lawvere's theorem, which always produces a fixed point of the flip, produces a
contradiction. The real complement has one fixed point, at `1/2`, so Lawvere's
theorem, run with the complement controller, produces not a contradiction but a
point: a diagonal question where the confidence equals `1/2`. Feed a surjective
self-prediction map `s : A → A → ℝ` to the diagonal, apply the complement
controller, and the naming equation gives `s a a = 1 - s a a`, which solves to
`s a a = 1/2`. This is `calibration_diagonal_hits_half`, and its impossibility
form, that a surjective system cannot avoid `1/2` on its diagonal, is
`calibration_no_strict_avoidance`.

Compare the two routes to `1/2`. The intermediate value theorem reaches it by
connectedness: the confidence is below and above the threshold, so it crosses.
The diagonal reaches it by self-reference: the confidence names a behavior that
complements its own diagonal value, so it equals its own complement, which is
`1/2`. One argument bisects a connected interval, the other evaluates a naming
equation. The output is identical, the value `1/2` at a distinguished question,
and from there both proofs run the same calibration-versus-faithfulness clash. The
verified statement that the whole trilemma follows from surjectivity alone, with
no topology, is `hallucination_via_lawvere`, whose proof is Theorem 4.17's final
step attached to `calibration_diagonal_hits_half` in place of Theorem 4.16.

So the correspondence table of the primer is now a list of theorems. Self-
reference and connectedness are two ways to trap a value. The Boolean negation
`(!·)` and the real complement `y ↦ 1 - y` are the two flips, one with no fixed
point and one with a single fixed point at the threshold. The liar index and the
boundary question are the same distinguished point under two constructions. The
diagonal impossibility {lean}`no_reflective_verdict` of Chapter 1 and the analytic
`hallucination_trilemma` of this chapter are, in the precise sense
`Foundation.F_04` records, two spellings of one fact. The topology in
`HoF_07_TrilemmaCore` is a convenient way to enforce surjectivity onto a connected
slice of the reals; any other route to that value, including the universality-of-
in-context-learning route, yields the very same boundary point and the very same
contradiction.

It is worth being precise about what is shared and what is not. What is shared is
the boundary object and the final clash. What differs is the hypothesis that
manufactures the object. The diagonal needs a system that names its own behaviors,
`no_universal` read as a demand rather than a conclusion. The intermediate value
theorem needs a connected domain and continuous fields. Neither hypothesis implies
the other. A finite discrete model can be universal in the diagonal sense and
carry no topology at all, and a smooth model on a manifold can be continuous and
connected while naming almost none of its own behaviors. The two engines cover
disjoint failure modes and agree wherever both apply, which is exactly what one
wants from two proofs of one theorem.

There is a categorical way to say the shared part that makes the unification more
than a coincidence of two calculations. Recall from Remark 1.5 that Lawvere's
theorem holds in its cleanest form for a _section_, a right inverse
`s : (A → Y) → A` of evaluation, and that this is the form true verbatim in any
cartesian closed category. The complement controller `y ↦ 1 - y` is an endomap of
the reals with a single fixed point, and Lawvere's theorem applied to a section of
a real-valued self-prediction map delivers that fixed point on the diagonal. The
intermediate value theorem is not a categorical statement, but it delivers the same
value, and the reason is that both are extracting the fixed point of the same
controller. The topology in `HoF_07_TrilemmaCore` is one way to guarantee that the
confidence sweeps through a connected slice of the reals wide enough to contain the
controller's fixed point. Surjectivity of the self-prediction map is another. Once
either guarantee is in hand, the fixed point of `y ↦ 1 - y` is reachable, and it is
`1/2`.

The whole unification is packaged in the companion library at two levels. The
statement that the topological and categorical proofs are the same theorem is
`hallucination_unification_documentation` and its surrounding lemmas in
`Foundation.F_04`. The statement that the several trilemmata of Chapter 3, the
hallucination form, the defense form, and the truth-boundary coupling, are
instances of one master result is `trilemmata_unified`, with the bundled statement
`hallucination_master_theorem`. The reader who wants to see the diagonal and the
intermediate value theorem land on the identical object at the level of kernel-
checked terms should read `F_04` first, then `F_13_UnifiedTrilemmata`. The prose
here is a guide to those files, not a substitute for them.

One geometric remark closes the meeting point. When the truth-distance is a linear
probe, the boundary is not just a level set but an affine hyperplane of codimension
one, a translate of the probe's kernel, by rank-nullity. This is
`linear_probe_boundary_coset` and `linear_probe_boundary_dim`. For a differentiable
nonlinear probe the boundary is a hyperplane to first order at every regular point,
with the tangent hyperplane being the kernel of the derivative, verified as
`nonlinear_boundary_tangent` and `tangent_hyperplane_dim`, and every regular point
is itself a sign crossing that generates local coverage for free,
`regular_point_is_crossing`. The boundary object the two engines share is thus not
an abstract point in a general space. In the linear case it is a flat wall of one
dimension less than the representation space, and the coupled point is a point on
that wall carrying threshold confidence. The full geometry is Chapter 5's subject,
but it is the same wall both engines have been walking toward.

# Where the two engines diverge

The engines agree on the existence of the boundary object. They diverge sharply on
what else they can tell you about it, and the divergence is the reason both
chapters exist.

The diagonal gives a witness and nothing quantitative. It does not say how many
liar indices there are, how hard `a₀` is to find, or what it would cost a search
to reach one. It cannot, because it uses no metric. Its only input is a naming
equation, and a naming equation has no notion of distance, width, or margin. This
is the content of Remark 1.14, and it is a real limit, not a temporary gap. The
diagonal is silent on geometry because geometry is not among its hypotheses.

The intermediate value theorem, on its own, is equally silent, as Remark 4.8
noted. Bare connectedness gives existence and no location. The difference is that
the analytic engine can be fed more. Add a distance to the question space and
require the confidence and truth-distance to be Lipschitz, and the bare crossing
becomes a quantitative object. The decisive regions, where the confidence is
bounded away from `1/2` on either side, must be held apart by a distance
controlled by the Lipschitz constant and the margin. The coupled point sits at the
center of a tube of near-ambiguous questions whose radius is set by the same
constants. Truth-side slack must be strictly positive, so exact-zero slack is
infeasible, and its infimum is a measurable width of the boundary. These are the
verified results `confidence_gap_width`, `ambiguity_tube`, `truth_margin_tube`,
`two_slack_approx_coupling`, and `truth_slack_must_be_positive`, and they are the
subject of Chapter 5.

None of that is available to the diagonal, and none of it is available to the
intermediate value theorem without the extra metric hypotheses. The right way to
hold the two engines together is this. Use the diagonal when the system names
itself and you want the cleanest possible existence proof with the smallest
possible trust story, a `decide` on a finite flip and three lines of term-mode.
Use the intermediate value theorem when the system lives on a connected space, and
then, if you also have a metric, keep going into Chapter 5 and read off the widths.
Both routes reach the boundary. Only the second route measures it.

There is also a difference in what each engine says about how to escape. The
diagonal is escaped by breaking universality, by ensuring the system cannot name
the diagonal behavior. That is a statement about the expressive power of the naming,
and it is often hard to arrange without crippling the system, since the whole point
of a general system is to handle arbitrary inputs. The analytic engine is escaped
by breaking connectedness, coverage, continuity, or exact separation, and each of
these is a concrete design lever. Abstention on an open region disconnects the
space. Restricting to retrieval-grounded content that is never strictly false
breaks coverage. Hard decoding breaks continuity, at the price the discrete section
computed. Band separation with positive slack replaces exact separation, at the
price of a positive truth-boundary width. The analytic engine, because it names its
hypotheses as geometric and quantitative conditions, hands the designer a menu of
priced escapes. The diagonal offers essentially one, and it is expensive. This is a
practical reason to prefer the analytic engine wherever a system carries geometry,
even though the two prove the same existence fact.

# The engine in one page

It helps to have the whole argument compressed once, stripped of the applied
readings, so the logical skeleton is visible. The analytic engine is four moves.

The first move is a continuity fact. The realized truth-distance and the confidence
are continuous real-valued functions on the question space, because they are built
from continuous pieces by composition and pairing. Continuity is what lets the next
move happen.

The second move is the intermediate value theorem. On a connected space a
continuous real field that takes a negative value and a positive value takes the
value zero, and one that takes a value below a threshold and a value above it takes
the threshold. This is the only analytic input, and it is Theorem 4.7, verified as
`IsPreconnected.intermediate_value₂`.

The third move is coupling. Coverage gives the truth-distance both signs, and
calibration converts these into confidence values on both sides of the threshold,
so the intermediate value theorem lands a question at the threshold, and calibration
read backward pins the truth-distance to zero there. The output is a single
question that is exactly ambiguous in confidence and exactly on the boundary in
truth. This is Theorem 4.16, verified as `hallucination_trilemma_strict`.

The fourth move is the clash. Faithfulness demands the truth-distance be strictly
negative wherever the confidence reaches the threshold, and the coupled point has
confidence at the threshold and truth-distance zero. Strictly negative and zero
cannot both hold. This is Theorem 4.17, verified as `hallucination_trilemma`.

Every variant in the chapter is a substitution into this skeleton. The antipodal
variant replaces coverage in the third move with a symmetry that supplies both
signs for free. The discrete core keeps only the third and fourth moves and assumes
the boundary question the first two moves would have produced. The stochastic
variant runs the skeleton on expected fields, or converts it into a positive-
probability error by averaging. The diagonal engine of Chapter 1 replaces the
second move, the intermediate value theorem, with a naming equation that reaches the
same threshold value. The skeleton does not change. What changes is which hypothesis
supplies the coupled point, and the fourth move is the same clash every time.

# Historical and bibliographic notes

The intermediate value theorem is Bolzano's, and the modern formulation as
preservation of connectedness under continuous maps is standard in any point-set
topology text. The reading of it as an impossibility engine for learning systems
is recent, and the machine-checked development these notes follow is the companion
`HallucinationProofs` library, with the topological core in `HoF_03`, `HoF_05`,
and `HoF_07`, the antipodal variant in `HoF_08`, and the discrete core in
`HoF_10`. The unification of the analytic and diagonal proofs is `Foundation.F_04`,
which records that both extract the same `1/2` point from a surjectivity-style
hypothesis and then run the same clash. The one-dimensional Borsuk-Ulam analog is
a scalar relative of the full antipodal theorem of Borsuk; the sphere
instantiation uses Mathlib's connectedness of spheres. The companion paper "Truth
Has a Boundary" states the coupling theorem for representation geometry, verifies
every result in Lean against Mathlib with no sorry placeholders, and reports the
predicted coupling in five small language models. The framing there, that exact
threshold uncertainty is a topological property of representation space, is the
applied face of Theorem 4.16.

The statistical inevitability results in the literature run on a different track and
reach a different conclusion, and the contrast sharpens what this chapter does. Those
results argue that a calibrated model must hallucinate on facts it saw rarely, or
that hallucination is undecidable in a computability sense, and they conclude that
confident falsehood is unavoidable in the aggregate. The engine here is topological,
lives in representation geometry, localizes its conclusion at a specific boundary
question, and is more modest in what it asserts, since the deterministic theorems
yield uncertainty at the coupled point rather than confident error. Only the
stochastic dichotomy derives falsehood, and it needs the extra mean-zero hypothesis
to do it. The two lines of work are complementary. One counts errors; this one
locates a wall.

The verified library is organized so that the logical dependencies match the
chapter's narrative. `HoF_03_BoundaryCrossing` holds the raw intermediate value
theorem applications, the boundary and confidence crossings, and the closedness and
path-crossing facts. `HoF_05_Coverage` isolates the coverage condition in its
several strengths and proves the coverage-to-boundary workhorse. `HoF_07_TrilemmaCore`
assembles the coupling theorem and the trilemma from these pieces. `HoF_08_BorsukUlam`
develops the antipodal variant, its robust and sphere forms, and prints an axiom
audit. `HoF_10_PureDiscrete` extracts the topology-free core and proves the
factorization of the continuous result through it. `Foundation.F_04` and
`F_13_UnifiedTrilemmata` sit above all of these and record the unification with the
diagonal engine. A reader who wants to trace a single theorem from prose to kernel
can follow this map, and every result carries a name that appears in exactly one of
these files. The reduction of the main theorems to the three standard kernel axioms
is checked in the final verification file, so the trust story is not a claim in the
prose but a machine-audited fact.

# Exercises

**Exercise 4.1.** Prove directly from Definition 4.3 that a two-point discrete
space is disconnected, and that the one-point space is connected. Conclude that
`Bool` is disconnected and explain, in one sentence, why the analytic engine
cannot run on it.

**Exercise 4.2.** Show that the continuous image of a connected space is
connected, and deduce that continuity plus connectedness of the domain rules out
a continuous surjection from a connected space onto a two-point discrete space.
Relate this to Lemma 4.15: what would a confidence map with no crossing say about
the connectedness of `Q`?

**Exercise 4.3.** Fill in the omitted lines of Proposition 4.6. Given an interval
`S ⊆ ℝ` and a putative separation by open `U` and `V`, take a point in `S ∩ U` and
a point in `S ∩ V`, form the supremum of `S ∩ U` below the second point, and
derive a contradiction with the openness of both pieces.

**Exercise 4.4.** State and prove the two-function form of the intermediate value
theorem used in the library: for continuous `f, g` on a connected `X` with
`f a ≤ g a` and `g b ≤ f b`, there is an `x` with `f x = g x`. Derive Theorem 4.7
as the special case `g` constant.

**Exercise 4.5.** In the proof of Theorem 4.16, exactly one direction of each
calibration biconditional is used going forward and exactly one going backward.
Identify which, and show that a one-way calibration, only the forward directions,
is not enough to pin the truth-distance to zero at the crossing.

**Exercise 4.6.** Show that Theorem 4.17 fails if faithfulness is weakened to the
inclusive-boundary form `(M q).2 ≥ 1/2 → δ(q, (M q).1) ≤ 0`. Construct, in prose,
a model on a connected space meeting all three weakened conditions, and locate its
coupled point. This is the exclusive-guarantee escape of the policy taxonomy.

**Exercise 4.7.** Reprove {lean}`c4_boundary_question_impossible` with the
threshold at an arbitrary integer `τ` in place of `0`, keeping the proof in core
Lean. Then explain in one paragraph why the choice of threshold is a convention
that never affects the existence of the coupled point.

**Exercise 4.8.** The proof of {lean}`c4_discrete_sign_change` inducts on the
right endpoint. Rewrite it to induct on a bound and return the _least_ crossing
index, and argue that the continuous intermediate value theorem has no analogous
canonical choice. Connect this to the non-uniqueness discussion after
Theorem 4.16.

**Exercise 4.9.** Prove that the truth boundary `{q | δ(q, (M q).1) = 0}` is
closed whenever `δ` and the answer map are continuous, using only that a singleton
in `ℝ` is closed and that preimages of closed sets under continuous maps are
closed. This is `model_truth_boundary_isClosed`; write the argument yourself.

**Exercise 4.10.** In the antipodal setting, show that an odd continuous field on
a connected space with a free involution has at least two zeros unless it is
identically zero on the orbit of some point. What does the second zero correspond
to in the model reading?

**Exercise 4.11.** Prove the approximate-oddness bound in prose: if
`|g (σ q) + g q| ≤ ε` for all `q` and `g` is continuous on a connected space, then
some `q` has `|g q| ≤ ε/2`. Show the bound is tight by exhibiting a field that
meets it with equality.

**Exercise 4.12.** Verify the claim of Section "Where the two engines meet" by
hand: given a surjective `s : A → A → ℝ`, use the diagonal with the controller
`y ↦ 1 - y` to produce an `a` with `s a a = 1/2`. Identify precisely which step
replaces the intermediate value theorem, and which step is shared with
Theorem 4.16.

**Exercise 4.13.** The complement controller `y ↦ 1 - y` has a fixed point while
the Boolean flip `(!·)` has none. Explain why this difference makes Lawvere's
theorem yield a contradiction in the Boolean case and a distinguished point in the
real case, and state the general principle: what does the fixed-point set of the
controller become in each reading?

**Exercise 4.14.** Give an example of a system that satisfies the diagonal
hypothesis (universality) but not the analytic one (connectedness with continuous
fields), and an example that satisfies the analytic hypothesis but not the
diagonal one. Conclude that neither engine subsumes the other.

**Exercise 4.15.** (Harder.) The discrete core needs a boundary question handed to
it, while the continuous engine derives one. Formulate a hypothesis on a finite
question space, weaker than connectedness, under which a boundary question is still
forced. Compare it to three-sided coverage and to the existence of an odd field
under a free involution.

**Exercise 4.16.** (Harder.) Suppose the confidence map is continuous but the
answer map is not. Which of Lemma 4.14, Lemma 4.15, and Theorem 4.16 survive, and
which fail? Rework the hypotheses of Theorem 4.16 to use the smallest continuity
assumptions that still deliver the coupled point.

**Exercise 4.17.** (Open-ended.) Chapter 5 adds a metric and extracts the width of
the ambiguity tube. Before reading it, conjecture how the tube radius should scale
with the Lipschitz constant of the confidence map and the confidence margin, and
sketch which step of Theorem 4.16 the metric refines. Compare your conjecture to
`ambiguity_tube` once you reach it.

**Exercise 4.18.** (Open-ended.) The antipodal variant removes coverage using a
symmetry. Speculate on what a system would need to satisfy both the diagonal
hypothesis and the antipodal hypothesis at once, and describe the boundary object
in that combined setting. Chapter 8 returns to this for J-space.

**Exercise 4.19.** Verify the multi-turn claim in detail. Assuming `Q` is
connected, prove that `Q × Q` is connected by the slice argument sketched in the
primer, and conclude by induction that `Q^T` is connected. Then state the coupling
theorem for a two-turn model `M : Q × Q → A × ℝ` and observe that its proof is
Theorem 4.16 with `Q^2` in place of `Q`. Where, if anywhere, did the second turn
enter the argument?

**Exercise 4.20.** Prove the stochastic dichotomy from the sketch in the discrete
section. Let `d` be integrable with mean zero on a probability space, suppose
`c ≥ 1/2` implies `d < 0` almost everywhere, and suppose `c ≥ 1/2` has positive
probability. Show `d > 0` has positive probability. (Hint: assume not, split the
integral of `d` over the confident and non-confident events, and derive a strictly
negative mean.) Then explain why this is the only result in the chapter that
concludes with confident error rather than uncertainty.

**Exercise 4.21.** (Harder.) The exclusive-guarantee escape leaves a system
consistent but silent at the coupled point. Design, in prose, a reporting policy
that at least makes the silence visible, for instance by having the system flag any
query whose confidence lands within a small band of the threshold. Using
Theorem 4.17b and the corollary on positive slack, argue that such a band cannot be
made empty, so the flag can never be guaranteed never to fire.
