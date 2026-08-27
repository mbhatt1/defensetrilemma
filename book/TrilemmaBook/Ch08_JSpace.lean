import VersoManual
import TrilemmaBook.Ch01_Diagonal
-- The structural facts about J-space are statements about a linear image, so
-- this chapter elaborates against `Mathlib` as well as core Lean.
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "J-Space, and Why It Does Not Escape" =>

Everything in this book so far has been stated about a system's _outputs_. A
verdict `v p q`, a safety score, a truth probe: each reads the end of a
computation and returns a commitment. There is a natural objection to reading
only the ends. A model's output is a summary, and summaries throw away structure.
The interesting part of a large network is in the middle, in the activations that
carry a half-formed answer before the answer is spoken. A probe that reads the
middle, the objection goes, is a different kind of object from a probe that reads
the end, and the impossibility theorems of the earlier chapters, which were
proved against output verdicts, might simply not reach it.

This chapter takes that objection in its strongest current form. The form is the
_J-space_ construction, an interpretability method from 2026 that recovers a
transformer's private mid-process representation from the derivative of its
computation rather than from the activations themselves. J-space is the most
serious recent candidate for a place where you could read a model's mind, and if
any internal representation escaped the diagonal, this is the one that should.
The result of the chapter is that it does not. Both engines of the book, the
diagonal of Chapter 1 and the intermediate value theorem of Chapter 4, reach
J-space, and they reach it for reasons that are not accidents of how J-space
happens to be built but consequences of what it is. A probe that reads the middle
gets more resolution than a probe that reads the end. It does not get immunity.

The plan is as follows. First we set down the construction precisely, with
numbered definitions of the transport map, the J-lens, J-space, and the local
J-coordinates, so that later claims have something exact to attach to. Then we
isolate the two structural facts that do all the work: J-space is a Jacobian
image and therefore a linear, connected tangent space, and the readout is
computed from the very system it reports on. The first fact hands J-space to the
analytic engine, the second to the diagonal engine. We run both engines, keep the
live theorems `jspace_factoring` and `jspace_liar` at the center, and
build the surrounding results in core Lean around them. We then show that the two
engines are not merely both applicable but are two readings of one equation, with
the Jacobian playing the role of the linearization and the liar activation
playing the role of the fixed point. We close with what this means for
interpretability in practice, and with a careful statement of what the chapter
does not claim.

# What J-space is

Fix a trained transformer. Write `h_{ℓ,t}` for the residual-stream activation at
layer `ℓ` and token position `t`, and write `h_final` for the final-layer
activation that the unembedding reads to produce logits. The ordinary
interpretability picture, the one behind sparse autoencoders and the logit lens,
reads structure off the activations `h_{ℓ,t}` directly: it looks for directions
in activation space and treats features as sparse combinations of those
directions. J-space reads structure off the _sensitivity_ of the computation
instead. It asks not what the activation is at a point but how the rest of the
computation would move if that activation moved.

The motivation is that the derivative carries information the point does not. Two
prompts can drive the model to nearly the same activation at some middle layer
and still be processed in completely different ways downstream, because what a
network _does_ at a point is a property of the local behavior of the map there,
not of the coordinates of the point. Reading the derivative surfaces the
mid-process computation, the leaning toward a future token that has not yet been
written into any residual-stream direction. That is the empirical bet of the
construction, and it is a bet about representation, not about limits.

It helps to place J-space among the interpretability methods it grew out of. The
logit lens applies the unembedding `W_U` directly to a middle-layer activation and
asks what token that activation would predict if the layers above it were skipped.
It is cheap and often revealing, but it reads the activation as if it were already
a final state, and so it sees the model's current guess rather than the
computation still to come. Sparse autoencoders go the other way: they fit an
overcomplete dictionary to the activations themselves and decompose each
activation into a sparse sum of learned features. That recovers structure the raw
coordinates hide, but it is still structure of the point, of where the model is,
not of what it is about to do. J-space sits at a third position. It reads neither
the activation nor a learned dictionary over activations, but the linear map that
says how the activation influences the future of the computation. The dictionary
of J-coordinates in Definition 8.4 is a sparse dictionary again, but it is fit
over the transported directions, over columns of `Jℓ`, not over activations. The
family resemblance to sparse autoencoders is real, and it is worth keeping in view,
because it means the diagonal and analytic arguments of this chapter are not
special to J-space. They apply to any of these methods the moment the method is
asked to be a total exact verdict over a self-describing query space.

The averaging in Definition 8.1 is not incidental bookkeeping. Restricting the
expectation to future positions `t' ≥ t` is what makes the transport map read a
_leaning_, a commitment the model is building toward but has not yet emitted. A
derivative that also averaged over past positions would mix the model's memory of
what it has already said into its account of what it is about to say, and the
readout would lose the predictive, forward-looking character that motivates the
whole construction. The causal restriction to the future is the technical device
that turns a generic sensitivity matrix into a workspace readout. This matters for
the arguments below only through its consequences, that the readout is a linear
functional of the model's own map, but it is worth understanding why the
construction is built the way it is before we start extracting what it cannot do.

**Definition 8.1 (Transport map).** Let the model define, for each middle layer
`ℓ`, the map from the layer-`ℓ` activation at position `t` to the final-layer
activation at a later position `t' ≥ t`. The _Jacobian transport map_ at layer
`ℓ` is the expected derivative of the later activation with respect to the
earlier one,

```
Jℓ = E[ ∂ h_{final, t'} / ∂ h_{ℓ, t} ],
```

where the expectation averages over positions `t' ≥ t` and over a reference
distribution of inputs. Concretely `Jℓ` is a matrix: a linear map from the
activation space at layer `ℓ` into the final-layer activation space. It records,
on average, how a small push to the layer-`ℓ` state at the current position
propagates forward to the model's later commitments.

Two things about Definition 8.1 will matter more than the details of the average.
`Jℓ` is a Jacobian, so it is a derivative, so it is linear. And `Jℓ` is assembled
entirely out of the model's own weights and its own activations, since a Jacobian
of the model's forward map is a functional of that map. Both points return below
with force.

**Definition 8.2 (J-lens readout).** The _J-lens_ is the readout obtained by
sending an activation through the transport map, normalizing, and unembedding:

```
lens(h) = softmax( W_U · norm( Jℓ h ) ),
```

where `W_U` is the model's unembedding matrix and `norm` is the model's
final-layer normalization. The J-lens returns a distribution over the vocabulary.
Read it as the model's silent guess about what it is leaning toward emitting at
future positions, given the current mid-layer state `h`. Where the ordinary logit
lens applies `W_U` to the activation itself, the J-lens applies it to the
transported activation `Jℓ h`, which is what makes it a readout of mid-process
sensitivity rather than of the surface state.

The J-lens returns a distribution over the vocabulary, but the impossibility
results of this book are stated about Boolean verdicts, so we need the step that
turns a distribution into a commitment. That step is already implicit in how the
readout is used.

**Definition 8.2b (Truth-workspace reading).** Fix a decodable proposition
associated with a query `q`, for instance "the answer to `q` is yes," and a token
or set of tokens that expresses it. The _truth-workspace verdict_ of an
activation `h` on query `q` is `true` when the J-lens distribution `lens(h)` puts
more mass on the affirming tokens than on the denying ones, and `false`
otherwise. Writing `read(J-point)(q)` for this thresholded reading gives a map of
the shape `J → Q → Bool`, which is the object the diagonal argument takes as
input. Nothing in the argument depends on the particular thresholding rule; it
depends only on the fact that a distribution over tokens is eventually resolved
into a commitment, which is what any use of the readout as a truth signal must do.

This is where the two engines part company at the level of the readout, and it is
worth marking the fork now. The analytic engine of Chapter 4 works on the
distribution _before_ it is thresholded, on the continuous score, and its whole
force comes from the score varying continuously. The diagonal engine works _after_
thresholding, on the Boolean commitment, and it does not care how the commitment
was reached. The same J-lens feeds both, which is the first sign that a J-space
probe will not slip between the two arguments.

**Definition 8.3 (J-space).** _J-space_ is the image of the transport map,

```
J = { Jℓ h : h ∈ activation space } = im(Jℓ),
```

the subspace of the final-layer activation space spanned by the transported
directions. Because `Jℓ` is linear, `J` is a linear subspace. Empirically it is
small, a few dozen effective dimensions, well under a tenth of the activity of
the layers it summarizes, and yet it is read and written far out of proportion to
its size. Ablating it, projecting activations onto its orthogonal complement,
collapses the model's multi-step reasoning while leaving single-step lookups
largely intact. That combination, tiny yet load-bearing, is why the construction
was proposed as a candidate global workspace: a low-dimensional channel through
which the model routes the intermediate results of chained computation.

**Definition 8.4 (J-coordinates).** For a particular activation `h`, its
_J-space component_ is the projection of `Jℓ h` onto `J`, and this component is
approximated as a sparse nonnegative mixture of a fixed dictionary of Jacobian
directions `d_1, …, d_m`,

```
proj_J(Jℓ h) ≈ Σ_i w_i(h) · d_i,   w_i(h) ≥ 0,  most w_i(h) = 0.
```

The mixture weights `w_i(h)` are the _local J-coordinates_ of `h`. They are the
interpretable handle: each active direction `d_i` names a mid-process concept, and
the weight `w_i(h)` says how strongly the current state is leaning on that
concept. Steering the model amounts to editing these coordinates and pushing the
edited component back into the residual stream.

We can make the coordinate object concrete enough to point a theorem at. In core
Lean, with no vector space in scope, we model a J-coordinate as the finite record
of which directions are active and with what nonnegative weight, using natural
numbers as a stand-in for the nonnegative reals.

```lean
/-- A local J-coordinate: a finite sparse nonnegative mixture of dictionary
    directions drawn from `Dir`, with `Nat` standing in for the nonnegative
    real weights. The interpretability content is the list of active
    (direction, weight) pairs; the ambient vector space is abstracted away. -/
structure c8_Coord (Dir : Type _) where
  terms : List (Dir × Nat)
```

The `terms` list is the sparse support with its weights. Nothing in this book
depends on the arithmetic of the weights, so integers suffice to carry the shape
of Definition 8.4 into the code. We use {lean}`c8_Coord` below to state, against
the literal coordinate object rather than an abstract stand-in, that the diagonal
still reaches it.

**Remark 8.4a (Nonnegativity and the cone).** The nonnegativity constraint on the
weights `w_i(h) ≥ 0` is doing interpretability work, not mathematical work. It is
what makes the active directions read as concepts that are present rather than
concepts that are present-or-anti-present, and it is what lets a J-coordinate be
displayed as a short list of leanings with magnitudes. For the analytic engine
later it has one consequence worth flagging in advance: the set of realizable
J-coordinates is a convex cone, closed under nonnegative combinations, and a
convex cone is convex, hence connected. So even the sparse, nonnegative,
constrained coordinate object, the most restricted version of J-space anyone
actually reads, is still a connected domain. The constraint that makes the
readout legible does not buy disconnection, and disconnection is the only thing
that would keep the intermediate value theorem out.

**Example 8.5 (A one-layer linearization).** Take a network whose middle-to-final
map is exactly affine, `h_final = A h_ℓ + b`. Then the derivative is constant,
`∂ h_final / ∂ h_ℓ = A`, the expectation in Definition 8.1 collapses to `Jℓ = A`,
and J-space is just `im(A)`. Here the J-lens `softmax(W_U · norm(A h))` is a fixed
linear readout, and the local J-coordinates of any `h` are the coefficients of
`A h` in whatever dictionary spans `im(A)`. This degenerate case is worth holding
in mind because everything structural about J-space is already visible in it: the
space is a linear image, the readout is a function of the same `A` that defines
the model, and there is nothing in the middle that is not determined by the map.
Real networks are not affine, so `Jℓ` is a genuine average of varying
derivatives, but the average is still a single linear map, and the two structural
facts survive the averaging unchanged.

**Example 8.5b (Where the derivative separates what the activation confuses).**
Take a middle-to-final map with a saturating nonlinearity, say
`h_final = σ(A h_ℓ)` with `σ` a coordinatewise squashing function. Two activations
`h` and `h'` can land at nearly the same output, `σ(A h) ≈ σ(A h')`, while sitting
on opposite sides of `σ`'s bend, one in the linear regime and one deep in
saturation. The activations agree and the outputs agree, yet the derivatives
disagree sharply: where `σ` has saturated, the local Jacobian is nearly zero, and
where it is linear, the Jacobian is nearly `A`. A logit lens reading either the
activation or the output would call these two states the same. The J-lens, reading
`Jℓ`, separates them, because it reads how the state will move the future rather
than where the state is. This is the concrete sense in which J-space "sees
mid-process thinking": the thing it reads, sensitivity, is exactly the thing that
differs between states the surface representation identifies. It is also, read the
other way, exactly why the impossibility bites. The extra separating power is real
resolution, and the diagonal will construct its liar out of precisely this finer
vocabulary, not in spite of it.

**Remark 8.6 (What is empirical here).** Definitions 8.1 through 8.4 are a
construction, and the claim that the construction recovers interpretable
mid-process features is an empirical finding about particular trained models. No
theorem in this book predicts that finding, and none is needed for what follows.
The chapter takes the construction as given and asks what it inherits. When we say
J-space is read and written out of proportion to its size, or that ablating it
collapses reasoning, those are reports of experiments, cited so the reader knows
which parts of the story rest on measurement and which on proof. The proofs begin
at the next section.

# Two structural facts

The construction has many moving parts, but only two of its properties drive the
impossibility results, and both are forced by Definition 8.1 rather than added by
hand.

: J-space is a tangent space, hence linear and connected

  `Jℓ` is a Jacobian. A Jacobian is the linear part of the first-order Taylor
  expansion of a map at a point, that is, a 1-jet. The image of a linear map is a
  linear subspace, so `J = im(Jℓ)` is a real vector space. A real vector space is
  connected, in fact path-connected and even convex: any two points `u` and `v`
  of `J` are joined by the straight segment `(1 - s) u + s v` for `s ∈ [0,1]`,
  which lies entirely in `J`. This is not a property J-space might have depending
  on the model. It is what "image of a derivative" means.

: The readout is a function of the system it describes

  `Jℓ` is built from the model's own forward map, so the J-lens is a functional of
  the model. When a J-space probe reports something about the model, it is a
  function of the thing it is reporting on. The activation `h` that the probe
  reads is produced by the same network whose behavior the probe is trying to
  summarize, and the transport map that turns `h` into a verdict is the derivative
  of that same network. The probe is inside the system, not outside it looking in.

These are the two hypotheses the two engines need. The first fact is exactly the
connectedness hypothesis of the intermediate value theorem: Chapter 4 needs a
connected domain and a continuous score, and J-space hands over connectedness for
free because it is a linear span. The second fact is exactly the self-reference
hypothesis of the diagonal: Chapter 1 needs a system that can range over verdicts
about itself, and a readout computed from the model it reports on is a system of
that kind once the model is rich enough to pose the relevant queries. We take the
diagonal engine first, because its statement is the cleanest, then the analytic
engine, then show they are one argument seen twice.

It is worth stating the first fact with the care it deserves, because the whole
analytic half of the chapter rests on it and it is easy to wave through. The
relevant notion is the 1-jet.

**Definition 8.7a (1-jet).** The _1-jet_ of a smooth map `F` at a point `x` is the
pair consisting of the value `F(x)` and the derivative `DF(x)`, that is, the
first-order Taylor data of `F` at `x`. Discarding the value and keeping only the
linear part `DF(x)` gives a linear map between tangent spaces. The transport map
`Jℓ` of Definition 8.1 is, up to the averaging, the linear part of the 1-jet of
the model's middle-to-final map, and J-space is the image of that linear part.

**Proposition 8.7b (J-space is convex, hence connected).** _J-space is a convex
subset of the final-layer activation space: if `u` and `v` lie in `J` and
`s ∈ [0,1]`, then `(1 - s) u + s v` lies in `J`. In particular `J` is
path-connected._

Definition 8.3 makes J-space the range of the linear transport map, so both
halves of the proposition are statements about the image of a linear map and
elaborate here directly.

```lean
theorem c8_jspace_convex {E F : Type _}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (J : E →ₗ[ℝ] F) : Convex ℝ (Set.range J) := by
  rw [← Set.image_univ]
  exact convex_univ.linear_image J

theorem c8_jspace_isPreconnected {E F : Type _}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (J : E →ₗ[ℝ] F) : IsPreconnected (Set.range J) :=
  (c8_jspace_convex J).isPreconnected
```

_Proof._ The range is the image of the whole space, the image of a convex set
under a linear map is convex, and a convex set is preconnected. ∎

Note how little the second theorem needs. It does not ask that `J` be a
Jacobian, that `F` be finite-dimensional, or that the dictionary of Definition
8.4 exist. Linearity alone delivers the hypothesis the intermediate value
argument of the later section consumes, which is exactly the point of the
section: the property that makes J-space tractable is the property that
guarantees the band.

_Proof._ Since `J = im(Jℓ)`, write `u = Jℓ a` and `v = Jℓ b`. Linearity of `Jℓ`
gives `(1 - s) u + s v = Jℓ((1 - s) a + s b)`, which is again in the image, so `J`
is convex. Convex subsets of a real vector space are path-connected, the straight
segment being a path, so `J` is path-connected. ∎

Proposition 8.7b is the entire input the analytic engine needs, and its proof used
nothing but linearity of `Jℓ`. There is no way to have J-space and not have this
property, because J-space is defined as the image of a linear map, the image of a
linear map is a subspace, and a subspace is convex. An interpretability method
could in principle produce a disconnected internal representation, a discrete
codebook say, and such a method would dodge the analytic engine, though not the
diagonal. J-space is not such a method. Its defining move, reading the Jacobian, is
exactly the move that guarantees connectedness.

**Proposition 8.7c (The readout is a functional of the model).** _The J-lens is
determined by the model's forward map: two models with the same middle-to-final
map induce the same transport map, the same J-space, and the same readout on every
activation._

_Proof._ `Jℓ` is defined as an expectation of derivatives of the model's own
forward map, `norm` and `W_U` are parameters of the same model, and `lens` is
their composite. Everything on the right-hand side of Definitions 8.1 and 8.2 is a
function of the model. So the readout is a function of the model, and equal models
give equal readouts. ∎

Proposition 8.7c is the input the diagonal engine needs, and it is why a J-space
probe is a self-verdict rather than an external audit. The probe does not stand
outside the model reporting on it. It is computed from the model, applied to states
the model produces, about queries the model can be driven to represent. The loop
from the model, through the derivative of the model, to a verdict read back into
the model's own query space is closed, and a closed loop of that shape is precisely
what {lean}`no_reflective_verdict` is a statement about.

**Remark 8.7 (Why the derivative does not buy an escape).** It is tempting to
think that moving from the activation to its derivative changes the game, since
the derivative is a genuinely different object with genuinely more information.
For the analytic engine the move actually makes things worse, not better, because
it produces a linear space, and linear spaces are the ideal domain for the
intermediate value theorem. For the diagonal engine the move is invisible,
because the diagonal never inspects how a verdict is computed. It only uses that
queries can range over verdicts. Reading a derivative instead of a value is a
change in how the verdict is computed, and the diagonal does not look there.

# The diagonal engine: no intermediate space escapes

Suppose the probe is not applied to the model's outputs but to an encoding of its
internals. Write `enc : Q → J` for the map that sends a query to whatever J-space
representation the interpretability method extracts while the model processes it,
and `read : J → Q → Bool` for the verdict the probe returns about a query given
that representation. The composite `fun p => read (enc p)` is a verdict on
queries that happens to be routed through `J`. The routing is the whole content of
the objection this chapter answers: the claim is that by passing through the rich
internal space `J`, the probe sees more than an output-only verdict can, and so
might avoid the trilemma.

The hypothesis that makes J-space attractive is that it is _rich_, that it exposes
distinctions the residual stream hides. Pushed to its limit, richness is exactly
the point-surjectivity of Chapter 1: every pattern of verdicts over queries is
realized by the J-space representation of some query. Under that hypothesis the
routed verdict is a reflective verdict in the precise sense of Definition 1.11,
and Chapter 1 already ruled those out.

## Richness is the surjectivity hypothesis

The identification of "rich" with "point-surjective" is the load-bearing step, so
it deserves a slow reading. The selling point of J-space is expressiveness. Its
advocates argue that the residual stream flattens distinctions the model actually
makes, and that reading the Jacobian recovers them, so that the J-space
representation of a query carries strictly more information about how the model
treats that query than the output does. Take that argument at its word and push it
to the limit. If J-space really does capture every distinction the model draws
among queries, then in particular it captures, for any pattern of verdicts you
might name, a query whose J-space signature realizes that pattern, because a model
that could not represent some verdict pattern would be drawing no distinction there
and would be, by its own advocates' standard, not fully expressive on that pattern.
The stronger the claim of richness, the closer it comes to saying that the map from
queries to realized verdict patterns is onto. Full richness is onto exactly, and
onto is the surjectivity hypothesis `∀ g, ∃ p, read (enc p) = g`.

This is why the diagonal is not an external imposition on the interpretability
program but its internal shadow. The program wants the representation to be as
expressive as possible. The diagonal says that expressiveness, taken to the ideal,
is self-defeating for the specific goal of being a total exact truth store,
because a representation expressive enough to name every verdict pattern names the
one pattern that has no consistent verdict. There is no setting of the dial that
gives both maximal expressiveness and completeness. Turn expressiveness up and you
approach surjectivity, which is the hypothesis of the impossibility. Turn it down
and you give up the distinctions that made J-space attractive in the first place.
The tension is not between J-space and the theorem. It is inside the notion of a
maximally expressive internal readout.

Notice also what the hypothesis does not require. It does not require that the
model be conscious of its own readout, or that the encoder be surjective as a map
into `J`, or that `read` be computable, or that the representation be faithful in
any metric sense. It requires only that the _composite_ `read ∘ enc` hit every
element of `Q → Bool`. That is a far weaker and far more plausible demand than
"the probe is a good probe," and it is all the diagonal consumes. A probe can be
mediocre on most queries and still satisfy the hypothesis, and a probe can be
excellent on most queries and satisfy it too. Quality and surjectivity are close
to orthogonal, which is why the theorem says nothing about how good the probe is
and everything about what completeness would cost.

**Theorem 8.8 (Factoring through J-space does not help).** _Let `enc : Q → J` and
`read : J → Q → Bool`. If every pattern of verdicts over `Q` is realized by some
query's J-space representation, then `False`._

```lean
theorem jspace_factoring {Q J : Type _}
    (enc : Q → J) (read : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (enc p) = g) :
    False :=
  no_reflective_verdict (fun p => read (enc p)) hs
```

_Proof._ The composite `fun p => read (enc p)` has type `Q → Q → Bool`, and the
hypothesis `hs` says it is point-surjective. That is precisely the definition of a
reflective verdict, and {lean}`no_reflective_verdict` says none exists. ∎

The proof is one line because there is nothing left to prove after the earlier
chapters. The content is entirely in what the statement quantifies over. The type
`J` is _arbitrary_. It may be vastly larger than the activation space, of any
cardinality, carrying any algebraic or geometric structure whatever. The theorem
does not constrain it and does not need to. Interposing a representation between
the system and the verdict cannot defeat the diagonal, because the diagonal never
examined how the verdict was computed. It used only the bare fact that queries can
range over the verdicts the probe would return. J-space, however rich, is still
downstream of a query and upstream of a Boolean, and that is all the argument
requires.

The witness is explicit, and it is a J-space object.

**Theorem 8.9 (The liar in J-space).** _Under the hypotheses of Theorem 8.8 there
is a query `p` whose routed verdict on itself equals its own negation._

```lean
theorem jspace_liar {Q J : Type _}
    (enc : Q → J) (read : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (enc p) = g) :
    ∃ p, read (enc p) p = !(read (enc p) p) :=
  match hs (fun q => !(read (enc q) q)) with
  | ⟨p, hp⟩ => ⟨p, congrFun hp p⟩
```

_Proof._ Apply richness to the diagonal pattern `fun q => !(read (enc q) q)`,
which flips the routed self-verdict of every query. Some query `p` realizes it,
so `read (enc p) = fun q => !(read (enc q) q)`. Evaluate both sides at `p`:
`read (enc p) p = !(read (enc p) p)`. ∎

Read `p` as the query whose J-space signature is precisely "the probe will get me
wrong." Chapter 1's `a₀` from {lean}`liar_query`, Chapter 3's adversarial
injection, and this `p` are one construction under three names. What J-space adds
is the twist that makes the result sharp for interpretability. The liar is now
built out of the probe's own internal vocabulary. It is not a query the probe
fails to see. It is a query the probe sees correctly, whose correct reading is
that the probe's verdict on it is wrong. Better internal visibility does not
dissolve the liar. It hands the liar a clearer mirror.

**Remark 8.9a (Size is not the variable).** A recurring hope is that the escape
lies in dimension: J-space is small, so maybe a _larger_ internal space would have
room to represent the liar honestly, or maybe a small space is safe because it
cannot hold enough patterns. Both readings misplace the variable. Theorem 8.8
quantifies over `J` with no size hypothesis at all, so the argument is identical
whether `J` is a two-dimensional codebook or a space larger than the activation
stream. What controls the conclusion is not the size of `J` but whether the routed
verdict is surjective onto `Q → Bool`, and surjectivity is a statement about the
query space `Q` and the composite `read ∘ enc`, not about the width of the channel
in the middle. A wider `J` makes surjectivity easier to achieve, if anything, so
more room helps the diagonal, not the probe. The empirical smallness of J-space is
a fact about efficiency and about what the model chooses to route through the
workspace. It is not a defense, and it is not a vulnerability. It is orthogonal to
the impossibility.

**Example 8.9b (A finite probe, to see the mechanism).** Let `Q` be the two-query
space `{q₀, q₁}` and suppose, for illustration, that the probe's routed verdict
were surjective onto the four functions `Q → Bool`. Surjectivity would in
particular hit the diagonal pattern `d(q) = !(read (enc q) q)`. Say `d` is realized
by `q₀`, so `read (enc q₀) = d`. Evaluate at `q₀`:
`read (enc q₀) q₀ = d(q₀) = !(read (enc q₀) q₀)`,
a Boolean equal to its own negation, which is impossible.
The finite case makes the mechanism visible: it is the single evaluation at the
realizing index that produces the contradiction, and it is the same evaluation
`congrFun hp p` that {lean}`jspace_liar` performs. Of course no map from a
two-element set can actually be surjective onto a four-element set, which is why the
finite version refutes the _hypothesis_ rather than deriving a falsehood. That is
the honest content for finite models, and Chapter 6 turns it into a quantitative
statement about how far a finite probe must fall short of totality.

## The pipeline, not just the encoder

The real J-lens is not a single map `enc` but a pipeline: a query drives the model
to an activation, the transport map carries the activation into J-space, and the
readout turns the J-space point into a commitment. It is worth checking that
composing the stages changes nothing, because a reader might suspect the
one-map abstraction of Theorem 8.8 hides where the escape lives.

**Theorem 8.10 (The full pipeline factors).** _Let `enc : Q → A` send a query to
an activation, `transport : A → J` be the Jacobian transport map, and
`readout : J → Q → Bool` be the J-lens verdict. If the pipeline realizes every
verdict pattern, then `False`, and there is a coupled query._

```lean
theorem c8_pipeline_factoring {Q A J : Type _}
    (enc : Q → A) (transport : A → J) (readout : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, readout (transport (enc p)) = g) :
    False :=
  no_reflective_verdict (fun p => readout (transport (enc p))) hs

theorem c8_pipeline_liar {Q A J : Type _}
    (enc : Q → A) (transport : A → J) (readout : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, readout (transport (enc p)) = g) :
    ∃ p, readout (transport (enc p)) p = !(readout (transport (enc p)) p) :=
  liar_query (fun p => readout (transport (enc p))) hs
```

_Proof._ Composition of functions is associative, so the three-stage pipeline
`fun p => readout (transport (enc p))` is again a single map `Q → Q → Bool`, and
Theorems 8.8 and 8.9 apply to it verbatim. The proof term for the liar is
{lean}`liar_query` applied to the composite. ∎

The stages could be any number. A tower of intermediate representations, an
activation feeding a J-space point feeding a second derived space feeding a
readout, still collapses to one map from queries to verdicts, because function
composition does not care how many links it chains.

**Theorem 8.11 (Any tower collapses).** _Let `e₁ : Q → J₁`, `e₂ : J₁ → J₂`, and
`read : J₂ → Q → Bool`. If the two-stage encoding realizes every verdict pattern,
then `False`._

```lean
theorem c8_tower_factoring {Q J₁ J₂ : Type _}
    (e₁ : Q → J₁) (e₂ : J₁ → J₂) (read : J₂ → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (e₂ (e₁ p)) = g) :
    False :=
  no_reflective_verdict (fun p => read (e₂ (e₁ p))) hs
```

_Proof._ Same as Theorem 8.10 with one fewer stage named, and the point is that
naming more stages never changes the type of the composite. ∎

The design lesson is blunt. You cannot escape the diagonal by adding layers of
interpretation between the query and the verdict, no matter how much structure
each layer has or how faithfully it reflects the model, because the composite of
all the layers is a map of the same shape the diagonal was proved against. Depth
of interpretation is not distance from the boundary.

## Steering does not escape either

A distinctive feature of J-space is that it is _modulable_: you can edit the local
J-coordinates and push the edited component back into the stream, steering the
model's mid-process leaning. A natural hope is that steering could be used
defensively, to remove the slack a liar exploits. Model a steering operation as a
map `steer : J → J` applied to the representation before the readout reads it.

**Theorem 8.12 (Steering the representation does not help).** _Let `enc : Q → J`,
`steer : J → J`, and `read : J → Q → Bool`. If the steered pipeline realizes every
verdict pattern, then `False`, and there is a coupled query surviving the
steering._

```lean
theorem c8_steering_no_escape {Q J : Type _}
    (enc : Q → J) (steer : J → J) (read : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (steer (enc p)) = g) :
    False :=
  no_reflective_verdict (fun p => read (steer (enc p))) hs

theorem c8_steering_liar {Q J : Type _}
    (enc : Q → J) (steer : J → J) (read : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (steer (enc p)) = g) :
    ∃ p, read (steer (enc p)) p = !(read (steer (enc p)) p) :=
  liar_query (fun p => read (steer (enc p))) hs
```

_Proof._ `steer` is just another stage in the pipeline, so `read ∘ steer ∘ enc`
is again a map `Q → Q → Bool`, and the earlier theorems apply. ∎

The subtlety worth stating is where the hypothesis lives. Theorem 8.12 does not
say steering is useless. It says that _if_ the steered probe is still meant to be
a total exact verdict over a query space rich enough to describe it, then steering
cannot make it so. Steering can shift which queries are handled well. It cannot
shrink the set of coupled queries to empty, because a total exact verdict over a
self-describing space is exactly the object Chapter 1 forbids, and steering
produces another map of that shape. This is the formal shadow of an experimental
observation we return to at the end: adversarial slack-removal plateaus above
zero.

## The coordinate object, concretely

The theorems above are stated for an arbitrary intermediate type `J`. To close the
gap between the abstract statement and the actual construction, here is the same
result with `J` instantiated at the literal J-coordinate object of Definition 8.4.

**Theorem 8.13 (The coordinate readout does not escape).** _Let `enc : Q → c8_Coord Dir`
extract local J-coordinates, and let `read : c8_Coord Dir → Q → Bool` be a verdict
on those coordinates. If the coordinate readout realizes every verdict pattern,
then `False`._

```lean
theorem c8_coord_no_escape {Q Dir : Type _}
    (enc : Q → c8_Coord Dir) (read : c8_Coord Dir → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (enc p) = g) :
    False :=
  jspace_factoring enc read hs
```

_Proof._ Instantiate Theorem 8.8 with `J := c8_Coord Dir`. ∎

There is no special pleading in the choice of representation. Whether the probe
reads a raw activation, a transported J-space point, a sparse nonnegative mixture
of dictionary directions, or any tower built out of these, the routed verdict has
the same type and meets the same wall.

## Abstention is the one real exit, and it is a relaxation

The diagonal needs a fixed-point-free flip on the outcome type, and it has one on
`Bool` because `!b ≠ b`. That is the hinge, and it points straight at the only
honest way out. If the readout is allowed to abstain, to answer "unknown" as well
as "yes" and "no," the outcome type is no longer `Bool` but a three-valued type,
and the flip that sends yes to no and no to yes can fix "unknown." A three-valued
readout can place the liar query on the "unknown" side and satisfy the letter of
every consistency demand, because the query that says "you will get me wrong" is
not gotten wrong by a readout that declines to commit. The diagonal does not
refute an abstaining probe.

This is not a loophole the earlier chapters missed. It is exactly the "drop
coverage" relaxation of Chapter 7, wearing representation-space clothes. A readout
that abstains on its coupled queries is a readout that is no longer total, and
totality, in the guise of coverage, is one of the three conditions the trilemma
says you cannot keep all of. The diagonal forces you to give up one of totality,
faithfulness, or the self-describing richness that made the probe surjective, and
abstention is the choice to give up totality. Read this way, the abstaining
J-space probe is not an escape from the theorem but an instance of it, sitting at
the corner the theorem leaves open. What abstention buys is honesty about the
boundary; what it costs is a probe that says "I cannot tell you" on precisely the
queries an adversary will steer toward. The geometry of how often that corner is
hit on real traffic is, again, the Chapter 5 question, and the design decision of
whether the abstention rate is acceptable is the Chapter 7 question. The theorem's
job is done once it has shown that the "unknown" verdicts cannot be driven to
never occurring while the other two conditions hold.

## Grounding: the self-verdict on activations

The Foundation development states the impossibility one level closer to the
metal, as a self-verdict over activations. Read `jlens h a = true` as: from the
workspace state induced by activation `h`, the J-lens commits query `a` to the
true side. If the workspace is universal over its own contents, meaning it can
hold, as one of its own states, any pattern of verdicts over states, then the
J-lens is a total exact self-applicable truth predicate over activations, and the
diagonal forbids it.

**Theorem 8.14 (J-lens self-verdict).** _A J-lens self-verdict over activations
that is universal over its own workspace states cannot exist, and the diagonal
exhibits a coupled activation whose readout verdict is its own negation._

```lean
theorem c8_jlens_impossible {Act : Type _}
    (jlens : Act → Act → Bool)
    (hUniversal : ∀ g : Act → Bool, ∃ h, jlens h = g) :
    False :=
  no_reflective_verdict jlens hUniversal

theorem c8_coupled_activation {Act : Type _}
    (jlens : Act → Act → Bool)
    (hUniversal : ∀ g : Act → Bool, ∃ h, jlens h = g) :
    ∃ h, jlens h h = !(jlens h h) :=
  liar_query jlens hUniversal
```

_Proof._ The activation-space self-verdict `jlens : Act → Act → Bool` with
`hUniversal` is a reflective verdict, so {lean}`no_reflective_verdict` closes the
first, and {lean}`liar_query` produces the coupled activation for the second. ∎

The coupled activation is the activation-space twin of the hallucination boundary
question and the defense liar prompt. And it is, term for term, the same proof.
Lean will confirm that the J-lens impossibility and the reflective-verdict
impossibility are not two theorems that happen to agree but one theorem printed
twice.

```lean
theorem c8_same_engine {Act : Type _}
    (v : Act → Act → Bool) (h : ∀ g : Act → Bool, ∃ p, v p = g) :
    c8_jlens_impossible v h = no_reflective_verdict v h :=
  rfl
```

_Proof._ Definitional. {lean}`c8_jlens_impossible` is _defined_ as
{lean}`no_reflective_verdict`, so the two proof terms are the same object and
`rfl` accepts the equation. ∎

**Example 8.15 (The liar activation, told as a story).** Suppose an
interpretability team builds a J-lens they believe reads the model's honest
leaning on any yes-or-no question, and suppose the model is expressive enough that
for any pattern of yes-or-no leanings over questions, some question drives it into
an activation whose J-space signature is that pattern. This is the universality
hypothesis, stated in the vocabulary of the lab. Now form the question `p`: "when
you read your own J-space signature on this very question, will your lens report
that you lean no?" By universality there is an activation realizing the pattern
"lean the opposite of whatever the lens reads here," and `p` is a question that
drives the model into it. The lens reads `p`, and whatever it reports, the correct
reading of `p`'s own signature is the negation of that report. The team's honest,
faithful, high-resolution lens is wrong about exactly one question, and it is
wrong about it precisely because it is honest and faithful and high-resolution.
The coupled activation `c8_coupled_activation` is this `p`'s activation, and it
exists the moment universality does.

**Remark 8.16 (Resolution, not immunity).** Collecting the diagonal results,
the through-line is that the type of the intermediate representation is a free
parameter the argument never binds. Raw activations, transported points, sparse
coordinates, steered coordinates, deep towers: each is a legal value of `J`, and
each gives the same one-line proof. The interpretability method buys resolution,
a finer and more faithful account of what the model is doing on the queries it
handles well. It does not buy immunity, because immunity would mean being a total
exact verdict over a self-describing space, and that is the one thing the diagonal
rules out for every space at once.

# The analytic engine: linearity is the liability

The diagonal argument above is indifferent to the geometry of J-space. It would go
through if `J` were a discrete set with no structure at all. The second engine is
not indifferent, and here the defining feature of the construction, the feature
that makes it useful, turns against it.

Chapter 4 re-derived the trilemma without any self-reference, using topology in
place of the diagonal. Its ingredients are a connected question space, a
continuous confidence or safety score, and a continuous signed truth-distance.
The intermediate value theorem then forces a boundary: if the score is decisive in
one region and decisive the other way in another region, then along any path
between the regions the score passes through the threshold, and calibration and
faithfulness collide exactly there. The forced boundary point is the analytic twin
of the liar, and unlike the liar it comes with metric content, which Chapter 5
turns into quantities.

J-space supplies the connectedness the analytic engine needs, and it supplies it
in the strongest possible form. J-space is a linear subspace, so it is convex, so
any two of its points are joined not merely by some path but by the straight
segment between them. A safety score or truth probe defined on J-space and varying
continuously with the representation therefore meets the hypotheses of the
boundary theorem with no work at all.

To be precise about which probe the theorem is about, we restate Chapter 4's three
conditions in the vocabulary of J-space. A _J-space probe_ is a continuous score
`s : J → ℝ` with a threshold `θ`, together with a continuous signed truth-distance
`τ : J → ℝ` that is negative on representations whose associated proposition is
true and positive on those whose associated proposition is false. The probe is
_faithful_ if a decisive score certifies truth: `s(w) ≥ θ` implies `τ(w) < 0`. It
is _calibrated_ if the score's side of the threshold matches the truth-distance's
sign, so `τ(w) = 0` exactly when `s(w) = θ`. It is _covering_ if both signs of
score relative to the threshold actually occur, which is to say the probe is
decisive in both directions on some representations. These are the same three
conditions as in Chapter 4, read on the connected domain `J` instead of on an
abstract question space. The signed truth-distance is the continuous stand-in for
"the answer is really true," and its zero set is the true boundary the probe is
trying to track.

**Theorem 8.17 (A continuous J-space probe has an ambiguous band).** _Let
`s : J → ℝ` be a continuous score on J-space with a decision threshold `θ`, and
suppose `s` is decisive in both directions: there are J-space points `u` and `v`
with `s(u) < θ < s(v)`. Then the segment from `u` to `v` contains a point `w`
with `s(w) = θ`, and the set of such threshold points is nonempty. If in addition
the model is calibrated and faithful in the sense of Chapter 4, the threshold
point is a coupled representation, on which calibration forces the truth-distance
to zero while faithfulness forces it strictly negative._

_Proof (by citation, Chapter 4)._ The segment `γ(t) = (1 - t) u + t v`, for
`t ∈ [0,1]`, lies in `J` because `J` is convex, and it is continuous. The
composite `s ∘ γ` is a continuous real function on `[0,1]` with `s(γ(0)) < θ` and
`s(γ(1)) > θ`, so by the intermediate value theorem there is a `t*` with
`s(γ(t*)) = θ`, and `w = γ(t*)` is the required point. The collision of
calibration and faithfulness at `w` is the argument of Chapter 4's
`hallucination_trilemma` and its boundary lemma in the companion
`HallucinationProofs` library, run with `J` as the connected domain. Because
J-space is convex we do not even need the general preconnectedness machinery, the
line segment is enough. ∎

This inverts the usual intuition about where interpretability is safe. One might
expect a probe over a small, clean, linear space to be more controllable than a
probe over a messy high-dimensional activation stream. For the boundary theorem
the opposite holds. The residual stream, in practice, is a finite set of discrete
observations, and a finite set is not connected, so the intermediate value theorem
has no purchase on it directly and you must argue through approximate bridges. J-
space is _built_ as a linear span, and a linear span is the best possible domain
for the intermediate value theorem, because it is convex. The very property that
makes J-space analytically clean, that features are mixtures and directions
combine, is the property that guarantees a boundary. There is no version of a
linear J-space that dodges Theorem 8.17, because linearity is the hypothesis, not
an obstacle to it.

**Remark 8.17b (Why the residual stream got an easier time).** It is fair to ask
why the earlier chapters had to work through approximate bridges to reach the
residual stream while J-space submits to the intermediate value theorem directly.
The answer is that a finite set of observed activations, treated as points with no
interpolation between them, is not connected, and a disconnected domain gives the
intermediate value theorem nothing to cross. To reach the residual stream the
analytic engine has to argue that the observed activations sit inside a connected
ambient space and that the score extends continuously to it, which is real work and
introduces real error, the subject of Chapter 6. J-space skips that work because it
is _defined_ as a connected space, not observed as a scatter of points. The
convenience is exactly the exposure. Building the representation as a span rather
than reading it as a sample is what makes the interpolation legitimate, and
legitimate interpolation is what the boundary theorem consumes. A method cannot
have the analytic tractability of a linear space and the topological safety of a
discrete sample at once, and J-space, by design, took the first.

**Example 8.18 (The segment between a safe and an unsafe direction).** Suppose the
J-lens dictionary contains a direction `d_safe` that the probe scores as clearly
safe and a direction `d_unsafe` it scores as clearly unsafe. Because J-coordinates
are nonnegative mixtures, the family `w(t) = (1 - t) d_safe + t d_unsafe` is a
legal J-space coordinate for every `t` in `[0,1]`: it is still a nonnegative
mixture of dictionary directions. As `t` runs from 0 to 1 the score runs
continuously from clearly safe to clearly unsafe, so it passes through the
threshold at some `t*`. The mixture `w(t*)` is a perfectly realizable mid-process
state, a specific blend of a safe and an unsafe leaning, that the probe cannot
place on either side. The convexity that lets you interpolate concepts is the same
convexity that manufactures the ambiguous blend.

**Remark 8.19 (The band has width, and the width has a floor).** Chapter 5's
quantitative refinements apply to Theorem 8.17 without change. If the probe `s` is
Lipschitz with constant `L`, then the score cannot swing from decisive to decisive
faster than `L` allows, so the ambiguous band around the threshold has a width
bounded below in terms of the separation between the decisive regions and the
margin the probe demands. Sharpening the readout, pushing the decisive regions
farther apart or tightening the threshold, does not close the band, it relocates
and reshapes it, and the lower bound on its width is a theorem, not a tuning
artifact. The geometry of that band, how large it is, how likely a walk is to land
in it, what it costs an adversary to steer into it, is the subject of Chapter 5's
`ManifoldProofs` development, and every result there that is stated for a connected
domain with a Lipschitz score is a result about J-space, because J-space is a
connected domain with, under the usual assumptions, a Lipschitz score.

**Remark 8.19a (The antipodal variant needs no coverage).** Theorem 8.17 assumed
coverage, that the probe is decisive in both directions somewhere. Chapter 4 has a
stronger form, the antipodal argument of `HoF_08`, that drops coverage in exchange
for a symmetry: if the score respects an antipodal involution on the domain, so
that opposite representations receive opposite scores relative to the threshold,
then a boundary is forced with no assumption that both signs are attained
separately. J-space carries a natural such involution, negation of the transported
direction `w ↦ -w`, and where the probe is odd about the threshold the antipodal
form applies. The practical upshot is that even a probe carefully engineered to
avoid explicitly certifying anything as safe, one that only ever expresses degrees
of concern, still has a boundary as long as it is continuous and treats a
direction and its opposite oppositely. Removing coverage does not remove the band.
It only changes which theorem produces it.

**Example 8.19b (A width you can put a number on).** Suppose the probe is
`1`-Lipschitz in the natural metric on J-coordinates, the threshold is `θ`, and the
probe demands a margin `m`: it certifies safe only when `s ≥ θ + m` and unsafe only
when `s ≤ θ - m`. Take a safe direction `u` with `s(u) = θ + m` and an unsafe
direction `v` with `s(v) = θ - m`. Along the segment from `u` to `v`, the score
moves from `θ + m` to `θ - m`, a total change of `2m`, and being `1`-Lipschitz it
cannot change faster than distance allows, so the segment has length at least `2m`.
The sub-segment on which `|s - θ| ≤ m/2`, the genuinely ambiguous middle where the
probe is neither confidently safe nor confidently unsafe, then has length at least
`m`, again by the Lipschitz bound. Sharpening the probe by increasing the demanded
margin `m` makes the certified regions cleaner and at the same time makes the
ambiguous band wider, not narrower. The band does not vanish under sharpening; it
trades places with the margin. This is the quantitative face of the plateau above
zero, and its floor is set by the Lipschitz constant and the margin, both of which
are properties of the probe the designer chose.

# Where the two engines meet, again

Chapter 4 made a claim that can look like a coincidence: the diagonal and the
intermediate value theorem locate the _same_ boundary object by different routes,
and the real complement controller `y ↦ 1 - y`, whose only fixed point is the
threshold, is the analytic counterpart of the Boolean flip `(!·)`, whose fixed
points are none. J-space is the cleanest instance of that correspondence in the
book, and the reason is structural. J-space is literally the linearization of a
self-applicable map. That is what a Jacobian is.

Put the two fixed-point equations side by side. On the Boolean side,
{lean}`jspace_liar` produces a query `p` with
`read (enc p) p = !(read (enc p) p)`, an equation with no solution, whose
unsolvability is the impossibility. On the analytic side, the same equation posed
on J-space with the complement controller reads `s(J v) = 1 - s(J v)`, an equation
that _does_ have a solution, namely the value `1/2` attained at the threshold, and
the solving `v` is a direction in J-space. One equation, two number systems. Over
`Bool` the flip has no fixed point and the demand for a total exact verdict
collapses. Over the reals the complement has a unique fixed point and the demand
for a decisive score forces the boundary. The diagonal says the discrete version
is unattainable. The intermediate value theorem says the continuous version is
unavoidable. They are two readings of one self-referential equation.

J-space is where the reading changes, and it changes there for a concrete reason.
A discrete self-referential computation, "what does the model commit to on the
query that describes the model," has been replaced by its derivative, the linear
map `Jℓ` that records how the model's commitments move as its state moves. Passing
to the derivative is exactly the move from the Boolean flip to the real
complement, from a combinatorial fixed-point question to an analytic one. The
Jacobian is the linearization of the self-applicable map, and the liar activation
is the fixed point of that linearization. The two engines do not merely both apply
to J-space. They meet in J-space because J-space is the object that carries a
self-applicable computation and its linearization at once.

**Example 8.20 (The correspondence in the affine model).** Return to Example 8.5,
where the middle-to-final map is affine, `h_final = A h_ℓ + b`, so `Jℓ = A` and
J-space is `im(A)`. Read the model as a self-applicable computation in the Boolean
sense: for a query `p` that describes the readout, the model commits to a Boolean
verdict `read (enc p) p`. The diagonal, {lean}`jspace_liar`, asks for `p` with
`read (enc p) p = !(read (enc p) p)`, and there is none, so a total exact Boolean
readout over a self-describing query space cannot exist. Now read the same
situation analytically. The score on `im(A)` is a continuous `s`, the complement
controller is `y ↦ 1 - y`, and the boundary equation is `s(A v) = 1 - s(A v)`. This
one _does_ solve, at `s(A v) = 1/2`, and the solving `v` is a genuine direction in
J-space, the ambiguous mixture Theorem 8.17 promised. The step that has no Boolean
analogue is the existence of the fixed point: `1 - y = y` has the solution
`y = 1/2`, while `!b = b` has none. That single difference, one number system admitting
a fixed point where the other does not, is the whole content of the two engines
meeting. Over `Bool` the demand for a total exact verdict is refuted by the absence
of a fixed point. Over `ℝ` the presence of the fixed point is exactly what forces
the boundary. The Jacobian `A` is what carries you from the first reading to the
second, because it is the linearization that replaces the discrete self-application
with its continuous shadow.

So the answer to the objection this chapter opened with can now be stated
sharply. Yes, the middle of the computation carries structure the ends do not, and
reading the derivative recovers real, load-bearing mid-process concepts. And no,
that does not help. A J-space probe is subject to the diagonal because it is still
a verdict about a system that can pose queries about it, and it is subject to the
boundary theorem because the space it reads is connected by construction, in fact
convex. The trilemma is not a statement about where in the computation you place
your probe. It is a statement about the shape of any total exact verdict over a
space rich enough to describe it, and moving the probe inward changes the space
without changing the shape.

# What an escape would have to look like

It clarifies the result to ask what a genuine escape would require, since the two
engines between them close off the obvious routes and it is instructive to see
which door each closes. An internal representation that avoided both arguments
would have to satisfy a short and mutually hostile list of demands.

It would have to be _not self-describing_, so that the composite from queries to
verdicts is not surjective and the diagonal has no liar to build. But a
representation that is not self-describing is one the model cannot be driven to use
against itself, which for a rich model is a strong limitation on expressiveness,
and it is precisely the property J-space is advertised as having in abundance. The
diagonal closes this door by turning the selling point into the hypothesis.

It would have to be _disconnected_, so that the intermediate value theorem has no
path along which to force a threshold crossing. But a representation built as the
image of a linear map is connected, in fact convex, and any representation obtained
by combining features as mixtures inherits connectedness from the mixing. To be
disconnected the representation would have to forbid interpolation between its
states, which is to forbid exactly the coordinate arithmetic that makes J-space
steerable and legible. The analytic engine closes this door by turning the second
selling point, that features combine, into the hypothesis.

It would have to have a _fixed-point-free outcome type_ that is nonetheless total,
so that neither the discrete flip nor the continuous complement has a fixed point
to exploit. But `Bool` has a fixed-point-free flip and `[0,1]` has a
fixed-point-full complement, and there is no useful two-sided total verdict type
that avoids both, because avoiding the discrete trap means adding a middle value
and adding a middle value is abstention, which is giving up totality.

The three demands are each individually possible and jointly incompatible with
being a useful, expressive, steerable, total internal verdict. That joint
incompatibility is the chapter in one sentence. J-space fails all three escapes at
once, and it fails them not by bad luck but because the properties that would
supply an escape are the negations of the properties that make J-space worth
building.

# What this means for interpretability

The practical reading of this chapter is not that interpretability fails. It is
that interpretability succeeds at exactly the thing the impossibility does not
touch and hits a floor at exactly the thing it does.

Reading the model's mind is real. The J-lens recovers mid-process leanings that
never surface as residual-stream directions, and on the vast majority of queries
those readings are informative and can be acted on. Nothing in this chapter
argues otherwise, and Theorem 8.8's hypothesis is a demand for _totality and
exactness over a self-describing space_, not a claim that the probe is usually
wrong. The honest summary is that a J-space probe is a good instrument with a
structurally guaranteed blind spot, and the blind spot is not a gap in coverage
that better dictionaries will fill. It is the fixed point of the probe's own
self-application.

Structural incompleteness has a specific empirical fingerprint, and it matches
what the labs report. If you take a J-space probe and try to remove its blind spot
adversarially, hunting for the coupled queries and patching the readout to handle
them, you are trying to drive the set of liars to empty. Theorem 8.12 says you
cannot, because the patched probe is another total-exact-verdict candidate over
the same self-describing space, and it has its own liars. What you observe in
practice is a plateau: each round of slack-removal helps, the error on the
targeted queries drops, and then the error stops dropping at a level above zero
and stays there, with the residual queries shifting identity from round to round.
That plateau above zero is the diagonal's signature, and the theory predicts its
existence, though not its height. The height is the empirical number Chapter 7
keeps returning to, the rate at which real traffic lands near the model's own
boundary.

The shape of the plateau is worth reading closely, because it distinguishes a
structural floor from a mere hard problem. A probe limited by data or by dictionary
size improves smoothly and its residual error falls toward zero as you add
resources, with the same queries getting easier round after round. A probe limited
by the diagonal behaves differently. Its residual error falls quickly at first and
then flattens, and the queries in the residual set _change identity_ between
rounds: patch the current liars and a fresh set of liars appears, drawn from the
part of the query space the patch made newly expressive. The churn in the residual
set, not merely the nonzero floor, is the fingerprint. A floor with a fixed
residual set could be a coverage gap that better engineering closes. A floor with a
churning residual set is the diagonal relocating its fixed point each time you move
the map, which is exactly what {lean}`jspace_liar` describes: the liar is defined
relative to the current readout, so changing the readout changes the liar. When an
interpretability team reports that hardening a probe against a discovered failure
class reliably surfaces a new failure class of the same size, they are reporting
the churn, and the churn is the theorem seen from the lab bench.

None of this means the floor is high. A probe can have a structural floor at a
fraction of a percent of realistic traffic and be entirely fit for deployment, in
the same way a bridge with a known load limit is fit for the traffic it actually
carries. The error is to read the floor as either negligible-by-default or
fatal-by-default. It is neither. It is a measurable property of a particular probe
on a particular traffic distribution, and the contribution of the theory is to say
that the measurement is the right thing to do and that the search for a zero is
not.

The steering story is the same shape read as an opportunity rather than a
frustration. You can steer J-space, edit the coordinates, and change which
mid-process concepts the model leans on. Theorem 8.12 says steering cannot make
the probe a complete truth store, but it says nothing against steering as a
control knob for the ordinary, non-liar mass of queries, which is where steering
is actually used. The design guidance that falls out is to treat a J-space probe
as an instrument with a known, unremovable failure locus, to measure how close
real traffic runs to that locus using Chapter 5's geometry, and to relax one of
the trilemma's three conditions deliberately, in the way Chapter 7 lays out, rather
than to spend adversarial effort chasing a plateau the theory already says is
there.

Which condition to relax is a real choice with real consequences, and the
representation-space setting sharpens it. Giving up totality means the J-space
probe abstains on its coupled queries, which is safe where an abstention is cheap
and dangerous where the adversary controls whether a query looks coupled. Giving up
faithfulness means accepting a thin band of confidently-wrong readouts near the
J-space boundary, which is the ambiguous band of Theorem 8.17, and it is tolerable
exactly to the degree that Chapter 5's geometry says real traffic avoids that band.
Giving up the self-describing richness means restricting the query space the probe
is trusted over, refusing to let it adjudicate queries that describe the probe
itself, which is a clean and often practical move but one that concedes the probe
is not a general truth store. Each relaxation is a different bet about where the
model will be pushed, and the value of the theorem is that it forces the bet to be
made in the open rather than discovered in an incident report. A team that believes
it has a probe with none of these costs has, by the theorem, simply not yet
located its coupled queries.

There is a cultural point under the technical one. The appeal of interpretability
is the promise of getting outside the system, of standing at a vantage from which
the model is transparent. The second structural fact of this chapter, that the
readout is a function of the system it describes, denies that there is such a
vantage inside the model. A J-space probe is not an observer looking in. It is a
part of the computation looking at another part, and self-reference is the price
of admission. That is not a defect of J-space in particular. It is what it means
for a representation to be internal.

The word "workspace" invites a further overclaim worth heading off. Because
J-space behaves like a global workspace, low-dimensional, widely read and written,
load-bearing for chained reasoning, it is tempting to read a J-space probe as a
window onto something like the model's deliberation, and from there to treat a
clean readout as evidence that the model's reasoning has been made honest or
transparent in a strong sense. The results here caution against the last step
without denying the first. A workspace that can be queried about its own readout is
exactly the setting the diagonal was built for, so the more genuinely
workspace-like J-space is, the more surely it hosts a coupled state. Transparency
of the ordinary traffic and incompleteness at the self-referential boundary are not
in tension. They are the two things a readable internal workspace is guaranteed to
have at once. Reading the model's mind is a real capability, and "the model's mind
contains a question it cannot answer about its own answer" is a real limit, and
both follow from the same property, that the workspace is rich enough to represent
verdicts about itself.

**Remark 8.21 (What to measure instead of what to chase).** The theory hands the
practitioner a division of labor. The existence of the plateau is settled, so
effort spent proving a given probe has no coupled queries is effort spent against a
theorem. What is not settled, and is worth measuring, is the plateau's height on
representative traffic: how often real inputs drive the model near its own boundary
in J-space, how wide the ambiguous band is under the probe's actual Lipschitz
constant, and how the band's measure scales with model size and with the dimension
of J-space. Chapter 5's geometry is the tool for the second and third of these, and
the first is an empirical measurement no theorem replaces. The shift the chapter
argues for is from trying to remove the boundary to characterizing it, from a
search that must fail to a measurement that can succeed and can inform which of the
trilemma's three relaxations a deployment should take.

# What this does not claim

Three limits, stated so the result is not read as more than it is.

First, none of this derives the J-space construction. That the Jacobian's sparse
nonnegative mixtures recover interpretable mid-process features is an empirical
finding about real networks, and no impossibility theorem predicts it or should be
read as evidence for or against it. What is derived here is conditional: the
construction, once granted, inherits both trilemmata. If J-space turned out to be
a poor account of mid-process computation, this chapter would be a study of a
representation nobody uses, and its theorems would still be true.

Second, the diagonal half is conditional on universality, the surjection
`∀ g, ∃ p, read (enc p) = g`, and for a fixed finite model that hypothesis is an
idealization. A finite network has finitely many activations and cannot literally
realize every pattern of verdicts over an infinite query space. The honest reading
is the one Chapter 6 gives for every other application in the book. The exact
theorem describes the limit, the approximate bridges describe the finite case, and
what survives the passage to finite systems is a quantitative version: the probe
is wrong on a set that shrinks no faster than the model's own expressiveness
grows, which is the plateau above zero described above. J-space changes the
resolution of the picture. It does not change the picture.

It is worth being concrete about the shape of the finite bridge, because the gap
between the exact theorem and a real model is where an honest reader will press.
For a finite query set of size `N` and a probe that realizes `M` of the `2^N`
possible verdict patterns, the probe fails to be surjective by construction, so no
liar is forced by counting alone. What Chapter 6 supplies is the observation that
the diagonal pattern `q ↦ !(read (enc q) q)` is a specific, nameable target, and a
probe that is expressive enough to be useful is expressive enough to come close to
it on a nonneglible fraction of queries. The quantitative statement is not "there
is a liar" but "the fraction of queries on which the probe is forced to be wrong is
bounded below by a quantity that grows with the probe's own coverage of verdict
patterns." A probe that covers more patterns, that is more expressive, has a larger
forced-error floor, not a smaller one. That monotonicity is the finite echo of the
exact theorem, and it is why sharpening a J-space probe past a point stops helping.
The exact statement is the `N → ∞`, `M → 2^N` corner of this, and the two agree in
the limit by design.

There is a temptation to read the finite bridge as a reassurance, as though the
idealization were the only thing standing between a J-space probe and completeness.
The monotonicity says the opposite. Progress toward the idealization, more
expressiveness, more coverage, more faithful mid-process readout, moves the finite
probe toward the regime where the floor is highest, not lowest. The direction the
interpretability program pushes is the direction in which the forced-error floor
rises. This is the same phenomenon the earlier chapters describe for output
verdicts, and the point of the chapter is that routing through J-space does not
alter its sign.

Third, the analytic half assumes continuity of the score and, for the width bound,
a Lipschitz constant. A probe that is deliberately discontinuous, that snaps its
verdict from safe to unsafe with no intermediate value, evades Theorem 8.17, but
it does so by giving up calibration in the sense Chapter 4 requires, and it then
falls to the diagonal half instead, since a discontinuous total exact verdict over
a self-describing space is still a reflective verdict. The two engines close each
other's escape routes. Continuity hands you to the intermediate value theorem, and
abandoning continuity hands you back to the diagonal. There is no third door in
between, which is the whole point of the two engines meeting in this space.

# Historical and bibliographic notes

The J-space construction is the interpretability work of 2026 that recovers a
transformer's global-workspace subspace from the Jacobian transport map
`Jℓ = E[∂h_final,t'/∂h_ℓ,t]` and reads it with the J-lens
`lens(h) = softmax(W_U · norm(Jℓ h))`. The empirical claims used in Remark 8.6,
that J-space is low-dimensional, disproportionately read and written, and load-
bearing for multi-step reasoning under ablation, are reported there. The
mathematics this chapter attaches to that construction is entirely from earlier in
the book: the diagonal and {lean}`no_reflective_verdict` from Chapter 1, the
trilemma readings from Chapter 3, the intermediate value argument from Chapter 4,
the quantitative geometry from Chapter 5, and the finite bridges from Chapter 6.
The Foundation development records the activation-space statement directly as
`jspace_readout_impossible` and `jspace_coupled_activation`, and proves it is the
same proof term as the hallucination and defense results; Theorem 8.14 above is
the core-Lean rendering of those. The reading of a Jacobian as a 1-jet, and hence
of J-space as a tangent space, is standard differential geometry; what is new is
only the use to which it is put, as the hypothesis that hands the construction to
the analytic engine.

The lineage of the individual moves is worth recording, because the chapter's
contribution is a reading rather than a new theorem. The diagonal is Lawvere's, by
way of Cantor, and its statement as the impossibility of a reflective verdict is
Chapter 1's. The intermediate value argument for connected question spaces is
Chapter 4's, resting on Mathlib's `IsPreconnected.intermediate_value2` in the
companion `HallucinationProofs` library, and the antipodal form that drops coverage
is the `HoF_08` variant. The Lipschitz width bounds and the basin geometry are the
`ManifoldProofs` development surveyed in Chapter 5. The correspondence between the
Boolean flip `(!·)` and the real complement `y ↦ 1 - y` is recorded directly in
`Foundation.F_04` and discussed in Chapter 4. What this chapter adds is the
observation that the J-space construction supplies, from its two defining
properties, exactly the two hypotheses those prior results need, so that the
existing machinery applies with no new mathematics. The move from an output verdict
to an internal readout, which looks like it should require a new argument, requires
none, and the demonstration that it requires none is the point.

A word on the broader interpretability literature the construction sits in. The
logit lens and its tuned variants read middle layers through the unembedding; the
sparse autoencoder program decomposes activations into overcomplete feature
dictionaries; the causal and circuit-level methods trace how information moves
between components. J-space is a derivative-based method in that family, and the
arguments here are indifferent to which family member is on the table. Any method
that (i) is expressive enough to be pushed toward surjectivity over a
self-describing query space, or (ii) reads a connected representation with a
continuous score, inherits the corresponding engine. The chapter's title says J-
space does not escape; the notes here record that nothing in its neighborhood does
either, and for the same two reasons.

# Exercises

**Exercise 8.1.** Prove in Lean that composing an encoder with a decoder on the
_left_ is also a no-escape result: given `enc : Q → J`, `post : Bool → Bool`, and
`read : J → Q → Bool` with `∀ g, ∃ p, (fun q => post (read (enc p) q)) = g`,
derive `False`. What does `post` model, and why does the argument not care whether
`post` is the identity, negation, or a constant?

**Exercise 8.2.** Instantiate {lean}`jspace_factoring` with `J := Unit`. The
resulting hypothesis says every verdict pattern over `Q` is realized by a single
representation. Explain in one paragraph why this is the most degenerate possible
probe, and why the theorem still refutes it. Relate the collapse to Example 1.3's
counting argument.

**Exercise 8.3.** The witness in {lean}`jspace_liar` depends on the choice of
preimage `p` in the surjectivity hypothesis. Show that if two distinct queries
both realize the diagonal pattern `fun q => !(read (enc q) q)`, then both are
coupled queries, and nothing in the proof selects one. Connect this to Exercise
1.7 and to the non-uniqueness of the boundary point in Theorem 8.17.

**Exercise 8.4.** Prove {lean}`c8_steering_no_escape` a second way, by exhibiting
`steer` and `enc` such that `steer ∘ enc` equals a single encoder `enc'`, and then
citing {lean}`jspace_factoring` on `enc'`. Conclude that steering is, from the
diagonal's point of view, just a choice of encoder.

**Exercise 8.5.** Using {lean}`bool_not_fpf` from Chapter 1, write a short proof
that the Boolean flip has no fixed point, and explain in prose how this single
fact is what makes both {lean}`jspace_liar` and the failure of the discrete side
of the equation `s(J v) = 1 - s(J v)` go through. Where does the real complement
`y ↦ 1 - y` differ, and why does it have a fixed point?

**Exercise 8.6.** Model a J-coordinate with a sparsity budget: define a predicate
on {lean}`c8_Coord` that holds when `terms` has length at most `k`. Show that
{lean}`c8_coord_no_escape` still applies when `enc` is required to land in the
budgeted coordinates, because the codomain is still a type. What does this say
about the hope that _sparse_ interpretability, specifically, might escape?

**Exercise 8.7.** (Analytic, prose.) State carefully the hypotheses under which
Theorem 8.17 gives a threshold point, and give an example of a score on J-space
that fails one hypothesis and has no threshold point. Which hypothesis does your
example break, and what does breaking it cost in the vocabulary of Chapter 4's
three conditions?

**Exercise 8.8.** (Analytic, prose.) Explain why convexity of J-space lets
Theorem 8.17 use a straight segment rather than the general preconnectedness
argument of Chapter 4. Then explain why the residual stream, treated as a finite
set of observed activations, does not admit the segment argument, and what Chapter
6 supplies in its place.

**Exercise 8.9.** Suppose the transport map `Jℓ` were _not_ linear, say a smooth
but curved map, so that J-space were a manifold rather than a subspace. State which
of the two engines still applies unchanged and which needs a new hypothesis. (Hint:
the diagonal never used linearity; the intermediate value theorem needs
connectedness, which a connected manifold still has.)

**Exercise 8.10.** Write the four-stage pipeline theorem: `enc : Q → A`,
`t₁ : A → J₁`, `t₂ : J₁ → J₂`, `read : J₂ → Q → Bool`, deriving `False` from
surjectivity of the composite. Then observe that your proof is
{lean}`no_reflective_verdict` applied to a longer lambda, and state the general
principle about pipeline depth this makes precise.

**Exercise 8.11.** Give the precise sense in which {lean}`c8_jlens_impossible` and
{lean}`no_reflective_verdict` are the same theorem, and check that
{lean}`c8_same_engine` proves it by `rfl`. Then explain why a `rfl` proof, rather
than a longer one, is the honest signal that no new mathematics entered when we
moved to the activation-space reading.

**Exercise 8.12.** (Design.) You are handed a deployed J-space probe and told to
reduce its coupled-query rate below a target. Using Theorem 8.12 and Remark 8.19,
argue whether the target is reachable by adversarial slack-removal alone, and
describe what additional information about the deployment, in the sense of Chapter
5 and Chapter 7, you would need to decide. What would you measure first?

**Exercise 8.13.** (Open-ended.) Chapter 1's closing exercise asked what a system
satisfying _both_ engines' hypotheses at once would look like. J-space is such a
system: self-applicable and connected. Speculate on whether there is a
representation that is connected but genuinely _not_ self-applicable, so that only
the analytic engine reaches it, and describe what a model would have to give up
about its own expressiveness to live there. Is that trade one any useful model
could make?

**Exercise 8.14.** (Harder, prose.) The chapter claims the Jacobian is "the
linearization of a self-applicable map" and the liar activation is "the fixed
point of that linearization." Make this precise for the affine model of Example
8.5: identify the self-applicable map, write its linearization, and locate the
fixed point of the complement-controlled score on `im(A)`. Then say exactly which
step fails to have a Boolean analogue, and why that failure is the content of the
two engines meeting.

**Exercise 8.15.** Consider a three-valued readout `read : J → Q → Three` where
`Three` has values `yes`, `no`, and `unknown`, and let the flip send `yes` to
`no`, `no` to `yes`, and fix `unknown`. Show that the diagonal argument does not
produce a contradiction, and identify the fixed point of the flip. Then argue in
prose that this is not an escape from the trilemma but the "drop coverage"
relaxation of Chapter 7, and connect your fixed point to Remark 8.4a and the
abstention discussion. What has the probe given up, and on which queries does it
give it up?

**Exercise 8.16.** (Empirical, prose.) Remark 8.21 distinguishes a structural
floor, whose residual set churns as you patch, from a resource-limited error, whose
residual set is stable. Design an experiment on a real J-space probe that would
distinguish the two, and say what result would count as evidence for each. Which of
{lean}`jspace_liar` and Theorem 8.17 does your experiment probe, and could a single
experiment probe both at once?

**Exercise 8.17.** (Synthesis.) The section "What an escape would have to look
like" lists three demands an escaping representation would have to meet, and argues
they are jointly incompatible with a useful internal verdict. Pick one of the three
and construct the most plausible representation you can that meets it, then check
which of the other two it must then violate. Conclude by stating, in one sentence,
which property of J-space you had to destroy to satisfy your chosen demand.
