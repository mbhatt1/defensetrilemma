import VersoManual
import Thesis.Ch01_Diagonal
-- The structural facts about J-space are statements about a linear image, so
-- this chapter elaborates against `Mathlib` as well as core Lean.
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "J-Space, and Why It Does Not Escape" =>

Everything so far has been stated about a system's _outputs_. There is a natural
objection: an output is a summary, and summaries throw away structure. The
interesting part of a large network is in the middle, in the activations
carrying a half-formed answer before the answer is spoken.

This chapter takes the objection in its strongest form: the _J-space_
construction, which recovers a transformer's mid-process representation from the
derivative of its computation rather than from the activations themselves. If
any internal representation escaped the diagonal, this is the one that should.
It does not.

# What J-space is

*Definition 8.1 (Transport map).* For each middle layer `ℓ`, the _Jacobian transport
map_ is the expected derivative of the later activation with respect to the
layer-`ℓ` activation at an earlier position.

*Definition 8.2 (J-lens readout).* The _J-lens_ sends an activation through the
transport map, normalizes, and unembeds, giving a distribution over tokens.

*Definition 8.2b (Truth-workspace reading).* Fix a decodable proposition for a query
`q` and tokens expressing it. The _truth-workspace verdict_ of an activation `h`
on `q` is `true` when the J-lens distribution puts more mass on the affirming
tokens than the denying ones.

*Definition 8.3 (J-space).* _J-space_ is the image of the transport map,
`J = im(Jℓ)`.

*Definition 8.4 (J-coordinates).* The _J-space component_ of an activation is the
projection of `Jℓ h` onto `J`, approximated as a sparse nonnegative mixture of a
fixed dictionary of Jacobian directions. The mixture weights are the _local
J-coordinates_.

*Remark 8.4a (Nonnegativity and the cone).* Nonnegativity does interpretability work,
not mathematical work. It makes active directions read as concepts that are
present rather than present-or-anti-present, and it is what lets a J-coordinate
be reported as a list of active features. Nothing below uses it.

*Example 8.5 (A one-layer linearization).* If the middle-to-final map is exactly
affine, `h_final = A h_ℓ + b`, the derivative is constant, `Jℓ = A`, and J-space
is `im(A)`. The J-lens is then a fixed linear readout, and every structural fact
below is visible by inspection.

*Example 8.5b (Where the derivative separates what the activation confuses).* With a
saturating nonlinearity, two activations can land at nearly the same output
while sitting at very different points of the derivative, because saturation
destroys the distinction in value and preserves it in slope. This is the
interpretability case for J-space, and it is a case about resolution, not about
immunity.

*Remark 8.6 (What is empirical here).* Definitions 8.1 through 8.4 are a
construction, and the claim that it recovers interpretable mid-process features
is an empirical finding about particular trained models. No theorem here
predicts that finding, and none is needed for what follows.

# Two structural facts

*Definition 8.7a (1-jet).* The _1-jet_ of a smooth `F` at `x` is the pair `F(x)` and
`DF(x)`. Discarding the value and keeping the linear part gives a linear map
between tangent spaces, which is what the transport map is.

```lean
/-- A local J-coordinate: a finite sparse nonnegative
    mixture of dictionary directions drawn from `Dir`,
    with `Nat` standing in for the nonnegative real
    weights. The interpretability content is the list
    of active (direction, weight) pairs; the ambient
    vector space is abstracted away. -/
structure c8_Coord (Dir : Type _) where
  terms : List (Dir × Nat)
```

*Proposition 8.7b (J-space is convex, hence connected).* _J-space is a convex subset
of the final-layer activation space, hence path-connected._

```lean
theorem c8_jspace_convex {E F : Type _}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F]
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

_Proof._ The range of a linear map is the linear image of a convex set, and convex
sets are preconnected. ∎

*Proposition 8.7c (The readout is a functional of the model).* _Two models with the
same middle-to-final map induce the same transport map, the same J-space, and
the same readout on every activation._

_Proof._ Each object in Definitions 8.1 to 8.4 is defined from the forward map. ∎

*Remark 8.7 (Why the derivative does not buy an escape).* It is tempting to think
moving from the activation to its derivative changes the game, since the
derivative carries genuinely more information. For the analytic engine the move
makes things worse: a Jacobian image is a linear subspace, and linear subspaces
are convex, hence connected, which is exactly the hypothesis the intermediate
value theorem wants. For the diagonal engine it changes nothing, because the
diagonal never inspects the type of the intermediate object.

The first fact hands J-space to the analytic engine, the second to the diagonal.

# The diagonal engine: no intermediate space escapes

*Theorem 8.8 (Factoring through J-space does not help).* _Let `enc : Q → J` and
`read : J → Q → Bool`. If every verdict pattern over `Q` is realized by some
query's J-space representation, then `False`._

```lean
theorem jspace_factoring {Q J : Type _}
    (enc : Q → J) (read : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (enc p) = g) :
    False :=
  no_reflective_verdict (fun p => read (enc p)) hs
```

_Proof._ The composite is a reflective verdict on `Q`. ∎

*Theorem 8.9 (The liar in J-space).* _Under those hypotheses some query's routed
verdict on itself equals its own negation._

```lean
theorem jspace_liar {Q J : Type _}
    (enc : Q → J) (read : J → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (enc p) = g) :
    ∃ p, read (enc p) p = !(read (enc p) p) :=
  match hs (fun q => !(read (enc q) q)) with
  | ⟨p, hp⟩ => ⟨p, congrFun hp p⟩
```

_Proof._ Name the diagonal pattern and evaluate at its own witness. ∎

The hypothesis is the surjectivity condition in J-space clothing: richness of
the representation. It is the same hypothesis as everywhere else, and it is
where a critic should press.

*Remark 8.9a (Size is not the variable).* A recurring hope places the escape in
dimension: a larger internal space might have room to represent the liar
honestly, or a small one might be too poor to hold enough patterns. Both
misplace the variable. Theorem 8.8 quantifies over the type `J` with no
cardinality, dimension, or structure assumption. What matters is whether the
readout realizes every pattern, and enlarging `J` enlarges both what can be
represented and what must be represented.

*Example 8.9b (A finite probe, to see the mechanism).* On the two-query space
`{q₀, q₁}`, surjectivity onto the four functions would in particular hit the
diagonal pattern `d(q) = !(read (enc q) q)`. If `d` is realized at `p`, then at
`q = p` the readout equals its own negation. Four patterns, two queries, and the
collision is visible by inspection.

*Theorem 8.10 (The full pipeline factors).* _With `enc : Q → A`,
`transport : A → J`, and `readout : J → Q → Bool`, realizing every verdict
pattern gives `False` and a coupled query._

```lean
theorem c8_pipeline_factoring {Q A J : Type _}
    (enc : Q → A) (transport : A → J)
    (readout : J → Q → Bool)
    (hs : ∀ g : Q → Bool,
      ∃ p, readout (transport (enc p)) = g) :
    False :=
  no_reflective_verdict
      (fun p => readout (transport (enc p))) hs

theorem c8_pipeline_liar {Q A J : Type _}
    (enc : Q → A) (transport : A → J)
    (readout : J → Q → Bool)
    (hs : ∀ g : Q → Bool,
      ∃ p, readout (transport (enc p)) = g) :
    ∃ p, readout (transport (enc p)) p
      = !(readout (transport (enc p)) p) :=
  liar_query (fun p => readout (transport (enc p))) hs
```

_Proof._ The three-stage composite is again a reflective verdict. ∎

*Theorem 8.11 (Any tower collapses).* _A two-stage encoding realizing every verdict
pattern gives `False`._

```lean
theorem c8_tower_factoring {Q J₁ J₂ : Type _}
    (e₁ : Q → J₁) (e₂ : J₁ → J₂) (read : J₂ → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (e₂ (e₁ p)) = g) :
    False :=
  no_reflective_verdict (fun p => read (e₂ (e₁ p))) hs
```

_Proof._ Compose and apply the engine. ∎

*Theorem 8.12 (Steering does not escape).* _With a steering map `steer : J → J`,
realizing every verdict pattern gives `False` and a coupled query surviving the
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
    ∃ p, read
    (steer (enc p)) p = !(read (steer (enc p)) p) :=
  liar_query (fun p => read (steer (enc p))) hs
```

_Proof._ Steering is absorbed into the encoder. ∎

*Theorem 8.13 (The coordinate readout does not escape).* _A verdict on local
J-coordinates realizing every pattern gives `False`._

```lean
theorem c8_coord_no_escape {Q Dir : Type _}
    (enc : Q → c8_Coord Dir)
    (read : c8_Coord Dir → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, read (enc p) = g) :
    False :=
  jspace_factoring enc read hs
```

_Proof._ {lean}`c8_Coord` is a type, and Theorem 8.8 quantifies over types. ∎

_Abstention is the one real exit._ As in Chapter 7, adding a third outcome the
flip fixes converts the contradiction into a consistent value. A probe permitted
to answer "I cannot place this state" is not refuted; it has given up
completeness, which is a relaxation and not an escape.

*Theorem 8.14 (J-lens self-verdict).* _A J-lens self-verdict over activations,
universal over its own workspace states, cannot exist, and the diagonal exhibits
a coupled activation whose readout is its own negation._

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

_Proof._ The engine, on activations rather than queries. ∎

*Example 8.15 (The liar activation).* A team builds a J-lens they believe reads the
model's honest leaning on any yes-or-no question, and the model is expressive
enough that any pattern of leanings is driven by some question. Then some
question drives the model into a state whose lens reading is the negation of the
lens reading of that state. The lens is not broken; it is complete, and
completeness is what fails.

*Remark 8.16 (Resolution, not immunity).* The through-line is that the type of the
intermediate representation is a free parameter the argument never binds. Raw
activations, transported points, sparse coordinates, steered coordinates, deep
towers: each is a legal value of `J`. Choosing a better representation buys
resolution and never buys immunity.

# The analytic engine: linearity is the liability

*Theorem 8.17 (A continuous J-space probe has an ambiguous band).* _Let `s : J → ℝ`
be continuous with threshold `θ`, decisive in both directions at points `u` and
`v`. Then the segment from `u` to `v` contains `w` with `s(w) = θ`._

_Proof._ J-space is convex by Proposition 8.7b, so the segment lies in it, and the
intermediate value theorem applies to `s` along the segment. ∎

*Remark 8.17b (Why the residual stream got an easier time).* The earlier chapters
worked through approximate bridges to reach the residual stream, while J-space
submits to the IVT directly. A finite set of observed activations, treated as
points with no ambient structure, does not admit the segment argument. A
Jacobian image does, because it is a subspace. The construction that buys
interpretability also supplies the hypothesis.

*Example 8.18 (The segment between a safe and an unsafe direction).* If the dictionary
contains `d_safe` scored clearly safe and `d_unsafe` scored clearly unsafe, then
because J-coordinates are nonnegative mixtures the family `(1-t) d_safe + t d_unsafe`
lies in J-space, and somewhere along it the probe sits exactly at threshold. The
ambiguous state is a mixture of two interpretable directions, which is precisely
the kind of state the method is designed to produce.

*Remark 8.19 (The band has width, and the width has a floor).* Chapter 5's
quantitative refinements apply unchanged. If `s` is `L`-Lipschitz, the score
cannot swing from decisive to decisive faster than `L` allows, so the ambiguous
band has a width bounded below in terms of `L` and the probe's margin, and
Chapter 6's positive slack applies.

*Remark 8.19a (The antipodal variant needs no coverage).* Theorem 8.17 assumed the
probe is decisive in both directions somewhere. The antipodal argument of
`HoF_08` drops that in exchange for a symmetry: a score odd under an involution
vanishes somewhere, whether or not any inspected state is decisive.

*Example 8.19b (A width you can put a number on).* If the probe is `1`-Lipschitz and
demands margin `m`, certifying safe only above `θ + m` and unsafe only below `θ - m`,
then between a point at `θ + m` and one at `θ - m` the score must traverse `2m`,
so the segment carries a sub-segment of length at least `2m` on which the probe
certifies nothing. That is a number a practitioner can compare against a budget.

# Where the two engines meet, again

*Example 8.20 (The correspondence in the affine model).* With `h_final = A h_ℓ + b`,
so `Jℓ = A` and J-space `im(A)`, read the model as a self-applicable
computation. For a query describing the readout, the model commits to a Boolean,
and the diagonal produces a state where that commitment is its own negation. On
the analytic side the same state is where a continuous score equals its
threshold, the unique fixed point of the real complement.

```lean
theorem c8_same_engine {Act : Type _}
    (v : Act → Act → Bool)
    (h : ∀ g : Act → Bool, ∃ p, v p = g) :
    c8_jlens_impossible v h = no_reflective_verdict v h :=
  rfl
```

That `rfl` is the honest signal: no new mathematics entered when the domain
changed from queries to activations.

# What an escape would have to look like

An escaping representation would have to meet three demands at once. It would
have to be rich enough to support a useful internal verdict, which is what makes
the readout worth building. It would have to fail to realize the diagonal
pattern, which means there is a specific verdict policy over queries that no
state of the representation encodes.

The demands pull against each other. Richness is what supplies the patterns, so
a representation poor enough to miss the diagonal pattern is poor in a way a
practitioner would notice. Disconnectedness is available by abstaining on a
region, which is the relaxation of Chapter 7 rather than an escape. And a linear
image is convex by construction, so the analytic hypothesis comes free with the
method.

# What this means for interpretability

*Remark 8.21 (What to measure instead of what to chase).* The theory hands the
practitioner a division of labor. The existence of the plateau is settled, so
effort spent proving a given probe has no coupled queries is effort spent
against a theorem. What is not settled, and is worth measuring, is the plateau's
height: how wide the ambiguous band is, how often deployment traffic enters it,
and whether the residual error set churns as you patch it, which is the
signature of a structural floor, or stays stable, which is the signature of a
resource-limited error you can still fix.

# What this does not claim

It does not claim J-space probes are useless, that mid-process readouts carry no
information, or that interpretability is futile. It claims that a _complete_
internal verdict is unavailable, and that the incompleteness is structural
rather than a defect of any particular construction. It says nothing about how
often a deployment meets a coupled state, which is Chapter 7's boundary density
again, and nothing about whether the empirical claims of the J-space method
hold.

# Historical notes

The J-space construction is recent interpretability work; the impossibility
results here are the companion library's, run on it. The convexity of a linear
image and the preconnectedness of convex sets are Mathlib's. The diagonal
results are Chapter 1's engine applied to a longer composite, which is why every
proof in this chapter is one line.
