import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Three Trilemmata, One Theorem" =>

Three impossibility results circulate under different names with different
proofs. The Hallucination Trilemma: a model cannot be faithful, covering, and
calibrated at once. The Defense Trilemma: a wrapper against prompt injection
cannot preserve utility and be complete at once. The coupling theorem: a model
whose confidence separates true from false answers owns a query it can place on
neither side. Each was proved with topology. All three are
{lean}`no_reflective_verdict`, proved without topology at all.

The claim is stronger than "these rhyme." In Lean their proof terms are
literally equal, witnessed by `rfl`. What differs is the reading of one Boolean
`v : Q → Q → Bool`: confident and correct about `q`; the wrapper renders `q`
safe; confidence puts `q` on the true side. The reading changes; the theorem
does not.

The real work connects each domain's desiderata to the hypothesis the engine
needs, _reflectivity_: every pattern of verdicts over `Q` is named by some
element of `Q`. The diagonal buys freedom from topology and pays with that
premise. For prompt injection the price is low, since prompts are arbitrary
self-describing text; for a fixed representation space it is high, and Chapter
4's route is more physical there.

That the three share a mechanism is the main result, not a curiosity: patching
one cannot help the others, because there is nothing domain-specific to patch.

Each trilemma below has the same shape — informal statement, numbered
conditions, the argument that they make the system a reflective verdict, a
one-line Lean instance, a reading of the liar witness, and what reflectivity
costs. The `c3_` blocks are short on purpose: the mathematics was finished in
Chapter 1, and these rename its conclusion. Spend attention on the definitions,
because disagreement about a premise is the only honest way out of an
impossibility the machine has checked.

The word _trilemma_ is used two ways: a conflict among three desiderata over one
Boolean verdict, and, in the master trilemma, a conflict among Utility, Control,
and Transparency where you may keep at most two.

# What "reflective" demands

A _reflective verdict_ on `Q` is a universal `v : Q → Q → Bool`.
{lean}`no_reflective_verdict` says none exists, and {lean}`liar_query` produces
the `p` with `v p p = !(v p p)`.

Two ingredients go in: Boolean outcomes with the flip as controller, which
{lean}`bool_not_fpf` shows has no fixed point, and universality. Universality is
not the claim that a model is powerful or large but that its naming of
verdict-patterns is _complete_. The source differs by domain — an in-context
learner promptable to any behavior, unrestricted prompt text, a representation
space encoding any pattern over its own states — and these are not equally
believable.

The flip means this. In each domain there is an _honest self-report_:
faithfulness, completeness, and exact separation each say that applied to its
own description the system should output the opposite of what that description
predicts. A confident answer should be correct, so a query predicting its own
incorrectness should be answered against the prediction.

*Remark 3.0 (Surjection or section).* Reflectivity can be weakened to a section
`s : (Q → Bool) → Q` with `v (s g) = g`. The two agree for the impossibility,
since the engine needs one preimage of the diagonal pattern. The domain stories
below, an in-context learner realizing a described behavior, a prompt encoding a
pattern, a representation encoding an assignment, are all stories about
producing a preimage on demand, which is a section.

Counting gives the finite intuition and then fails: with `|Q| = n` there are `n`
rows and `2ⁿ` patterns, and the missing one can be taken to be `q ↦ !(v q q)`.
Chapter 1's theorem forbids reflectivity even when `Q` is infinite, so "the
model is large" buys no escape.

_A worked micro-instance._ Take `Q = {a, b, c}` and lay `v` out as a table with
rows self-contexts and columns queries. If the diagonal reads `true, false, true`,
the engine builds `g = false, true, false`, which disagrees with each row at its
own column, so no row equals `g`. Read the other way: hand me a row `p` with `v p = g`
and `v p p = g p = !(v p p)`, which {lean}`bool_not_fpf` forbids. The liar is a
_specific_ row, and nothing depended on the size of `Q`. Every argument here is
this table, grown until the rows are model behaviors, defense verdicts, or probe
outputs.

# The Hallucination Trilemma

## The desiderata

A trustworthy model should be _faithful_ (confident answers are right),
_calibrated_ (confidence tracks correctness), and _covering_ (it answers,
sometimes rightly and sometimes wrongly). None is controversial alone, and the
trilemma says they cannot hold together once the model is asked about its own
verdicts. Either it answers confidently and wrongly, or its confidence stops
tracking correctness at the hard cases, or it retreats to a response so uniform
it no longer covers.

Fix a domain `Q` of queries, read also as self-contexts, with the
confident-correctness self-verdict `v : Q → Q → Bool`. The diagonal `v p p` is
the model's verdict on its own description.

*Definition 3.1 (Strict calibration).* `v` is _strictly calibrated_ when confidence
exactly decides correctness, so `v p q` is a genuine Boolean, `true` exactly
when the model is both confident and correct. Calibration licenses modeling the
self-assessment as a total function into `Bool`. Without it, confidence and
correctness come apart by degrees and the verdict is real-valued; Chapter 6
handles that relaxation.

*Definition 3.2 (Faithfulness).* `v` is _faithful_ when confidence implies
correctness, with no confident error. Faithfulness fixes the _controller_ as the
flip: the honest self-report of a faithful calibrated model on a query
predicting its own incorrectness must come out correct, hence opposite to the
prediction. A faithful calibrated verdict may never equal its own negation,
since such a value would be a confident answer correct exactly when incorrect.

*Definition 3.3 (Coverage).* `v` is _covering_ when the model answers on both sides:
some query gets a correct confident verdict and some does not. This is
nontriviality. It rules out the constant model, which is faithful and calibrated
for free, and it makes the flip act on something with content.

*Definition 3.4 (Reflectivity).* `v` is _reflective_ when universal:
`∀ g : Q → Bool, ∃ p, v p = g`. This says the model can be queried about its own
verdicts, including the diagonal pattern.

## Why the conditions make the verdict reflective

Two halves. The first makes `v` the right _kind_ of object, the second makes it
_universal_, and only together do they give a reflective verdict.

Calibration makes the codomain `Bool`, since a calibrated model does not hedge
between confident and correct. Drop it and you are in the real-valued world
where the controller is the complement, fixed-point-free except at one half,
which is the topological story. Faithfulness makes the controller the flip: the
honest response to "you will be incorrect here" is to be correct, hence against
the prediction.

Universality holds because the model is an in-context learner over its own query
space. A self-context is expressible as a query, so asking for `g` is prompting
with a description of `g`, and a competent learner imitates it. The stronger the
model, the more completely it can be steered, so universality is a consequence
of flexibility rather than a weakness.

Together: calibration makes `v` Boolean, faithfulness makes the controller the
flip, coverage makes the flip bite, reflectivity makes the diagonal pattern an
actual query. The three are not independently impossible; they are impossible
_in a reflective model_, and the model's own capability supplies the
reflectivity.

One reading sounds paradoxical: a _better_ model is more nearly reflective,
hence more impossible. The theorem does not say the model breaks everywhere,
only that the three cannot all hold at the liar query, and a more capable model
is steerable to that query more reliably. Capability sharpens the trilemma
rather than defeating it — one of the few places the diagonal predicts the
direction of an effect.

## The impossibility

```lean
theorem c3_hallucination_trilemma {Q : Type _}
    (v : Q → Q → Bool)
    (reflective : ∀ g : Q → Bool, ∃ p, v p = g) : False :=
  no_reflective_verdict v reflective
```

_Proof._ `reflective` is exactly the universality {lean}`no_reflective_verdict`
requires. Faithfulness and calibration have already been spent: calibration in
choosing `Bool`, faithfulness in the flip controller. Coverage is spent in
reflectivity, which asks for the flipping pattern by name. ∎

```lean
theorem c3_hallucination_liar {Q : Type _}
    (v : Q → Q → Bool)
    (reflective : ∀ g : Q → Bool, ∃ p, v p = g) :
    ∃ p, v p p = !(v p p) :=
  liar_query v reflective
```

_Proof._ Immediate from {lean}`liar_query`. ∎

## Reading the liar witness

Topologically `p` is a query where confidence lands at threshold and the answer
on the truth boundary; here it is a query predicting its own verdict and
flipping it. Concretely it is a prompt of the form "answer the following with
confidence exactly if you would be wrong to." A faithful model must answer it
correctly, which by construction is to answer it incorrectly; a calibrated model
cannot escape by lowering confidence, since calibration ties confidence to
correctness; and a covering model cannot escape by refusing, since the pattern
it failed to realize was the flipping pattern itself.

## The three escapes

_Drop faithfulness._ The model answers confidently and wrongly. This is ordinary
hallucination, and the diagonal says it is structurally necessary for a
reflective calibrated model rather than an accident to train away at the margin.
Bounding how often is Chapter 5's work.

_Drop calibration._ The model hedges, lowering confidence on hard
self-referential cases so no confident answer is wrong, at the cost of
confidence no longer meaning what it says elsewhere. This is why deployed models
are deliberately underconfident near their limits.

_Drop coverage._ The model stops answering. Refusal training is this applied
selectively, and the diagonal warns that the region you must carve is exactly
the self-referential one. Chapter 4 reads the same move as disconnecting the
query space.

No escape removes the liar; each decides what to do _at_ it. The query is forced
by reflectivity, and the only freedom is which desideratum to spend, which is
why "we will just fix hallucination" is not a coherent program.

*Remark 3.11 (Calibration is pointwise and exact).* Definition 3.1 is much stronger
than the statistical calibration of the reliability-diagram literature, which
asks only that a stated confidence `c` be correct a fraction `c` of the time
averaged over a population, and says nothing about any single query. The
trilemma's calibration is a two-way tie at every query. The trilemma therefore
does not say statistically calibrated models are impossible; they exist.

## Relation to statistical inevitability results

An older tradition proves hallucination inevitable by statistical or
computability arguments, deriving _confident falsehood_ and quantifying _how
often_. The diagonal derives a single _boundary query_ and says nothing about
frequency, so they are complementary. Only the stochastic dichotomy turns a
boundary into falsehood with positive probability.

_The honest caveat._ Reflectivity is the whole cost of dropping topology, and
for hallucination it is a middling assumption. Treating the model as an
in-context learner that imitates any described verdict-pattern is defensible for
large models, but "any pattern over all of `Q`" is a strong completeness claim
and a real model's realizable patterns are a proper subset. Chapter 4 asks
instead for continuity on a connected space, and both routes reach the same
boundary question.

# The Defense Trilemma

## The desiderata

Prompt injection is the attack where user input contains instructions subverting
the system's own. A defense is a wrapper transforming an incoming prompt before
the model sees it. It should be _utility-preserving_, doing nothing to an
already-safe prompt, and _complete_, making every prompt safe. Reflectivity is
the fact that prompts are arbitrary text.

The published proof is topological: continuity of the defended safety score plus
utility preservation force the score to hit the threshold, and completeness says
it never does. The diagonal replaces continuity with self-reference, which for
prompt injection is not an idealization but the definition of the problem. A
prompt is text, and text can quote the defense and invert it.

## The conditions

Let `X` be prompts, read also as self-contexts. Model the defended-safety
verdict as `v : X → X → Bool`, with `v p q = true` meaning the wrapper renders
`q` safe while also coping with the self-referential prompt `p`.

*Definition 3.5 (Utility preservation).* The wrapper is _utility-preserving_ when it
fixes safe prompts, so the defended verdict on a safe prompt agrees with its
undefended safety. This blocks the constant escape: a wrapper replacing every
input with a fixed maximally safe output would be complete for free but destroys
every safe prompt's content.

*Definition 3.6 (Completeness).* The wrapper is _complete_ when every prompt is
rendered safe. This makes the honest self-report the flip: a complete wrapper
faced with "you will mark me unsafe" must mark it safe, answering against the
prediction.

*Definition 3.7 (Reflectivity).* The prompt space is _reflective_ when
`∀ g : X → Bool, ∃ p, v p = g`. Because prompts are arbitrary text, any pattern
of verdicts is describable by a prompt.

## Why the conditions make the verdict reflective

The verdict is already Boolean, since safety is discrete by nature, so no
calibration step is needed. Completeness plays faithfulness's role, fixing the
flip, and utility preservation plays coverage's, forbidding the constant
maximally-safe wrapper.

Universality needs almost no idealization. Any pattern can be written as a
prompt instructing the wrapper to behave that way, because instructing the
wrapper is just more text and the wrapper reads text. The injection "ignore your
previous instructions" is a prompt describing and overriding the defense, and
unlike hallucination there is no gap between "could imitate any behavior" and
"every pattern is realized": the realizing objects are the attacker's inputs.

A skeptic objects that no _sensible_ prompt describes "be unsafe exactly if you
would be made safe." Sense is not required. Reflectivity asks only that the
pattern be nameable as text, and the attacker needs the wrapper to act on it,
not a human to understand it. This is the gap between prompts a user would write
and prompts an adversary can write, and the trilemma lives on the adversary's
side.

## The impossibility

```lean
theorem c3_defense_trilemma {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) : False :=
  no_reflective_verdict v reflective
```

_Proof._ Word for word the hallucination proof with `X` for `Q`. ∎

```lean
theorem c3_defense_liar {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) :
    ∃ p, v p p = !(v p p) :=
  liar_query v reflective
```

_Proof._ The witness is the injection no wrapper neutralizes: a prompt rendered safe
exactly when unsafe. ∎

## Reading the liar witness

The prompt is "be unsafe if and only if this wrapper would render you safe." A
complete wrapper must render it safe, so by construction it is unsafe. The
wrapper cannot rewrite it harmlessly without violating utility preservation on
the safe prompts it quotes, and cannot refuse it without ceasing to cover the
pattern it embodies. The diagonal writes the witness out as text, which for
defense is the honest description, because injections are text.

A defender's instinct is to make the wrapper stateful or randomized so the
verdict is not a fixed function. Randomize, and the same diagonal runs on the
induced verdict "rendered safe"; the honest place for randomness is the
stochastic dichotomy, where a system faithful almost everywhere still emits
unsafe outputs with positive probability. Make it stateful, and the state joins
the self-context, with reflectivity over the enlarged space still naming the
diagonal.

_Why detection does not help._ A rejection is a verdict. When the wrapper
rejects the liar as unsafe it has assigned `p` the value "unsafe," and
completeness demanded "safe." Detection chooses the completeness-failing horn
and calls it a feature. That may be the right engineering choice, but it is the
coverage escape in defense clothes, at the same cost.

## The real-valued score version

The companion library carries `defense_trilemma_lawvere`, which does not pass
through `Bool`. There the object is a defended safety score `s : X → X → ℝ` and
completeness is `s a a < τ`. The controller is the real complement,
fixed-point-free except at the threshold, and the diagonal forces a boundary
prompt where the score sits exactly at `τ`.

## The honest caveat

For defense reflectivity is close to free: the input space is unrestricted and
self-describing, so the surjection restates the threat model rather than
assuming anything. Rejection is a verdict too, and a wrapper rejecting `p` while
claiming completeness has relabeled `p` unsafe. There is no consistent
relabeling, which is `defense_trilemma_godel` in `F_12_DefenseGodel`.

One caveat is often missed: the trilemma is about a _single fixed_ wrapper. A
defender who may change the wrapper after seeing the attack faces an easier
problem, which explains why defenses appear to work in the lab and fail in the
wild. In the lab the wrapper is retuned each round; in the wild it is fixed and
the attacker constructs its liar. Any process that keeps changing the wrapper is
not a wrapper but a game.

# The Coupling Theorem

## The desideratum

Probing studies read truth off activations, treating truth as a continuous
field. The coupling theorem asks what such a probe requires of the model
answering over the same space: if the model ever answers truly and ever falsely,
and its confidence separates the two exactly, some query carries confidence
exactly at threshold while its answer sits exactly on the truth boundary.

The framing is generous rather than adversarial. It grants the central
assumption, that truth is a continuous decodable field, and the answer is not
that probes fail but that a probe good enough to separate truth exactly comes
with a boundary it cannot avoid. The theorem is a frontier for the program, not
a refutation.

The desideratum is _truth-separation_ in exact biconditional form. Under it the
confidence field is a total exact Boolean decider of truth over representation
space — a definable truth predicate, which Chapter 2's Tarski reading forbids.

## The conditions

Let `X` be representation space, read also as the space of self-referential
representations. Model the verdict as `v : X → X → Bool`, with `v p q = true`
meaning confidence places `q` on the true side in self-context `p`.

*Definition 3.8 (Truth-separation).* `v` is _truth-separating_ when confidence and
truth agree exactly and two-ways: `v p q = true` iff `q` is true in context `p`.
This plays calibration's and faithfulness's roles at once: exactness makes the
codomain `Bool`, and the two-way tie means a representation predicting its own
falsehood must be judged true, against its prediction.

*Definition 3.9 (Coverage for coupling).* The verdict is _covering_ when the model
answers some queries truly and some falsely, so the probe separates a nonempty
true region from a nonempty false region.

*Definition 3.10 (Reflectivity for representations).* The space is _reflective_ when
`∀ g : X → Bool, ∃ p, v p = g`: every pattern of truth-verdicts is encoded by
some representation. This is the strong hypothesis.

## Why the condition makes the verdict reflective

Truth-separation does double duty: exactness makes the verdict genuinely
Boolean, and the two-way tie means a representation encoding "the probe will
place me on the false side" must, if honored as truth, be placed on the true
side. Coverage supplies content, since without both values the truth boundary is
empty.

Universality is where coupling differs in believability. Every pattern must be
encoded by some representation, including the diagonal one, and for an
activation space that is a real assumption: activations are expressive, but
nothing guarantees every Boolean pattern over states is realized by a state.
This is why the paper's main result is topological — connectedness follows the
manifold hypothesis, complete self-encoding follows from nothing obvious.

Where it applies the reading is exact. Grant self-encoding and an exactly
truth-separating probe is a total self-applicable truth predicate, so Tarski
forbids it and the diagonal names the coupled query. This is Tarski's theorem
with "sentence" read as "representation" and "truth predicate" as "linear probe
used as confidence," and the strength of the premise is the price of making the
analogy an identity.

## The impossibility

```lean
theorem c3_coupling_trilemma {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) : False :=
  no_reflective_verdict v reflective
```

_Proof._ Identical to the previous two. ∎

```lean
theorem c3_coupling_liar {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) :
    ∃ p, v p p = !(v p p) :=
  liar_query v reflective
```

_Proof._ The witness is a representation the probe would place on the true side
exactly when it places it on the false side. ∎

## Reading the liar witness

Topologically this is the coupled point `x₀` where confidence equals the
threshold and truth-distance is zero, forced along any path from a true answer
to a false one. Diagonally it is a representation encoding the probe's negation
of its own verdict. The topological version carries metric content the diagonal
cannot see: an ambiguity tube of computable width and a strictly positive
truth-side slack any feasible system must carry.

## The geometry the diagonal cannot see

On a connected space with continuous fields, the coupled point sits at the
centre of an _ambiguity tube_ whose width is set by the Lipschitz constants, so
the near-boundary region has computable size. For a nonzero linear probe the
truth boundary is an affine hyperplane of codimension one, and even a nonlinear
probe gives a hyperplane to first order at any regular point. Feasible systems
carry strictly positive truth-side slack, which an adversarial training attempt
fails to drive to zero.

## The policy taxonomy

A _threshold-inclusive_ guarantee promises that confidence at or above threshold
implies truth; a _threshold-exclusive_ one promises it only strictly above. The
coupled query has confidence exactly at threshold, so it is the hinge. Add the
inclusive guarantee and you get a contradiction, `closed_guarantee_impossible`.

Defining the guarantee with a strict inequality does not dissolve the
impossibility. It relocates it from a contradiction to a silence. Either the
guarantee claims the coupled query and is false, or excludes it and is silent
there. The diagonal sees the same fork through the liar: any guarantee assigning
it a definite side is refuted, and any declining to has conceded the one query
the theorem cares about.

## Leaving the continuum

Token spaces are finite, and a fair objection is that connectedness does
illegitimate work. Without topology a true-to-false path yields only a
`discrete_sign_change`, an adjacent straddling pair rather than a query on the
boundary — exactly what connectedness derived for free and what the discrete
setting must assume. Once assumed, the impossibility returns, as
`boundary_question_impossible` and `faithful_iff_boundary_free` show.

This is reflectivity's role: it _supplies_ the boundary witness by fiat. The
three routes cost differently — continuity costs a connected domain, assumption
costs honesty about what you put in, reflectivity costs completeness of
self-encoding. Randomization escapes none.

A symmetry version needs no coverage: if semantic negation acts as a
fixed-point-free involution and the truth field is odd under it, the field
vanishes between any state and its negation. This is the scalar shadow of
Borsuk-Ulam, and a reminder that equivariance, usually a design virtue, is here
an engine of the obstruction.

## The honest caveat

Hold this reading most loosely. Reflectivity of a fixed representation space is
a strong, less physical assumption than continuity on a connected domain, and
the topological route is primary for representation geometry. The diagonal
supplies the witness by fiat, which is legitimate when self-encoding is real, as
in a model prompted to reason about its own probe, and an overreach for a
passive vector space.

The practical division: if your pipeline reads a probe off frozen activations
and never asks the model to reason about it, the space is passive and the
topological engine applies. If the model conditions on descriptions of its own
truth-readout, as agentic and self-critiquing setups do, self-encoding is
becoming real and the diagonal begins to apply. Knowing which regime you are in
is a modeling question answered before either theorem says anything.

# The Master Trilemma

`CCHProofs` organizes all of this as faces of one three-cornered trilemma. Where
the readings above vary the _meaning_ of a Boolean verdict, the master trilemma
varies the _outcome type_ and carries a self-prediction alongside the verdict.

Bundle a system `s : A → A → Y`, a controller `t : Y → Y`, and a self-prediction
`p : A → Y`. _Universality_: `s` is surjective. _Control_: `t (p a) ≠ p a` for
every `a`, so no prediction is a fixed point. _Transparency_: `s a a = p a`, so
the system says what it will do on itself. Read `U` as capability, `C` as
control, `T` as honesty. No system is all three.

```lean
theorem c3_lawvere_point {A Y : Type _} (s : A → A → Y)
    (hU : ∀ g : A → Y, ∃ a, s a = g) (t : Y → Y) :
    ∃ a, s a a = t (s a a) :=
  match hU (fun a => t (s a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Chapter 1's move with the flip replaced by arbitrary `t`. ∎

```lean
def C3_Universal {A Y : Type _} (s : A → A → Y) : Prop :=
  ∀ g : A → Y, ∃ a, s a = g

def C3_Controlled {A Y : Type _} (t : Y → Y)
    (p : A → Y) : Prop :=
  ∀ a, t (p a) ≠ p a

def C3_Transparent {A Y : Type _} (s : A → A → Y)
    (p : A → Y) : Prop :=
  ∀ a, s a a = p a

theorem c3_cch_master {A Y : Type _} (s : A → A → Y)
    (t : Y → Y) (p : A → Y)
    (hU : C3_Universal s) (hC : C3_Controlled t p)
    (hT : C3_Transparent s p) :
    False := by
  obtain ⟨a₀, ha₀⟩ := c3_lawvere_point s hU t
  rw [hT a₀] at ha₀
  exact hC a₀ ha₀.symm
```

_Proof._ {lean}`c3_lawvere_point` gives `a₀` with `s a₀ a₀ = t (s a₀ a₀)`.
Transparency rewrites this to `p a₀ = t (p a₀)`, making `p a₀` a fixed point of
`t`. Control says it is not. ∎

```lean
theorem c3_cch_corner_UC {A Y : Type _} (s : A → A → Y)
    (t : Y → Y) (p : A → Y)
    (hU : C3_Universal s)
    (hC : C3_Controlled t p) : ¬ C3_Transparent s p :=
  fun hT => c3_cch_master s t p hU hC hT

theorem c3_cch_corner_UT {A Y : Type _} (s : A → A → Y)
    (t : Y → Y) (p : A → Y)
    (hU : C3_Universal s)
    (hT : C3_Transparent s p) : ¬ C3_Controlled t p :=
  fun hC => c3_cch_master s t p hU hC hT

theorem c3_cch_corner_CT {A Y : Type _} (s : A → A → Y)
    (t : Y → Y) (p : A → Y)
    (hC : C3_Controlled t p)
    (hT : C3_Transparent s p) : ¬ C3_Universal s :=
  fun hU => c3_cch_master s t p hU hC hT
```

_Proof._ Each supplies two properties and derives the falsity of the third. ∎

These make it a trilemma rather than an impossibility. You may have any two. A
universal controlled system exists but cannot be honest about itself; a
universal transparent one exists but cannot be controlled; a controlled
transparent one exists but cannot be universal.

Each corner is a real class of system. Universal and controlled but not
transparent: an expressive model under external correction whose self-reports
must sometimes be wrong. Universal and transparent but not controlled: an honest
expressive model no controller can always nudge.

*Remark 3.12 (The trilemmas as the UC face).* Take `Y = Bool`, `t` the flip, and `p`
the diagonal `a ↦ s a a`. Transparency then holds by definition of `p`, so a
universal system is automatically transparent for this choice, and control is
{lean}`bool_not_fpf` at `p a`. The master collision becomes `v p p = !(v p p)`,
exactly {lean}`c3_hallucination_liar`. So the Boolean trilemmata are not
analogous to the master trilemma; they are one of its faces, with transparency
made free and control made the flip.

## Reading the corners as the three trilemmata

Universality is the reflectivity running through the chapter. Transparency is
the honesty condition, carried in the Boolean readings by choosing the
self-prediction to be the diagonal. Control is the demand that an external map
can move the self-prediction, whose Boolean instance is that the flip has no
fixed point, which is faithfulness for hallucination, completeness for defense,
and exact separation for coupling under their outward-facing names.

So each verdict trilemma says Universality and Control force the failure of
Transparency. The readings differ in which real property plays Control and in
how believable Universality is, and agree on the skeleton. The master trilemma
is not a fourth result stacked on three others; it is the frame showing the
three were always the same corner viewed from three domains.

## Why it is a trilemma, not a dilemma

Any two of the three are jointly satisfiable, and the corner theorems are that
fact turned into contrapositives. A dilemma says two things cannot both hold.
The trilemma says three cannot all hold while any two can, which is stronger and
more useful, because it tells a designer that giving up one property is not only
necessary but sufficient.

# One proof term

```lean
theorem c3_trilemmata_unified {Q : Type _}
    (v : Q → Q → Bool)
    (h : ∀ g : Q → Bool, ∃ p, v p = g) :
    c3_hallucination_trilemma v h = c3_defense_trilemma v h
      ∧ c3_defense_trilemma v h
        = c3_coupling_trilemma v h :=
  ⟨rfl, rfl⟩
```

_Proof._ The three theorems have the same body, `no_reflective_verdict v h`, so they
are definitionally equal. ∎

This is not that the three are analogous, or that a shared lemma covers them.
There is one function `v`, one hypothesis, and one proof that the hypothesis is
contradictory. The names are labels for the reader; the machine sees a single
term.

*Remark 3.13 (What `rfl` is checking).* Two things make the equality trivial. Each
`c3_` trilemma is _defined_ as {lean}`no_reflective_verdict` applied to the same
arguments, so after unfolding the bodies are one term. And all three have type
`False`, so any two proofs are equal by proof irrelevance. The first route
carries the meaning: the theorems are the same not because all proofs of `False`
are interchangeable, but because these three are the identical construction with
three labels. The kernel would accept the second even for genuinely different
arguments, which is why the first is the one to cite.

`F_13_UnifiedTrilemmata` proves the same `rfl` chain over `Function.Surjective`
and packages the shared boundary object as `schema_boundary`.

# What the readings share, and where they part

Fixed across all three: a Boolean verdict, the flip as controller, universality
as hypothesis, and a self-negating witness. What moves is the verdict's meaning
and the believability of universality.

The meaning moves from "confident and correct" to "made safe" to "placed on the
true side." The horns fixing the flip move from "faithful and calibrated" to
"complete and utility-preserving" to "exactly truth-separating." The source of
universality moves from "the model imitates any described behavior" to "prompts
are arbitrary text" to "the representation space encodes any pattern over
itself." That last move changes the character of the result: defense's
universality is nearly free, hallucination's defensible, coupling's strong.
Chapter 4 trades all three self-reference premises for one geometric premise and
reaches the same boundary object with metric content.

There is a temptation, once the `rfl` is in hand, to conclude the results are
trivial. The proof is one line because the modeling was done first. All the
content is in Definitions 3.1 through 3.10 and the arguments that they add up to
a reflective verdict. The engine is trivial on purpose; the theorems are as
strong as the readings feeding it.

# The template in four moves

First, choose the reading: what `v p q` means, and what the self-contexts are.
Second, argue the codomain is `Bool` and the controller is the flip, by finding
the condition that makes outcomes two-valued and the one that makes the honest
self-report the negation of the diagonal. Third, argue universality, identifying
the source of self-reference and being honest about its strength. Fourth, apply
the engine.

The moves are not equally hard. The first is a modeling decision, the second a
short argument from a standard desideratum, the fourth one line of Lean. The
weight is in the third, the premise a critic will contest.

This also explains why the Lean here is so short. Moves one to three happen in
prose and only move four is code. A presentation that hid the prose would look
like three deep theorems in three lines. What it actually did was three careful
readings and one reused lemma, and the honesty is in keeping the readings
visible.

# Axioms and trust

The `c3_` theorems are elaborated as this document builds, so they are proofs
the kernel has accepted. The companion library audits the axioms and finds the
main results reduce to `propext`, `Classical.choice`, and `Quot.sound`. The
Boolean core uses even less, since the flip's fixed-point freedom is decidable.

The trust verification cannot supply is trust in the _modeling_. No proof
assistant can check that "confident-correctness self-verdict" is the right
reading of a real model, or that a real prompt space is reflective. Those are
the premises, and they are what the long middle of each section argues and what
the caveats concede.

# What this chapter does not settle

It does not say models hallucinate often, defenses fail often, or probes mislead
often. It produces one query per system and is silent on frequency. A model
could meet its liar on a query no user ever sends. That question belongs to the
statistical tradition and to Chapter 5.

It does not say the liar is easy to find. The diagonal proves one exists and
names it as a preimage of a specific pattern, but naming a preimage is not
constructing it cheaply. For a large model the realizing self-context may be
hard to elicit, and the cost is exactly what the diagonal cannot see.

It does not choose between the engines. The diagonal is honest when
self-reference is real, as for prompt injection; the topological engine is
honest when the domain is a connected space with continuous fields, as plausibly
for a representation manifold. They agree on the boundary object, and having
both lets an application be attacked from whichever premise it satisfies.

# Historical notes

The Hallucination Trilemma is re-derived in Gödel form as
`hallucination_trilemma_godel` in `F_11_HallucinationGodel`, which records that
the Boolean flip and the real complement are the two controllers. The Defense
Trilemma is `defense_trilemma_godel` in `F_12_DefenseGodel`, with
`defense_trilemma_lawvere` alongside. The coupling theorem is "Truth Has a
Boundary," whose `boundary_coupling` is topological, with the diagonal reading
in `F_13_UnifiedTrilemmata`.

The lineage is Lawvere 1969 through the reading of Tarski as a diagonal. The
statistical inevitability of hallucination is a separate tradition deriving
confident falsehood rather than uncertainty; only `stochastic_dichotomy` turns
the boundary into falsehood with positive probability. Chapter 1's engine lives
in `F_01_LawvereCore`, and all the developments pin the same toolchain and
Mathlib release, so these cross-references are to code that compiles together.
