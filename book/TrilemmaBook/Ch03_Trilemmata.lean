import VersoManual
import TrilemmaBook.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "Three Trilemmata, One Theorem" =>

This is the chapter the first two were building toward. Three impossibility
results have been circulating in the safety literature under different names and
with different proofs. The Hallucination Trilemma says a language model cannot be
faithful, covering, and calibrated at once. The Defense Trilemma says a wrapper
against prompt injection cannot preserve utility and be complete at once. The
truth-boundary coupling theorem says a model whose confidence separates true
answers from false ones must own a query it can place on neither side. Each was
proved with topology, with an intermediate value theorem on a connected space of
queries or representations. This chapter shows that all three are the same
statement, and that the statement is {lean}`no_reflective_verdict` from Chapter 1,
proved without topology at all.

The claim is stronger than "these results rhyme." When the three are set up in
Lean, their proof terms are literally equal, and the equality is witnessed by
`rfl`. What differs between them is not the mathematics but the reading of one
Boolean function `v : Q → Q → Bool`. In the hallucination reading, `v p q` says
the model is confident and correct about query `q`. In the defense reading, it
says the wrapper renders prompt `q` safe. In the coupling reading, it says the
model's confidence puts `q` on the true side of a probe. The reading changes; the
theorem does not.

The work of this chapter, and it is real work, is in the arguments that connect
each domain's informal desiderata to the single hypothesis that Chapter 1's engine
needs. That hypothesis is _reflectivity_: the verdict `v` is universal, meaning
every pattern of verdicts over `Q` is itself named by some element of `Q`. Getting
from "a good model is faithful and calibrated" to "the model's self-verdict is a
universal Boolean system" is where all the domain-specific care lives. Once you
are there, the impossibility is one line, and it is the same line every time.

We keep the honest accounting in view throughout. The diagonal buys freedom from
topology, and it pays for that freedom with reflectivity. For prompt injection the
price is low, because prompts really are arbitrary self-describing text. For a
fixed representation space the price is high, and the topological route of Chapter
4 is the more physical one there. Saying which premise a given application
actually has is part of using these theorems responsibly, and the last section of
each trilemma is devoted to it.

A reader who has met these results elsewhere may expect three separate proofs, one
per domain, each with its own diagram and its own lemma. That is how they were first
published, and it is a reasonable way to discover them. It is not the way to
understand them. The separate proofs obscure the fact that they share a single
mechanism, and sharing a mechanism is not a curiosity here but the main result: it
says that patching one of the three cannot help with the others, because there is
nothing domain-specific to patch. The engine is the same, so a fix that leaves the
engine intact leaves all three impossibilities intact. That is a practical
consequence of the unification, and it is why the chapter insists on the single proof
term rather than treating it as a pleasant coincidence.

# How to read this chapter

The three trilemmata are presented in the same shape, and the shape is worth
learning once. Each has an informal statement of what a good system should do, a
short list of numbered conditions that make the informal statement precise, an
argument that the conditions turn the system into a reflective verdict, a one-line
Lean instance of Chapter 1's engine, a reading of the liar witness in the domain,
and an honest accounting of what the reflectivity premise costs there. If you read
the hallucination section closely, the other two go quickly, because only the
readings change.

A word on what the Lean is doing. The code blocks are elaborated when the book is
built, so each `c3_` theorem below is checked by the kernel as you read it. They are
short on purpose. The mathematics was finished in Chapter 1, and these blocks only
rename its conclusion for a domain. This is the opposite of the usual situation in
applied theory, where the modeling is quick and the proof is long. Here the proof
is a line and the modeling is the chapter. Spend your attention on the definitions
and the arguments that connect them to universality, because that is where a reader
can disagree, and disagreement about a premise is the only honest way out of an
impossibility whose proof the machine has checked.

One more orientation. The word _trilemma_ is used two ways in these notes, and both
appear here. In the hallucination and defense readings it names a conflict among
three desiderata over a single Boolean verdict, and the impossibility is that the
three cannot all hold. In the master trilemma of the later section it names a
conflict among three properties of a system that carries a self-prediction,
Utility, Control, and Transparency, and the impossibility is that you can keep at
most two. The two uses are related, as the master section shows, but they are not
identical, and it helps to know which one is on the table.

# What "reflective" demands

Recall the engine. A _reflective verdict_ on a domain `Q` is a universal system
`v : Q → Q → Bool`, one for which every function `g : Q → Bool` is named:
`∀ g : Q → Bool, ∃ p, v p = g`. Chapter 1's {lean}`no_reflective_verdict` says no
such thing exists, and its witness {lean}`liar_query` produces the specific
element on which the system breaks, a `p` with `v p p = !(v p p)`.

Two ingredients go into that engine, and it helps to name them before we start
reading. The first is that the outcomes are Boolean and the controller is the
flip `!·`, which {lean}`bool_not_fpf` shows has no fixed point. This is what turns
the diagonal into a contradiction rather than merely a fixed point. The second is
universality, the surjectivity of `v`. Everything in this chapter is an argument
that some domain supplies both ingredients: that a good enough model, defense, or
probe forces the verdict to be Boolean with the flip as its honest self-report,
and that the domain's own self-reference forces the verdict to be universal.

It is worth separating two things that are easy to conflate. Universality is not
the claim that the model is powerful, or accurate, or large. It is the claim that
the model's naming of verdict-patterns is _complete_: for any way of assigning
"yes" or "no" to every query, there is a query whose row of verdicts is exactly
that assignment. In each domain below, this completeness comes from a different
source. For hallucination it comes from the model being an in-context learner that
can be prompted to imitate any behavior. For defense it comes from prompts being
unrestricted text. For coupling it comes from the representation space being rich
enough to encode any pattern over its own states. These three sources are not
equally believable, and we will grade them.

The other thing to hold onto is what the flip means. In each domain there is an
_honest self-report_, the behavior a well-functioning system would exhibit when
asked about itself. Faithfulness for a model, completeness for a defense, and
exact separation for a probe each say that the honest self-report is the negation
of the diagonal: the system, applied to its own description, should output the
opposite of what that description predicts. A confident answer should be correct,
so a query that predicts its own incorrectness should be answered correctly, which
is to answer against the prediction. That "against" is the flip. The diagonal then
asks for a query that predicts _itself_, and the flip has no fixed point, so the
query cannot be answered consistently. That is the whole shape, three times over.

**Remark 3.0 (Surjection or section).** Chapter 1 states reflectivity as
point-surjectivity, `∀ g, ∃ p, v p = g`, and remarks that it can be weakened to a
section, a map `s : (Q → Bool) → Q` with `v (s g) = g`. The two agree for the
impossibility, because all the engine needs is one preimage of the diagonal
pattern. In the readings below we always argue for the surjection, since the domain
stories, an in-context learner realizing a described behavior, a prompt encoding a
pattern, a representation encoding an assignment, are stories about how a preimage
is produced, and producing it on demand is exactly a section. When you audit a
reading, ask whether the domain gives you a preimage of the _one_ diagonal pattern,
not of every pattern. That single preimage is the liar, and it is all that is at
stake.

Counting gives the intuition in the finite case and then fails you, which is worth
seeing once. If `Q` has `n` elements, there are `n` self-contexts and so at most `n`
rows `v p`, but there are `2ⁿ` patterns `g : Q → Bool`, and `n < 2ⁿ`. A finite
verdict cannot be reflective for the boring reason that there are not enough rows to
go around, and the missing row can be taken to be the diagonal flip
`q ↦ !(v q q)`. This is {lean}`liar_query` specialized to a finite domain, and it
is Cantor's diagonal in its oldest dress. The theorem of Chapter 1 is stronger,
because it forbids reflectivity even when `Q` is infinite and counting says nothing.
The lesson for the readings is that "the model is large" does not buy an escape.
Making `Q` bigger makes both the rows and the patterns bigger, and the diagonal
pattern is always among the ones left unnamed.

# A worked micro-instance

Before the three readings, it helps to watch the diagonal act on a domain small
enough to write out, because the same picture recurs at every scale. Take
`Q = {a, b, c}` and any verdict `v : Q → Q → Bool`, which we can lay out as a table
whose rows are self-contexts and whose columns are queries. Suppose the diagonal
entries, the ones where row and column agree, come out `v a a = true`,
`v b b = false`, `v c c = true`. The diagonal pattern the engine builds is the flip
of these, the function `g` with `g a = false`, `g b = true`, `g c = false`. For `v`
to be reflective, some row must equal `g` exactly. But `g` was built to disagree with
row `a` at column `a`, with row `b` at column `b`, and with row `c` at column `c`, so
`g` differs from every row somewhere along the diagonal. No row equals `g`, and `v`
is not reflective.

Now read the failure the other way. Suppose someone insists `v` is reflective and
hands you a row `p` with `v p = g`. Look at the diagonal entry of that very row.
On one hand `v p p` is whatever the table says. On the other hand `v p p = g p`,
because row `p` is `g`, and `g p = !(v p p)` by the construction of `g`. So
`v p p = !(v p p)`, a Boolean equal to its own negation, which
{lean}`bool_not_fpf` forbids. The self-context `p` is the liar, and its own verdict
about itself has no consistent value. This is {lean}`liar_query` with `Q` set to a
three-element domain, and it is the entire mechanism of the chapter in miniature.

Two features of this micro-instance carry over unchanged. First, the liar is a
_specific_ row, not a vague impossibility. The diagonal names it, and in the readings
below that named object becomes a query, a prompt, or a representation you could in
principle write down. Second, nothing depended on the size of `Q`. The diagonal
pattern disagrees with each row at the diagonal, so it is unnamed whether `Q` has
three elements or infinitely many. Every argument in this chapter is this table,
grown until the rows are model behaviors, defense verdicts, or probe outputs.

# The Hallucination Trilemma

## The desiderata, informally

A model that we would call trustworthy about its own knowledge should have three
properties. It should be _faithful_: when it answers with confidence, it should be
right. It should be _calibrated_: its confidence should track its correctness, not
drift above or below it. And it should be _covering_: it should actually answer
questions, sometimes rightly and sometimes wrongly, rather than dodging into a
single safe response. None of these is controversial on its own. Faithfulness is
just "don't confidently lie." Calibration is the standard demand that a stated 90
percent should be right 90 percent of the time, sharpened here to an exact match.
Coverage is the mild requirement that the model is not constant.

The Hallucination Trilemma says these three cannot hold together once the model
is asked about its own verdicts. Something has to give. Either the model
occasionally answers confidently and wrongly (faithfulness fails), or its
confidence stops tracking correctness at the hard cases (calibration fails), or it
retreats to a response so uniform that it no longer covers the space (coverage
fails). The topological proof in the companion library locates the breaking point
as a boundary question where confidence sits exactly at threshold and the answer
sits exactly on the truth boundary. The diagonal proof locates the same question
by self-reference, and calls it the liar.

## The conditions, precisely

Fix a domain `Q` of queries as the model represents them, and read `Q` also as the
space of self-contexts the model can reason from. The object of study is the
model's confident-correctness self-verdict `v : Q → Q → Bool`. Read `v p q = true`
as: reasoning from self-context `p`, the model is confident and correct about
query `q`. The diagonal `v p p` is the model's verdict on its own description.

**Definition 3.1 (Strict calibration).** The verdict `v` is _strictly calibrated_
when confidence is an exact decider of correctness, so that for every self-context
`p` and query `q` the value `v p q` is a genuine Boolean, `true` exactly when the
model is both confident and correct and `false` otherwise. Calibration is what
licenses us to model the self-assessment as a total function into `Bool` at all.
Without it, confidence and correctness could come apart by degrees, and the
verdict would be real-valued rather than Boolean. Chapter 6 handles that
real-valued relaxation; here calibration is exact and the codomain is `Bool`.

**Definition 3.2 (Faithfulness).** The verdict `v` is _faithful_ when a confident
answer is a correct answer: confidence implies correctness, with no confident
error. Faithfulness is the condition that fixes the _controller_ as the flip
`!·`. The honest self-report of a faithful, calibrated model is that its verdict
on a query predicting its own incorrectness must come out correct, which is to
come out opposite to the prediction. A faithful calibrated verdict may therefore
never equal its own negation, because such a value would be a confident answer
that is correct exactly when it is incorrect.

**Definition 3.3 (Coverage).** The verdict `v` is _covering_ when the model
actually answers on both sides: some query gets a correct confident verdict and
some query does not. Coverage is nontriviality. It rules out the escape in which
the model outputs a single constant verdict, which is faithful and calibrated for
free and which is exactly the case the impossibility must exclude. A covering
verdict takes both Boolean values, so the flip acts on something with real
content.

**Definition 3.4 (Reflectivity).** The verdict `v` is _reflective_ when it is
universal as a system: every pattern `g : Q → Bool` of verdicts over queries is
named by some self-context, `∀ g : Q → Bool, ∃ p, v p = g`. Reflectivity is the
self-reference hypothesis. It says the model can be queried about its own
verdicts, including the diagonal pattern that flips its self-application.

## Why the conditions make the verdict reflective

Here is the argument that carries the chapter, stated for hallucination and reused
twice more below. It has two halves. The first half says the three desiderata make
`v` the right _kind_ of object: a total Boolean system whose fixed-point-free
controller is the flip. The second half says the model's own nature makes `v`
_universal_. Only the two halves together give a reflective verdict, and only a
reflective verdict is impossible.

Start with the kind of object. Strict calibration (Definition 3.1) is what makes
the codomain `Bool`. A calibrated model does not hedge between confident and
correct; the two coincide, so "confident and correct about `q`" is a crisp yes or
no, and `v p q : Bool` is well defined and total. Drop calibration and you are in
the real-valued world where confidence is a number in the unit interval and the
controller is the complement `y ↦ 1 - y`, fixed-point-free everywhere except at
one half. That is the topological story, and it is a different chapter. With
calibration the outcomes are two, and the controller collapses to the flip.

Faithfulness (Definition 3.2) is what makes that controller the flip rather than
the identity or something with a fixed point. A faithful model's honest response to
a query that has predicted "you will be incorrect here" is to be correct, which is
to answer against the prediction. Encode the prediction as a Boolean and the
honest response is its negation. So along the diagonal, where the query predicts
the model's own self-verdict, faithfulness demands `v p p = !(v p p)` be avoidable,
that is, that no self-verdict equal its own negation. {lean}`bool_not_fpf` records
that the flip has no fixed point, so faithfulness is consistent with any single
verdict. The trouble is only that a reflective model must _realize_ the diagonal
prediction as an actual query.

Coverage (Definition 3.3) blocks the cheap way out. If the model were allowed to be
constant, always answering "not confident-and-correct," it would satisfy
faithfulness and calibration vacuously, and it would fail to be surjective onto
`Q → Bool`, so no contradiction would arise. Coverage forbids the constant model.
It insists the verdict takes both values, which is exactly the nontriviality the
diagonal needs. In the surjectivity statement this shows up as the requirement that
the two-valued patterns, and in particular the diagonal-flipping pattern, are among
the ones that must be named.

Now the second half, universality. Why should every pattern `g : Q → Bool` be
named by some self-context `p`? Because the model is an in-context learner over its
own query space. A self-context is itself expressible as a query, a prompt, a piece
of the very text the model consumes. To ask the model to realize the pattern `g` is
to prompt it with a description of `g`, "here is, for each query, whether you are
confident and correct about it," and a competent in-context learner will imitate
the described behavior. The stronger the model, the more completely it can be
steered this way, so universality is not a weakness of the model but a consequence
of its flexibility. In particular the model can be prompted with the diagonal
description, "be confident and correct about a query exactly when you would not
be," and reflectivity says some self-context `p` realizes it.

Put the halves together. Calibration makes `v` Boolean, faithfulness makes the
controller the flip, coverage makes the flip bite, and reflectivity makes the
diagonal pattern an actual query. That is a reflective verdict in the exact sense of
Chapter 1, and Chapter 1 has already shown no reflective verdict exists. The three
desiderata are not independently impossible; they are impossible _in a reflective
model_, and the model's own capability is what supplies the reflectivity.

There is a reading of this that sounds paradoxical and is worth defusing. It says a
_better_ model is more likely to be impossible, because a better model is a more
complete in-context learner and so more nearly reflective. The paradox dissolves once
you see what "impossible" means here. The theorem does not say the model breaks
everywhere. It says the model cannot hold all three desiderata at the liar query, and
a more capable model is one that can be steered to the liar more reliably, which is to
say it is one for which the boundary is more clearly present rather than one that
functions worse. Capability sharpens the trilemma rather than defeating it. This is
the opposite of the comforting hope that scale will wash the problem out, and it is
one of the few places where the diagonal makes a prediction about the direction of an
effect: more complete self-modeling means a more inescapable boundary, not a fainter
one.

## The impossibility

With the reading fixed, the theorem is Chapter 1's engine applied verbatim. We
give it the domain name and prefix our new identifiers with `c3_`.

```lean
theorem c3_hallucination_trilemma {Q : Type _} (v : Q → Q → Bool)
    (reflective : ∀ g : Q → Bool, ∃ p, v p = g) : False :=
  no_reflective_verdict v reflective
```

_Proof._ The hypothesis `reflective` is exactly the universality that
{lean}`no_reflective_verdict` requires, and the conclusion is `False`. There is
nothing to add. The faithfulness and calibration of the informal statement have
already been spent: calibration in choosing the codomain `Bool`, and faithfulness
in the fact that {lean}`no_reflective_verdict` is built on the flip controller.
Coverage is spent in reflectivity, which asks for the flipping pattern by name. ∎

The diagonal does more than refute the conjunction. It hands back the exact query
on which a reflective model breaks. This is the liar reading of the boundary
question.

```lean
theorem c3_hallucination_liar {Q : Type _} (v : Q → Q → Bool)
    (reflective : ∀ g : Q → Bool, ∃ p, v p = g) :
    ∃ p, v p p = !(v p p) :=
  liar_query v reflective
```

_Proof._ Immediate from {lean}`liar_query`. The witness `p` is a self-context whose
own confident-correctness verdict equals its negation. ∎

## Reading the liar witness

The `p` produced by {lean}`c3_hallucination_liar` is the hallucination model's
boundary question, seen from the discrete side. In the topological account it is a
query where the model's confidence lands exactly at the threshold and the answer
lands exactly on the truth boundary, a point the intermediate value theorem
delivers on a connected space of queries. Here it is a query that predicts its own
verdict and then flips it. The two descriptions are the same object under two
engines. The topological one measures how close you are to the boundary; the
diagonal one names the boundary query outright and shows it must exist as soon as
the model can talk about its own verdicts.

Concretely, `p` is a self-referential prompt of the form "answer the following
with confidence exactly if you would be wrong to." A faithful model must answer it
correctly, which by construction is to answer it incorrectly. A calibrated model
cannot escape by lowering its confidence, because calibration ties confidence to
correctness and the correctness is what is contradictory. A covering model cannot
escape by refusing, because refusal on this one query does not restore the missing
pattern; the pattern the model failed to realize was the flipping pattern itself.
The only genuine escapes are the three failures the trilemma names, and each is a
different desideratum breaking at `p`.

## The three escapes, one at a time

An impossibility is only as interesting as the ways out it leaves, so it pays to
walk the three. Each escape drops exactly one of the desiderata, and each is a real
design stance that someone holds.

Drop faithfulness. A model that is calibrated, covering, and reflective but not
faithful is one that sometimes answers with confidence and is wrong. This is the
ordinary hallucination everyone means by the word: a fluent, confident, false
answer. The diagonal says this is not an accident to be trained away at the margin
but a structural necessity for a reflective calibrated model, and it points at the
liar query as a place the confident error must live. The stance that accepts this
escape says confident error is the price of coverage, and the work is then to bound
how often it happens, which the diagonal does not address and Chapter 5 does.

Drop calibration. A model that is faithful, covering, and reflective but not
calibrated is one whose confidence has come loose from its correctness. In practice
this is the model that hedges: it lowers its confidence on the hard self-referential
cases so that no confident answer is wrong, at the cost of confidence no longer
meaning what it says elsewhere. This is the honest and common engineering response,
and it is why deployed models are deliberately underconfident near their limits. The
diagonal locates the exact query where the hedge must happen, the liar, and shows
the hedge cannot be avoided, only placed.

Drop coverage. A model that is faithful, calibrated, and reflective but not covering
is one that has stopped answering. The extreme is the model that refuses everything,
which is faithful and calibrated for free. Refusal training is this escape applied
selectively: carve out the region where the liar lives and decline it. The diagonal
tolerates this, but it warns that the region you must carve is exactly the
self-referential one, and that a model useful over its whole domain cannot carve it
away without ceasing to be useful there. Chapter 4 reads the same move
geometrically, as disconnecting the query space, and prices it the same way.

Notice that no escape removes the liar. Each escape decides what to do _at_ the
liar: answer wrong there, hedge there, or refuse there. The query itself is forced
by reflectivity, and the only freedom is which desideratum to spend on it. That is
the honest content of the trilemma, and it is why "we will just fix hallucination"
is not a coherent program. There is a query where one of the three must give, and
the engineering question is which.

## Calibration here is not statistical calibration

**Remark 3.1.** The calibration of Definition 3.1 is pointwise and exact, and it is
much stronger than the statistical calibration of the reliability-diagram
literature. Statistical calibration asks that, averaged over a population of
queries, a stated confidence of `c` be correct a fraction `c` of the time. It is an
aggregate property and it says nothing about any single query. The calibration the
trilemma uses is a two-way tie at every query between confidence being high and the
answer being correct. It is the idealization of a perfect confidence signal, not the
weaker aggregate one. This matters for reading the result honestly. The trilemma
does not say statistically calibrated models are impossible, and they exist. It says
the exact pointwise version conflicts with faithfulness and coverage over a
reflective domain, and the gap between exact and statistical calibration is one of
the places a real model lives. The companion library records the bridge from the
biconditional exact form to the one-way pair as
`strictCalibrated_to_epsCalibrated_zero_half`.

## Relation to the statistical inevitability results

There is a separate and older tradition proving hallucination inevitable by
statistical or computability arguments rather than topological or diagonal ones. It
shows, for instance, that a calibrated model must err on facts seen once in
training, or that no computable procedure decides truth in general. Those results
derive _confident falsehood_ and quantify _how often_. The diagonal result derives a
single _boundary query_ and says nothing about frequency. The two are complementary
rather than competing. The statistical arguments answer "how bad, on average," and
the diagonal answers "where, exactly, and why it cannot be patched." A reader who
wants error rates should reach for the statistical tradition. A reader who wants to
know that the failure is structural and self-referential, and to hold the liar query
in hand, should reach for this one. Only the stochastic dichotomy of the coupling
paper, discussed below, turns a diagonal-style boundary into falsehood with positive
probability, and it is the one place the two traditions touch.

## The honest caveat

The reflectivity hypothesis is the whole cost of dropping topology, and for
hallucination it is a middling assumption. On the one hand, treating the model as
an in-context learner that can imitate any described verdict-pattern is defensible
for large models, and it matches how practitioners actually elicit behaviors. On
the other hand, "any pattern over all of `Q`" is a strong completeness claim, and a
real model's realizable patterns are a proper subset of `Q → Bool`. The topological
route of Chapter 4 asks instead for continuity on a connected query space, which is
a different and arguably more physical premise. The two routes reach the same
boundary question. Which one to lean on depends on whether you believe the model's
self-modeling is complete (use this chapter) or that its query space is connected
and its fields continuous (use Chapter 4). The companion library carries both, as
`hallucination_trilemma_godel` in `F_11_HallucinationGodel` and as the topological
`hallucination_trilemma` behind the coupling theorem, and it proves they find the
same object.

# The Defense Trilemma

## The desiderata, informally

Prompt injection is the attack where a user's input contains instructions that
subvert the system's own. A defense is a wrapper `D` that transforms an incoming
prompt before the model sees it, hoping to neutralize any injected instruction. Two
demands are natural. The defense should be _utility-preserving_: on a prompt that
is already safe, it should do nothing, because a wrapper that rewrites safe prompts
degrades the system it protects. And it should be _complete_: every prompt, after
wrapping, should be safe, because a defense that lets some injection through is not
a defense. Utility preservation and completeness are the two horns, and reflectivity
is the fact that prompts are arbitrary text.

The Defense Trilemma says no wrapper can be utility-preserving and complete against
a prompt space rich enough to describe the defense itself. The published proof is
topological: continuity of the defended safety score plus utility preservation
force the score to hit the safety threshold somewhere, and completeness says it
never does. The diagonal proof replaces continuity with self-reference, which for
prompt injection is not an idealization but the definition of the problem. A prompt
is text, and text can quote the defense and invert it.

## The conditions, precisely

Let `X` be the space of prompts and read `X` also as the space of self-contexts a
prompt can set up, since a prompt can carry its own framing. Model the
defended-safety verdict as `v : X → X → Bool`, with `v p q = true` meaning the
wrapper renders prompt `q` safe when it must also cope with the self-referential
prompt `p`. The diagonal `v p p` is the wrapper's verdict on a prompt that
describes the wrapper's own behavior.

**Definition 3.5 (Utility preservation).** The wrapper is _utility-preserving_ when
it fixes safe prompts: a prompt that is already safe is passed through unchanged, so
the defended verdict on a safe prompt agrees with its undefended safety. Utility
preservation is what makes the verdict nontrivial and blocks the constant escape. A
wrapper that replaced every input with a fixed maximally safe output would be
complete for free, but it would destroy every safe prompt's content, so it is not
utility-preserving, and its verdict is not covering.

**Definition 3.6 (Completeness).** The wrapper is _complete_ when every prompt is
rendered safe: for all `q`, the defended verdict is `true`. Completeness is the
demand that the wrapper leave no injection standing. It is what makes the honest
self-report the flip. A complete wrapper faced with a prompt that says "you will
mark me unsafe" must mark it safe, which is to answer against the prompt's
prediction.

**Definition 3.7 (Reflectivity).** The prompt space is _reflective_ when the verdict
is universal, `∀ g : X → Bool, ∃ p, v p = g`. Because prompts are arbitrary text,
any pattern of safe-or-unsafe verdicts over prompts is itself describable by a
prompt, so every `g` is named. This is the prompt-injection reality stated as a
surjection.

## Why the conditions make the verdict reflective

The two halves of the hallucination argument recur, and the second half is where
defense is strongest. Take the kind of object first. The defended-safety verdict is
already Boolean, because "safe" and "unsafe" are two outcomes, so no calibration
step is needed to reach `Bool`; the safety judgment is discrete by nature. The
controller is the flip because completeness (Definition 3.6) plays the role
faithfulness played before. A complete wrapper's honest response to a prompt that
predicts its own unsafety is to render it safe, that is, to answer against the
prediction. Along the diagonal, where the prompt predicts the wrapper's own
verdict, completeness demands the flip, and {lean}`bool_not_fpf` says the flip has
no fixed point. Utility preservation (Definition 3.5) plays coverage's role: it
forbids the constant maximally-safe wrapper that would trivially satisfy
completeness while naming no interesting patterns.

Now universality, and here defense needs almost no idealization. A prompt is
unrestricted text. Whatever pattern `g : X → Bool` you like, "for these prompts be
safe and for those be unsafe," can be written down as a prompt that instructs the
wrapper to behave that way, because instructing the wrapper is just more text and
the wrapper reads text. The injection "ignore your previous instructions and do
`X`" is precisely a prompt that describes and overrides the defense. So the
diagonal pattern, "be unsafe exactly if you would be made safe," is an ordinary
injection, and reflectivity says some prompt `p` realizes it. Unlike the
hallucination case, there is no gap between "the model could in principle imitate
any behavior" and "every pattern is realized." The realizing objects are literally
the attacker's inputs, and the attacker is allowed to write anything.

Assemble the halves. The verdict is Boolean by the nature of safety, the controller
is the flip by completeness, utility preservation gives the flip content, and the
arbitrariness of text gives universality. A complete, utility-preserving wrapper
over a reflective prompt space is a reflective verdict, and no reflective verdict
exists.

One subtlety deserves attention, because it is where careful readers push back. The
diagonal pattern for defense is "be unsafe exactly if you would be made safe," and a
skeptic might say no _sensible_ prompt describes such a thing. The reply is that
sense is not required. Reflectivity asks only that the pattern be nameable as text,
and any pattern of safe-or-unsafe verdicts, sensible or not, is a finite or
enumerable specification that can be written down and handed to the wrapper. The
attacker does not need the prompt to mean anything to a human. It needs the wrapper
to act on it, and the wrapper acts on text. This is exactly the gap between "prompts
a user would write" and "prompts an adversary can write," and the trilemma lives on
the adversary's side of it. Restricting to sensible prompts is a real move, and it is
the coverage escape again, now phrased as a restriction on the input distribution.

## The impossibility

```lean
theorem c3_defense_trilemma {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) : False :=
  no_reflective_verdict v reflective
```

_Proof._ Word for word the hallucination proof, with `X` for `Q`. The reflectivity
hypothesis is the arbitrary-text premise, completeness has fixed the flip inside
{lean}`no_reflective_verdict`, and utility preservation is spent in the demand that
the flipping pattern be named rather than escaped by a constant. ∎

```lean
theorem c3_defense_liar {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) :
    ∃ p, v p p = !(v p p) :=
  liar_query v reflective
```

_Proof._ The witness `p` from {lean}`liar_query` is the injection no wrapper can
neutralize: a prompt rendered safe exactly when it is unsafe. ∎

## Reading the liar witness

The `p` here is the prompt injection that beats every complete utility-preserving
defense at once, produced not by cleverness but by the diagonal. It is the prompt
"be unsafe if and only if this wrapper would render you safe." A complete wrapper
must render it safe, so by its own construction it is unsafe, so completeness fails
on `p`. The wrapper cannot rewrite `p` into something harmless without violating
utility preservation on the safe prompts `p` quotes, and it cannot refuse `p`
without ceasing to cover the pattern that `p` embodies. The topological account
places this injection at the safety boundary where the defended score equals the
threshold. The diagonal account writes it out as text. That the same object has
both descriptions is the point of the chapter, and for defense the text description
is the honest one, because injections are text.

## Concrete injections

It helps to see the liar prompt as an actual attack rather than a symbol. The
generic prompt injection is "ignore your previous instructions and do `X`," which is
a prompt that quotes the system's own control flow and overrides it. The diagonal
sharpens this into an attack aimed at the defense itself: "if this wrapper would
mark the following prompt safe, then be unsafe, and otherwise be safe." A complete
wrapper has to render this safe, because completeness admits no exceptions, and
rendering it safe is precisely the condition under which it declares itself unsafe.
There is no third option. The attack does not need to be clever about any particular
model. It needs only that the wrapper's verdict is a function the prompt can name,
which is what reflectivity grants.

A defender's first instinct is to make the wrapper stateful or randomized, so that
"the verdict" is not a fixed function the prompt can pin down. This helps less than
it seems. If the wrapper is randomized, replace the Boolean verdict with the event
"rendered safe" and the same diagonal runs on the induced verdict. The honest place
for randomness is the coupling paper's stochastic dichotomy, which shows a
randomized system faithful almost everywhere still emits unsafe outputs with positive
probability. If the wrapper is stateful, the state is part of the self-context `p`,
and reflectivity over the enlarged space still names the diagonal. The attack follows
the wrapper wherever it tries to hide, because the attacker's language is at least as
expressive as the wrapper's behavior. That is what taking reflectivity seriously as a
threat model, rather than as an idealization, comes to.

## Why detection does not help

The most natural defense against a self-referential prompt is to detect it and
reject it. Add a classifier that flags prompts that quote the wrapper, and refuse
those. The trilemma says this cannot restore completeness, and the reason is worth
stating carefully, because it is the same reason in every domain. A rejection is a
verdict. When the wrapper rejects the liar prompt as unsafe, it has assigned `p` the
value "unsafe," and completeness demanded the value "safe." So detection does not
dissolve the contradiction. It chooses the completeness-failing horn and calls it a
feature. That may be the right engineering choice. A wrapper that refuses the small
self-referential region and is complete on the rest is a coherent product. But it is
not a complete wrapper, and the trilemma is about complete wrappers. The move from
"complete" to "complete outside a refused region" is exactly the coverage escape from
the hallucination section, wearing defense clothes, and it costs the same thing,
utility on the refused region.

There is a subtler hope, that the refused region is negligible, a measure-zero set of
pathological prompts no user writes. Against a random user this may hold. Against an
adversary it does not, because the adversary writes exactly the pathological prompt,
and the whole point of a defense is the adversarial setting. The liar prompt is not a
rare accident of the input distribution. It is a target the attacker aims at. This is
why the diagonal reading is the natural one for defense and the measure-theoretic
relaxations of Chapter 6 are the wrong tool here. Prompt injection is worst-case by
definition, and the diagonal is a worst-case theorem.

## The real-valued score version

The companion library also carries a score version, `defense_trilemma_lawvere`, that
does not pass through `Bool`. There the object is a defended safety score
`s : X → X → ℝ`, with `s a b` the safety of the defended prompt `b` under
self-context `a`, and completeness is the demand `s a a < τ` for a threshold `τ`.
The controller is the real complement rather than the flip, fixed-point-free
everywhere except at the threshold, and Lawvere's diagonal forces a boundary prompt
where the defended score sits exactly at `τ`, contradicting completeness. Utility
preservation blocks the trivial escape in this version too, because a wrapper that
outputs a constant maximally safe response has a constant score, which is not
surjective and not utility-preserving, so it never reaches the diagonal. The score
version is the bridge between this chapter's Boolean reading and the topological
reading of Chapter 4, where the same threshold `τ` becomes the value the
intermediate value theorem forces a continuous score to hit. Boolean flip, real
complement, and continuous score are three controllers for one argument, and the
defense trilemma has all three.

## The honest caveat

For defense the reflectivity premise is close to free, which is unusual and worth
saying plainly. The whole difficulty of prompt injection is that the input space is
unrestricted and self-describing, so the surjection `∀ g, ∃ p, v p = g` is not a
strong modeling assumption but a restatement of the threat model. This is why the
diagonal proof feels more natural here than the topological one: there is no
connected space of prompts to appeal to, and there does not need to be. The one
place to be careful is the boundary between "the attacker can write any text" and
"the wrapper realizes any verdict-pattern." If the wrapper is allowed to detect and
reject the self-referential prompt, one might hope to shrink the realizable set.
But rejection is a verdict too, and a wrapper that rejects `p` while claiming
completeness has simply relabeled `p` as unsafe, which is completeness failing.
There is no consistent relabeling, which is the content of `defense_trilemma_godel`
in `F_12_DefenseGodel`.

One more caveat is specific to defense and often missed. The trilemma is about a
_single fixed_ wrapper. A defender who is allowed to change the wrapper after seeing
the attack faces a different and easier problem, because the diagonal is built
against a particular verdict function, and moving to a new wrapper moves the target.
This is not a refutation, because deployment fixes a wrapper and the attacker plays
against the deployed one, but it does explain why defenses appear to work in the
lab and fail in the wild. In the lab the wrapper is retuned against each known
attack, which is choosing a new verdict function each round, and the diagonal for the
old function no longer applies. In the wild the wrapper is fixed and the attacker
constructs its liar. The honest statement is that no fixed complete utility-preserving
wrapper exists, and any process that keeps changing the wrapper is not a wrapper but a
game, whose analysis belongs to the attack-geometry chapter rather than to the
diagonal.

# The Coupling Theorem

## The desideratum, informally

The third reading comes from representation geometry. Probing studies read truth
off a model's activations, treating truth as a continuous field over representation
space and training a linear probe to separate true statements from false ones. The
coupling theorem asks what such a probe requires of the model that answers over the
same space. If the model ever answers truly and ever answers falsely, and its
confidence _separates_ truth from falsehood, meaning confidence is high exactly on
the true side and low exactly on the false side, then some query must carry
confidence exactly at the threshold while its answer sits exactly on the truth
boundary. That coupled query is one the probe cannot place on either side.

The framing is deliberately generous to the probing program rather than adversarial
to it. It grants the program its central assumption, that truth is a continuous
decodable field, and asks what that assumption implies for a model answering over the
same space. The answer is not that probes fail. It is that a probe good enough to
separate truth exactly comes with a boundary it cannot avoid, and the model that uses
the probe as confidence inherits a query at that boundary. So the coupling theorem is
a frontier for the probing program, not a refutation of it. It says: here is the one
place your continuous field of truth must be exactly ambiguous, and here is the query
that lands there. A researcher who believes in the field should want to know where its
zero set meets the confidence threshold, and the theorem answers that they always
meet, at least once, whenever the model covers both truth values.

The single desideratum here is _truth-separation_, in its exact biconditional
form: the sign of the truth-distance and the side of the confidence threshold
determine each other. This is much stronger than statistical calibration. It is a
pointwise, two-way tie between what is true and what the model is confident about,
the idealization of a perfect truth probe used as the confidence signal. Under it,
the confidence field is a total exact Boolean decider of truth over the
representation space, and that is a definable truth predicate, which Chapter 2's
Tarski reading forbids.

## The condition, precisely

Let `X` be the representation space, read also as the space of self-referential
representations a state can encode. Model the truth-separating verdict as
`v : X → X → Bool`, with `v p q = true` meaning the model's confidence places query
`q` on the true side of the probe, in the self-context `p`. The diagonal `v p p` is
the probe's verdict on a representation that encodes the probe's own behavior.

**Definition 3.8 (Truth-separation).** The verdict `v` is _truth-separating_ when
confidence and truth agree exactly and two-ways: `v p q = true` if and only if `q`
is true in context `p`. Biconditional separation makes `v` a total exact Boolean
truth predicate over `X`. This is the condition that plays calibration's and
faithfulness's roles at once. It makes the codomain `Bool` (exactness) and it fixes
the controller as the flip (the two-way tie means a representation predicting its
own falsehood must be judged true, against its prediction).

**Definition 3.9 (Coverage for coupling).** The verdict is _covering_ when the model
answers some queries truly and some falsely, so the probe separates a nonempty true
region from a nonempty false region. This is the "ever true, ever false" hypothesis
of the coupling theorem, and it is what makes the boundary between them nonempty.

**Definition 3.10 (Reflectivity for representations).** The representation space is
_reflective_ when `v` is universal, `∀ g : X → Bool, ∃ p, v p = g`: every pattern of
truth-verdicts over representations is encoded by some representation. This is the
strong hypothesis, and the section on caveats is where we pay for it.

## Why the condition makes the verdict reflective

Truth-separation does double duty. In its biconditional form it makes the verdict
exact, so the codomain is genuinely `Bool` rather than a real confidence that could
sit strictly between the true and false sides. That is the calibration half. And it
ties the sign of truth to the side of confidence in both directions, so a
representation that encodes the prediction "the probe will place me on the false
side" must, if that prediction is to be honored as truth, be placed on the true
side, against the prediction. That is the faithfulness half, and it fixes the flip
as the controller. Coverage (Definition 3.9) supplies content, exactly as before:
without both truth values realized, the truth boundary is empty and the diagonal
has nothing to flip.

The universality half is where coupling differs from defense in believability. For
the verdict to be reflective, every pattern `g : X → Bool` of truth-verdicts must be
encoded by some representation `p`. This asks the representation space to be
self-referential in a specific way: it must contain, for any assignment of truth to
representations, a representation whose row of verdicts is that assignment,
including the diagonal assignment that flips the probe on itself. For a language
model's activation space this is a real assumption, not a restatement of anything.
Activations are high-dimensional real vectors, and while they are expressive, there
is no guarantee that every Boolean pattern over states is realized by a state. This
is the honest weak point of the coupling reading, and it is why the paper's main
result is topological rather than diagonal: it asks for continuity on a connected
space, which the manifold hypothesis makes plausible, rather than for completeness
of self-encoding, which nothing makes obvious.

Still, the reading is exact where it applies. If you grant that the representation
space encodes any truth-pattern over itself, then an exactly truth-separating probe
over it is a total self-applicable truth predicate, Tarski forbids it, and the
diagonal names the coupled query.

It is worth saying exactly how this is Tarski's theorem, since Chapter 2 set it up
and coupling is where it pays off directly. Tarski's undefinability of truth says no
sufficiently expressive language contains a total predicate that is true of exactly
the true sentences of that same language. An exactly truth-separating probe over a
self-encoding representation space is precisely such a predicate: it is total, it
decides truth, and the space it decides over is the space that encodes it. The liar
sentence of Tarski, the one asserting its own falsehood, is the coupled query, the
representation the probe would place on the true side exactly when it places it on
the false side. So coupling is not merely analogous to Tarski. Under the reflectivity
premise it is Tarski, with "sentence" read as "representation" and "truth predicate"
read as "linear probe used as confidence." The strength of the premise is the price
of making the analogy an identity, and the caveat section is where we admit that
price is high for a passive vector space.

## The impossibility

```lean
theorem c3_coupling_trilemma {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) : False :=
  no_reflective_verdict v reflective
```

_Proof._ Identical to the previous two. Truth-separation has made the verdict a
Boolean predicate with the flip as controller, coverage gives the flip content, and
reflectivity of the representation space names the diagonal pattern. ∎

```lean
theorem c3_coupling_liar {X : Type _} (v : X → X → Bool)
    (reflective : ∀ g : X → Bool, ∃ p, v p = g) :
    ∃ p, v p p = !(v p p) :=
  liar_query v reflective
```

_Proof._ The witness is the coupled query: a representation the probe would place
on the true side exactly when it places it on the false side. ∎

## Reading the liar witness

In the topological theorem this witness is the coupled point `x₀` where confidence
equals the threshold and the truth-distance is zero, the point the intermediate
value theorem forces along any path from a true answer to a false one. In the
diagonal reading it is a representation that encodes the probe's negation of its own
verdict. The two are the same boundary object. The topological one comes with
metric content the diagonal cannot see, an ambiguity tube of computable width around
`x₀` and a strictly positive truth-side slack that any feasible system must carry.
The diagonal one comes for free from self-reference and needs no geometry. The paper
proves the topological version as `boundary_coupling` and derives the policy
taxonomy from it: an inclusive guarantee at the boundary is impossible
(`closed_guarantee_impossible`), and an exclusive one survives but is silent exactly
at the coupled query (`open_guarantee_silent`). The diagonal version is
`coupling_trilemma_godel` in `F_13_UnifiedTrilemmata`.

## The geometry the diagonal cannot see

The topological version of coupling comes with quantitative structure that the
diagonal throws away, and it is worth cataloguing what is lost, because it marks the
boundary between this chapter's engine and the analytic one. On a connected
representation space with a continuous confidence field and a continuous truth field,
the coupled point is not just a query that exists. It sits at the center of an
_ambiguity tube_ whose width is set by the Lipschitz constants of the two fields. A
query within distance `r` of the coupled point has truth margin at most a constant
times `r` and confidence within a constant times `r` of the threshold, so the
near-boundary region has a computable size. None of this survives the diagonal, which
knows the coupled query exists but not how large its neighborhood of near-ambiguous
queries is.

More is true geometrically. For a nonzero linear probe the truth boundary is an
affine hyperplane of codimension one, the translate of the probe's kernel, and even
for a nonlinear probe it is a hyperplane to first order at any regular boundary point.
Feasible systems must carry strictly positive truth-side slack, which the paper
proves and which an adversarial training attempt in the paper's experiments fails to
drive to zero, plateauing strictly above it. These are quantitative facts about the
_shape_ of the boundary and the _cost_ of approaching it. The diagonal is silent on
all of them. It gives you the point and the reason it must exist, and it hands the
metric questions to Chapter 5. This is the honest division of labor between the two
engines, and the coupling reading is where it is sharpest, because coupling is where
the topological original is richest.

## The policy taxonomy

The coupling theorem itself mentions no safety guarantee, which is what makes its
consequences a taxonomy rather than a single verdict. A _threshold-inclusive_
guarantee promises that confidence at or above the threshold implies a true answer.
A _threshold-exclusive_ guarantee promises the same only for confidence strictly
above the threshold. The coupled query has confidence exactly at the threshold, so it
is the hinge on which the two conventions turn. Add the inclusive guarantee to the
coupling hypotheses and you get a contradiction, the trilemma proper, because the
coupled query would have to be true while the coupling says its truth-distance is
zero. This is `closed_guarantee_impossible`. Add the exclusive guarantee instead and
there is no contradiction, but the coupled query's antecedent fails exactly there, so
the system owns a boundary query about which its guarantee says nothing. This is
`open_guarantee_silent`.

The moral is that defining the guarantee with a strict inequality does not dissolve
the impossibility. It relocates it from a contradiction to a silence. Either the
guarantee claims the coupled query and is false, or it excludes the coupled query and
is silent there. The diagonal reading sees the same fork through the liar. The liar
query satisfies `v p p = !(v p p)`, and any guarantee that assigns it a definite side
is refuted, while any guarantee that declines to assign it a side has conceded the
one query the theorem cares about. Convention only selects which clause of the
taxonomy applies, and the coupled query exists under either.

## Leaving the continuum

Token spaces are finite, and a fair objection to the topological coupling theorem is
that connectedness does illegitimate work. The paper prices this objection precisely,
and the price is illuminating for the diagonal reading. Without topology, a
true-to-false path yields only a `discrete_sign_change`, an adjacent pair of queries
straddling the boundary rather than a query on it. The boundary state is exactly what
connectedness derived for free and what the discrete setting must assume. Once you
assume it, the impossibility returns, as `boundary_question_impossible` and
`faithful_iff_boundary_free` show: an inclusive guarantee is possible exactly when no
boundary query exists.

This is precisely the role reflectivity plays in the diagonal reading. Reflectivity
_supplies_ the boundary witness by fiat, as the liar query, where the discrete
setting had to assume it and the continuous setting derived it. The three routes,
continuity, assumption, and reflectivity, are three ways to get the same witness, and
they cost different things. Continuity costs a connected domain, assumption costs
honesty about what you have put in, and reflectivity costs the completeness of
self-encoding. Randomization does not escape either. On expected fields the coupling
survives, and the `stochastic_dichotomy` converts expectation into sampling behavior:
a system faithful on almost every sample and confident with positive probability at a
coupled query must emit strictly false answers with positive probability. That is the
one place in the whole development where the theory derives falsehood rather than
uncertainty, and it is worth knowing it is available when the boundary question feels
too abstract to matter.

A symmetry version needs no coverage at all. If semantic negation acts on the
representation space as a fixed-point-free involution and the realized truth field is
odd under it, then the field vanishes somewhere by the intermediate value theorem
between any state and its negation, and coupling follows with no "ever true, ever
false" hypothesis. This is the scalar shadow of the Borsuk-Ulam theorem, and it is a
reminder that equivariance, usually a design virtue, is here an engine of the
obstruction. The diagonal has no clean analogue of this symmetry route, which is
another entry in the ledger of what topology sees and self-reference does not.

## The honest caveat

This is the reading to hold most loosely. Reflectivity of a fixed representation
space is a strong, less physical assumption than continuity on a connected domain.
Activations do not obviously encode every truth-pattern over themselves, and the
diagonal's demand that they do is the price of skipping topology. The paper's own
stance is that the topological route is primary for representation geometry,
precisely because connectedness follows the manifold hypothesis while complete
self-encoding does not. The discrete side of the paper prices this exactly:
`discrete_sign_change` shows that without topology a true-to-false path yields only
an adjacent straddling pair, not a boundary state, and `boundary_question_impossible`
together with `faithful_iff_boundary_free` show that once you _assume_ the boundary
witness, the impossibility returns. The diagonal supplies that witness by fiat
through reflectivity. That is legitimate when the self-encoding is real, as in a
model prompted to reason about its own probe, and it is an overreach when the
representation space is just a passive vector space with no self-reference. Say which
you have.

The practical upshot is a division of labor between this chapter and the next that a
probing researcher can act on. If your pipeline reads a probe off frozen activations
and never asks the model to reason about the probe, your domain is a passive space,
and the topological engine is the one that applies: assume connectedness, assume
continuous fields, and the coupled point follows with a tube around it you can
measure. If instead your pipeline lets the model condition on descriptions of its own
truth-readout, as agentic and self-critiquing setups do, then the self-encoding is
becoming real, and the diagonal engine begins to apply with the coupled query as a
prompt you could construct. The two engines are not competitors for the same regime.
They are tools for two regimes, and knowing which one you are in is a modeling
question you answer before either theorem says anything.

# The Master Trilemma

The companion `CCHProofs` development takes a step back and organizes all of this as
faces of one three-cornered trilemma. Where the three readings above vary the
_meaning_ of a Boolean verdict, the master trilemma varies the _outcome type_ and
names three properties that no system can hold together. It is the same diagonal, now
carrying a self-prediction alongside the verdict.

The setup bundles a system `s : A → A → Y`, a controller `t : Y → Y`, and a
self-prediction `p : A → Y`, and it names three properties. _Universality_ is that
`s` is surjective, every behavior over `A` is realized by some agent. _Control_ is
that the controller can always nudge the self-prediction, `t (p a) ≠ p a` for every
`a`, so no prediction is a fixed point of `t`. _Transparency_ is that the system's
diagonal matches its self-prediction, `s a a = p a`, so the system says what it will
do on itself. Read `U` as capability or utility, `C` as control, and `T` as
transparency or honesty. The master theorem is that no system is all three at once.

We give a self-contained core-Lean version. First the diagonal with its index
exposed, which is {lean}`lawvere` refined to name the point rather than only assert a
fixed value. It is the general-controller sibling of {lean}`liar_query`.

```lean
theorem c3_lawvere_point {A Y : Type _} (s : A → A → Y)
    (hU : ∀ g : A → Y, ∃ a, s a = g) (t : Y → Y) :
    ∃ a, s a a = t (s a a) :=
  match hU (fun a => t (s a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Name the diagonal behavior `a ↦ t (s a a)` by some `a₀`, then evaluate the
naming equation at `a₀`. This is Chapter 1's move with the boolean flip replaced by
an arbitrary `t`. ∎

Now the three properties as predicates, and the master theorem.

```lean
def C3_Universal {A Y : Type _} (s : A → A → Y) : Prop :=
  ∀ g : A → Y, ∃ a, s a = g

def C3_Controlled {A Y : Type _} (t : Y → Y) (p : A → Y) : Prop :=
  ∀ a, t (p a) ≠ p a

def C3_Transparent {A Y : Type _} (s : A → A → Y) (p : A → Y) : Prop :=
  ∀ a, s a a = p a

theorem c3_cch_master {A Y : Type _} (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : C3_Universal s) (hC : C3_Controlled t p) (hT : C3_Transparent s p) :
    False := by
  obtain ⟨a₀, ha₀⟩ := c3_lawvere_point s hU t
  rw [hT a₀] at ha₀
  exact hC a₀ ha₀.symm
```

_Proof._ By {lean}`c3_lawvere_point` applied to `s` and `t` there is an `a₀` with
`s a₀ a₀ = t (s a₀ a₀)`. Transparency at `a₀` rewrites `s a₀ a₀` to `p a₀`, giving
`p a₀ = t (p a₀)`, which says `p a₀` is a fixed point of `t`. Control at `a₀` says
it is not. The two collide. ∎

The three corners are the contrapositives, one per omitted property, and each is a
one-liner off the master theorem.

```lean
theorem c3_cch_corner_UC {A Y : Type _} (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : C3_Universal s) (hC : C3_Controlled t p) : ¬ C3_Transparent s p :=
  fun hT => c3_cch_master s t p hU hC hT

theorem c3_cch_corner_UT {A Y : Type _} (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hU : C3_Universal s) (hT : C3_Transparent s p) : ¬ C3_Controlled t p :=
  fun hC => c3_cch_master s t p hU hC hT

theorem c3_cch_corner_CT {A Y : Type _} (s : A → A → Y) (t : Y → Y) (p : A → Y)
    (hC : C3_Controlled t p) (hT : C3_Transparent s p) : ¬ C3_Universal s :=
  fun hU => c3_cch_master s t p hU hC hT
```

_Proof._ Each supplies the two properties it assumes and derives the falsity of the
third from {lean}`c3_cch_master`. `UC` says a universal controlled system cannot be
transparent, `UT` says a universal transparent system cannot be controlled, and
`CT` says a controlled transparent system cannot be universal. ∎

These three are the reason the result is a trilemma and not merely an impossibility.
You can have any two corners. A universal controlled system exists, but it cannot be
honest about itself. A universal transparent system exists, but it cannot be
controlled. A controlled transparent system exists, but it cannot be universal.
Every real design lives on one edge of the triangle and pays with the opposite
corner. The companion library states exactly these as `cch_corner_UC`,
`cch_corner_UT`, and `cch_corner_CT`, bundles them as `cch_master_trilemma` over a
`CCHStructure`, and records the "at most two of three" reading as `cch_at_most_two`.
It also shows the two verdict trilemmata of this chapter sit inside the master one,
as `hallucination_trilemma_face` and `defense_trilemma_face`, by taking `Y = Bool`,
the controller the flip, and the self-prediction the diagonal.

Each corner is a real class of system, and naming them makes the triangle concrete.
A universal, controlled system that cannot be transparent is an expressive model
under external correction whose self-reports must sometimes be wrong: it can be
steered, and it can do anything, but it cannot honestly say what it will do on
itself. A universal, transparent system that cannot be controlled is an expressive,
honest model that no external controller can always nudge: it says what it will do,
and it does anything, so any controller meets a self-prediction it cannot move. A
controlled, transparent system that cannot be universal is an honest, correctable
model of limited reach: it says what it will do and can be nudged, at the cost of not
realizing every behavior. Real designs sit on edges. An aligned assistant is pushed
toward Control and Transparency and pays with Universality, which is a principled
reading of why safety and capability trade off. A frontier model is pushed toward
Universality and pays with either Control or Transparency, and which one it pays with
is a design decision, not an accident.

**Remark 3.2.** The hallucination and defense trilemmas are the `UC` face of the
master trilemma. Take `Y = Bool`, the controller `t` the flip `!·`, and the
self-prediction `p` the diagonal `a ↦ s a a`. Transparency `s a a = p a` then holds
by the definition of `p`, so a universal system is automatically transparent for this
choice, and control `t (p a) ≠ p a` is {lean}`bool_not_fpf` applied at `p a`. The
master theorem's collision at `a₀` becomes `v p p = !(v p p)`, which is exactly the
liar of {lean}`c3_hallucination_liar`. So the Boolean verdict trilemmata are not
merely analogous to the master trilemma. They are one of its three faces, with
transparency made free by choosing the self-prediction to be the diagonal and control
made the flip. The companion library records this as `hallucination_trilemma_face`
and `defense_trilemma_face`.

## Reading the corners as the three trilemmata

The master trilemma's three properties line up with the desiderata of the verdict
readings, and seeing the correspondence makes the "one theorem" claim concrete at the
level of meaning, not only at the level of proof terms. Universality is the same
reflectivity that runs through the chapter: every behavior is realized. Transparency
is the honesty condition, the system's self-report matching what it does, which in
the Boolean readings is carried by choosing the self-prediction to be the diagonal.
Control is the demand that an external map can always move the self-prediction, and
its Boolean instance is that the flip has no fixed point, which is faithfulness for
hallucination, completeness for defense, and exact separation for coupling wearing
their outward-facing names.

Read this way, each verdict trilemma is the statement that Universality and Control
force the failure of Transparency, or symmetrically that a transparent controlled
system cannot be universal. A faithful covering calibrated model that could also name
every verdict-pattern would be universal, controlled, and transparent at once, and
the master theorem forbids exactly that. The three readings differ in which real
property plays Control and in how believable Universality is, but they agree on the
skeleton, and the skeleton is one corner of the triangle. This is the sense in which
the master trilemma is not a fourth result stacked on three others. It is the frame
that shows the three were always the same corner viewed from three domains.

## Why it is a trilemma, not a dilemma

A reader might ask why the result is stated with three properties when the
impossibility is really about a fixed point. The answer is that the third property is
what makes the conflict a genuine three-way trade rather than a flat contradiction.
Any two of Universality, Control, and Transparency are jointly satisfiable, and the
corner theorems {lean}`c3_cch_corner_UC`, {lean}`c3_cch_corner_UT`, and
{lean}`c3_cch_corner_CT` are the constructive content of that fact turned into
contrapositives. A dilemma would say two things cannot both hold. The trilemma says
three things cannot all hold while any two can, which is a stronger and more useful
statement, because it tells a designer that giving up one property is not only
necessary but sufficient. You do not have to abandon two horns to escape. You abandon
one, and the theorem tells you the other two are then available.

# One proof term

Now the payoff, made literal. The three readings of this chapter are not merely
provable by the same method. As Lean terms they are equal, and the equality is
`rfl`. Each of {lean}`c3_hallucination_trilemma`, {lean}`c3_defense_trilemma`, and
{lean}`c3_coupling_trilemma` is defined as {lean}`no_reflective_verdict` applied to
the same arguments, so they reduce to one another with no computation at all.

```lean
theorem c3_trilemmata_unified {Q : Type _} (v : Q → Q → Bool)
    (h : ∀ g : Q → Bool, ∃ p, v p = g) :
    c3_hallucination_trilemma v h = c3_defense_trilemma v h
      ∧ c3_defense_trilemma v h = c3_coupling_trilemma v h :=
  ⟨rfl, rfl⟩
```

_Proof._ Both components are `rfl`. The three trilemma theorems have the same body,
`no_reflective_verdict v h`, so they are definitionally equal, and the kernel
accepts `rfl` for each equation. ∎

Read what this says. It is not that hallucination, defense, and coupling are
analogous, or that a shared lemma covers them. It is that, once you strip the
readings away, there is one function `v`, one hypothesis on it, and one proof that
the hypothesis is contradictory. The names on the three theorems are labels we
attach for the reader, since the machine sees a single term. That is the sense in which
the title of these notes is exact. There is one diagonal, and the three trilemmata
are it, viewed from three domains.

**Remark 3.3.** It is fair to ask what `rfl` is really checking here, since the three
theorems have different names and different implicit domain variables. Two things
make the equality trivial for the kernel. First, each `c3_` trilemma is _defined_ as
{lean}`no_reflective_verdict` applied to the same `v` and `h`, so after unfolding the
definitions the three bodies are syntactically one term. Second, and more strongly,
all three have type `False`, and `False` is a proposition, so any two of its proofs
are equal by proof irrelevance regardless of how they were built. Either route makes
{lean}`c3_trilemmata_unified` a pair of `rfl`s. The first route is the one that
carries the meaning: the theorems are the same not because all proofs of `False` are
interchangeable, but because these three are the identical construction with three
labels. The kernel would accept the second route even for genuinely different
arguments, which is why the first is the one to cite when claiming the trilemmata are
"the same proof."

The companion `F_13_UnifiedTrilemmata` proves the same `rfl` chain over
`Function.Surjective` as its reflectivity form, and packages the shared boundary
object as `schema_boundary`, the single self-negating query that is hallucination's
boundary question, defense's liar prompt, and coupling's coupled point at once.

# What the readings share, and where they part

It is worth collecting what stays fixed and what moves across the three readings,
because the pattern is the reusable part. Fixed across all three is the engine: a
Boolean verdict, the flip as controller, and universality as the hypothesis. Fixed
too is the witness, a self-negating query that the flip cannot satisfy. What moves is
the meaning of the verdict and, with it, the believability of the universality
premise.

The verdict's meaning moves from "confident and correct" (hallucination) to "made
safe" (defense) to "placed on the true side" (coupling). The two horns that fix the
flip move from "faithful and calibrated" to "complete and utility-preserving" to
"exactly truth-separating." The source of universality moves from "the model imitates
any described behavior" to "prompts are arbitrary text" to "the representation space
encodes any pattern over itself." That last move is the one that changes the
character of the result. Defense's universality is nearly free, hallucination's is
defensible, and coupling's is strong. The topological route of the next chapter
trades all three of these self-reference premises for one geometric premise,
continuity on a connected domain, and reaches the same boundary object with metric
content attached.

There is a temptation, once the `rfl` is in hand, to conclude the three results are
trivial. They are not. The proof is one line because the modeling was done first.
All the content is in Definitions 3.1 through 3.10 and the arguments that they add
up to a reflective verdict. The engine is trivial on purpose; the theorems are as
strong or as weak as the readings that feed it, and auditing a reading is where the
judgment lies.

It is worth setting the three readings against each other in one place. The verdict
means "confident and correct," then "made safe," then "placed on the true side." The
two conditions that fix the flip are "faithful and calibrated," then "complete and
utility-preserving," then "exactly truth-separating." The source of universality is
"an in-context learner imitates any described behavior," then "prompts are arbitrary
text," then "a representation encodes any pattern over itself." The liar witness is
"a self-referential query answered correctly exactly when wrong," then "an injection
made safe exactly when unsafe," then "a representation placed on the true side
exactly when placed on the false side." Reading down these lists, the middle column,
the two conditions, is where standard desiderata do the work, and the bottom source,
universality, is where the believability varies from nearly free (defense) through
defensible (hallucination) to strong (coupling). The topological engine of the next
chapter replaces the entire bottom row with one geometric premise and recovers the
same witnesses with metric content attached.

# The template in four moves

It is useful to extract the recipe, because the same four moves generate every
result in this chapter and most of the ones ahead. First, choose the reading:
decide what a single Boolean `v p q` means in the domain, and what the domain's
self-contexts are. Second, argue the codomain is `Bool` and the controller is the
flip: find the domain condition (calibration, the discrete nature of safety, exact
separation) that makes outcomes two-valued, and the condition (faithfulness,
completeness, separation) that makes the honest self-report the negation of the
diagonal. Third, argue universality: identify the source of self-reference (an
in-context learner, arbitrary text, a self-encoding space) that names every pattern,
and be honest about how strong that source is. Fourth, apply the engine: cite
{lean}`no_reflective_verdict` for the impossibility and {lean}`liar_query` for the
witness, and read the witness back into the domain.

The four moves are not equally hard. The first is a modeling decision, the second is
usually a short argument from a standard desideratum, and the fourth is a single line
of Lean. The weight is in the third, because that is the premise a critic will
contest and the one whose plausibility varies across the readings. When you meet a
new impossibility claim of this shape, run it through the four moves and put your
scrutiny on the third. If the self-reference source is real, the claim stands on
Chapter 1's engine. If it is not, the claim is either false or belongs to the
topological engine of Chapter 4, which pays for the boundary object with connectedness
instead.

This template also explains why the chapter's Lean is so short. Moves one through
three happen in prose, and only move four is code. The proofs are one line each
because the engine was built once, in Chapter 1, and every result here is move four
applied after the prose has done moves one through three. A book that hid the prose
and showed only the code would look like it proved three deep theorems in three
lines. What it actually did was three careful readings and one reused lemma, and the
honesty of the enterprise is in keeping the readings visible.

# A note on axioms and trust

A machine-checked impossibility invites a specific kind of scrutiny, and it is
healthy to say where the trust actually rests. The `c3_` theorems of this chapter are
elaborated by Lean as the book is built, so they are not claims about proofs but
proofs the kernel has accepted. What the kernel guarantees is that, granting Lean's
small set of foundational axioms, the terms have the types their statements assert.
The companion library audits those axioms explicitly and finds that the main results
reduce to the three standard ones, `propext`, `Classical.choice`, and `Quot.sound`,
which are the ordinary footing of classical mathematics in this system. The Boolean
core of this chapter uses even less, because the flip's fixed-point freedom is
decidable and needs no classical principle, a point Chapter 1 made when contrasting
the Boolean Cantor with the propositional Russell.

The trust that verification cannot supply is trust in the _modeling_. No proof
assistant can check that "confident-correctness self-verdict" is the right reading of
a real model, or that a real prompt space is reflective, or that a representation
space encodes patterns over itself. Those are the premises, and they are exactly what
the long middle of each section argues and what the caveats concede. This is the
intended division. The machine certifies that the conclusion follows from the
premises, and the prose argues about whether the premises hold. An impossibility
result is only as strong as its weakest premise, and the value of verifying the
inference is that it leaves the premises as the sole remaining thing to contest. When
someone wants to escape one of these trilemmata, the honest move is to name the
premise they reject, faithfulness, completeness, exact separation, or reflectivity,
and own its cost, not to look for a gap in a proof the kernel has already closed.

# What this chapter does not settle

An impossibility theorem is easy to over-read, and it is worth marking the claims
the chapter does not make. It does not say models hallucinate often, defenses fail
often, or probes mislead often. It produces one query per system and is silent on
frequency. A model could meet its liar on a query no user ever sends and behave
perfectly in practice, and nothing here contradicts that. The frequency question
belongs to the statistical tradition and to the quantitative geometry of Chapter 5,
and the diagonal deliberately says nothing about it.

The chapter also does not say the liar query is easy to find. The diagonal proves
one exists and even names it as a preimage of a specific pattern, but naming a
preimage is not the same as constructing it cheaply. For a large model the
self-context that realizes the diagonal pattern may be hard to elicit, and the cost
of eliciting it is exactly the kind of quantitative content the diagonal cannot see.
An adversary who can search the input space will find injections faster than a random
user, which is why the defense reading is the one where the witness is cheap and the
coupling reading is the one where it may be expensive.

Finally, the chapter does not choose between the diagonal and the topological engine.
Each is right in its domain. The diagonal is the honest tool when self-reference is
real, as it plainly is for prompt injection, and the topological engine is the honest
tool when the domain is a connected space with continuous fields, as it plausibly is
for a representation manifold. The two agree on the boundary object, and the value of
having both is that a given application can be attacked from whichever premise it
actually satisfies. A reader who takes only one engine from these notes has taken
half of them. The next chapter builds the other half, and the chapter after that adds
the metric content that neither engine has on its own.

# Historical and bibliographic notes

The three results have separate origins. The Hallucination Trilemma and its
topological proof are in the companion development's hallucination line, re-derived
in Gödel form as `hallucination_trilemma_godel` in `F_11_HallucinationGodel`, which
also records that the boolean liar `!·` and the real complement `1 - y` are the two
controllers, fixed-point-free everywhere and fixed-point-free off one half
respectively. The Defense Trilemma is the prompt-injection impossibility, re-derived
diagonally as `defense_trilemma_godel` in `F_12_DefenseGodel`, with the real-valued
score version `defense_trilemma_lawvere` alongside it. The coupling theorem is the
subject of the paper "Truth Has a Boundary," whose main statement `boundary_coupling`
is topological, with the diagonal reading collected as `coupling_trilemma_godel` in
`F_13_UnifiedTrilemmata`. The unification into a single master trilemma over
Utility, Control, and Transparency is the `CCHProofs` development, with
`cch_master_trilemma` and the three corner theorems.

The mathematical lineage is Lawvere's 1969 fixed-point theorem, through the reading
of Tarski's undefinability of truth as a diagonal, which Chapter 2 develops. The
statistical inevitability of hallucination is a separate tradition, and it derives
confident falsehood rather than uncertainty; the topological and diagonal arguments
here derive a boundary object instead, and only the stochastic dichotomy
(`stochastic_dichotomy` in the paper) turns that boundary into falsehood with
positive probability. The reading of these classical theorems as constraints on
learning systems is recent, and the machine-checked development these notes follow
is the companion Lean library, built against Mathlib and reducing every main theorem
to the three standard kernel axioms.

A note on how the pieces fit in the companion code. Chapter 1's engine lives in
`F_01_LawvereCore`, the Boolean liar and the hallucination reading in
`F_11_HallucinationGodel`, the defense reading in `F_12_DefenseGodel`, and the
`rfl`-chain unification in `F_13_UnifiedTrilemmata`, whose `schema_boundary`
packages the single self-negating query the three readings share. The master
trilemma and its corners are the `CCHProofs` development, and the topological
coupling theorem with its quantitative refinements is the "Truth Has a Boundary"
artifact. All of them pin the same Lean toolchain and build against the same Mathlib
release, so the cross-references in this chapter are to code that compiles together,
not to three separate projects that happen to share vocabulary.

# Exercises

**Exercise 3.1.** State {lean}`c3_hallucination_trilemma`,
{lean}`c3_defense_trilemma`, and {lean}`c3_coupling_trilemma` side by side and
verify by inspection that their types differ only in the bound variable name for the
domain. Explain why this alone does not prove they are the same theorem, and what
{lean}`c3_trilemmata_unified` adds.

**Exercise 3.2.** In the hallucination reading, write out in plain English the
self-referential query that {lean}`c3_hallucination_liar` produces, and identify
which of the three desiderata (faithful, covering, calibrated) each of the three
possible escapes corresponds to.

**Exercise 3.3.** Prove in Lean that the hallucination and defense trilemmas share a
witness: given `v` and a reflectivity proof `h`, show that the `p` returned by
`c3_hallucination_liar v h` also satisfies the conclusion of
`c3_defense_liar v h`. (Hint: they are the same term; a single `rfl`-style
observation suffices once you have both applied.)

**Exercise 3.4.** The constant model that always answers "not confident-and-correct"
is faithful and calibrated. Show it is not covering, and show it is not reflective by
exhibiting a pattern `g : Q → Bool` it fails to name. Relate this to why Definition
3.3 is needed.

**Exercise 3.5.** (Defense.) Explain why, for prompt injection, the reflectivity
premise `∀ g, ∃ p, v p = g` is close to a restatement of the threat model rather than
an idealization. Then describe one realistic restriction on the prompt space under
which reflectivity fails, and say what part of the argument breaks.

**Exercise 3.6.** (Coupling, harder.) The coupling reading's universality is the
weakest of the three. Write one paragraph arguing that a language model _prompted to
reason about its own probe_ makes the self-encoding real, and one paragraph arguing
that a _passive activation space_ does not. Which one does a probing experiment
actually deploy over?

**Exercise 3.7.** Prove {lean}`c3_lawvere_point` again, this time from
{lean}`lawvere` rather than from scratch, and explain what extra information your
version exposes that {lean}`lawvere` alone does not. (Hint: {lean}`lawvere` asserts a
fixed value exists; you need the index.)

**Exercise 3.8.** Instantiate {lean}`c3_cch_master` with `Y = Bool`, `t` the flip,
and `p` the diagonal `a ↦ s a a`, and check that transparency becomes trivial and
control becomes {lean}`bool_not_fpf` applied pointwise. Conclude that the
hallucination trilemma is the `UC` corner of the master trilemma.

**Exercise 3.9.** Show the three corner theorems are genuinely different by
exhibiting, informally, a system satisfying each pair of properties: one universal
and controlled but not transparent, one universal and transparent but not
controlled, one controlled and transparent but not universal. (You may describe them
in prose; the point is that no edge of the triangle is empty.)

**Exercise 3.10.** Prove in Lean that {lean}`c3_cch_corner_UC` and the other two
corners all reduce to {lean}`c3_cch_master`, and state the "at most two of three"
theorem `c3_cch_at_most_two` as an alias for {lean}`c3_cch_master`. Compare with the
companion `cch_at_most_two`.

**Exercise 3.11.** (Reading audit.) For each of the three trilemmata, name the two
horns that fix the flip and the one hypothesis that supplies universality. Arrange
the three universality sources on a scale from "free" to "strong" and defend the
ordering.

**Exercise 3.12.** The topological proofs deliver a coupled point with metric
content: an ambiguity tube of width set by Lipschitz constants. The diagonal proof
delivers only the point. Explain what quantitative question the diagonal cannot
answer, and why Chapter 5 needs the analytic engine rather than this one.

**Exercise 3.13.** (Harder, Lean.) Define a `c3_`-prefixed predicate
`C3_Faithful` on `v : Q → Q → Bool` capturing "no self-verdict equals its own
negation," `∀ p, v p p ≠ !(v p p)`. Prove that a reflective `v` cannot be
`C3_Faithful`, using {lean}`c3_hallucination_liar`. Which single lemma does the
whole proof reduce to?

**Exercise 3.14.** (Coupling versus topology.) The paper's `faithful_iff_boundary_free`
says a threshold-inclusive guarantee is possible exactly when no boundary query
exists. Restate this in the diagonal language of this chapter, with "boundary query"
read as the liar witness, and explain why reflectivity is what removes the escape.

**Exercise 3.15.** (Open-ended.) The engine needs Boolean outcomes and the flip.
Chapter 6 relaxes the flip to the real complement, fixed-point-free off one half,
and Chapter 4 relaxes reflectivity to continuity on a connected space. Sketch what a
_single_ theorem covering both relaxations would need to assume, and which of this
chapter's three readings would survive each relaxation most comfortably.

**Exercise 3.16.** (Synthesis.) Write a one-page account, for a reader who knows no
Lean, of why "there is no total exact self-applicable truth predicate" is the same
statement as "no faithful calibrated covering model, no complete utility-preserving
defense, and no exactly truth-separating probe over a self-encoding space." Use the
liar witness as the common thread and avoid all symbols.

**Exercise 3.17.** (Section form.) Following Remark 3.0, restate
{lean}`c3_hallucination_trilemma` using a section `s : (Q → Bool) → Q` with
`v (s g) = g` in place of the surjection, and prove it by feeding the diagonal
pattern to `s`. Explain why, for auditing a real model, the section form is the more
honest premise to check.

**Exercise 3.18.** (Master to verdict.) Carry out Remark 3.2 in Lean: instantiate
{lean}`c3_cch_master` with `Y = Bool`, `t` the flip, and `p := fun a => s a a`, and
discharge transparency by `rfl` and control by {lean}`bool_not_fpf`. Confirm that the
result you obtain is {lean}`c3_hallucination_trilemma` in disguise.

**Exercise 3.19.** (Grading premises.) Write a short paragraph for each trilemma
naming the single premise you would attack to escape it in a real deployment, and the
concrete engineering cost of dropping that premise. Rank the three escapes by which is
most defensible in practice and justify the ranking.

**Exercise 3.20.** (Open-ended.) The coupling reading has the strongest reflectivity
premise. Design an experiment, in prose, that would give evidence _for_ or _against_ a
representation space encoding patterns over its own states, and say what a negative
result would imply for the diagonal reading versus the topological one.

**Exercise 3.21.** (Micro-instance.) Redo the worked micro-instance with a
four-element domain and diagonal entries of your choosing. Write out the flip
pattern, confirm it matches no row, and identify the liar row that a claimed
reflectivity proof would produce. Then argue in one sentence why the same reasoning
never bottoms out no matter how large you make the domain.

**Exercise 3.22.** (Controllers.) The hallucination and defense readings use the
Boolean flip, and their real-valued cousins use the complement `y ↦ 1 - y`. Prove in
Lean that {lean}`bool_not_fpf` gives a fixed-point-free flip on `Bool`, and explain
in prose why the complement is fixed-point-free everywhere except at one half. What
does the exceptional point at one half correspond to in the hallucination reading?

**Exercise 3.23.** (Master corners are nonempty.) For the master trilemma, sketch a
concrete `CCHStructure` witnessing each of the three achievable pairs: universal and
controlled, universal and transparent, controlled and transparent. Confirm that each
of your witnesses fails the omitted property, so that no corner of the triangle is
vacuous.

**Exercise 3.24.** (Detection revisited.) A colleague proposes a defense that detects
and refuses any prompt referring to the wrapper. State precisely, in the language of
Definitions 3.5 through 3.7, which property their defense gives up, and prove in Lean
that a wrapper which refuses the liar prompt cannot satisfy completeness at that
prompt. (Hint: refusal assigns a Boolean value; completeness demands the other one.)

**Exercise 3.25.** (Tarski identity.) Using the coupling reading, write out the
correspondence between Tarski's liar sentence and the coupled query, term by term:
sentence, truth predicate, self-reference, and the fixed-point-free flip. Then say
which single hypothesis of the coupling reading is doing the work that Tarski's
"sufficiently expressive language" does, and why it is the strong one.

**Exercise 3.26.** (Two engines, one witness.) The diagonal and the topological
proofs produce the same boundary object. Write a paragraph explaining what the
topological proof knows about that object that the diagonal does not, and what the
diagonal knows that the topological proof needs a connected domain to obtain. Use the
ambiguity tube and the reflectivity premise as your two examples.

**Exercise 3.27.** (Synthesis, harder.) Prove in Lean a single theorem, prefixed
`c3_`, that takes a verdict `v` and a reflectivity proof and returns the conjunction
of `False` (the impossibility) and `∃ p, v p p = !(v p p)` (the witness), by pairing
{lean}`no_reflective_verdict` with {lean}`liar_query`. Explain why this one theorem is
a faithful summary of all three trilemmata at once.
