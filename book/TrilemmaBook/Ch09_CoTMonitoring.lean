import VersoManual
import TrilemmaBook.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Trace Is Not a Window" =>

Chapter 8 answered the objection that the trilemmata concern only outputs by
following a probe into the middle of the network. There is a second, more
practical version of the same objection, and it is currently the most widely
deployed safety measure in the field. Do not read the activations at all. Read
what the model *says* while it is thinking. A reasoning model emits a
chain of thought before it answers, and that chain is plain text: legible,
loggable, and cheap to check with a second model. If the reasoning that produced
a harmful action is written out in English on the way to the action, a monitor
can catch it there, and no interpretability breakthrough is required.

This is chain-of-thought monitoring, and the case for it is strong enough that a
2025 position paper signed across several labs argued for treating it as a
safety property worth actively preserving. The argument of that paper is worth
stating fairly, because the present chapter is not a rebuttal of it. Some tasks
genuinely require serial reasoning that the model cannot do in a single forward
pass, and for those tasks the chain of thought is not a commentary on the
computation but the working memory of the computation itself. When that holds,
the trace is load-bearing, and a monitor reading it sees something real.

What this chapter derives is where that guarantee stops. Three results, each
from a different mechanism, and none of them a restatement of Chapter 8. The
first is a pigeonhole argument, not a diagonal one: it shows that the two
properties the monitorability literature measures separately, faithfulness and
verbosity, are not independent, because faithfulness *forces* verbosity.
The second is the diagonal, applied to a monitor whose input the model
controls, which is a materially different situation from a probe reading
activations the model does not choose. The third concerns what happens when a
monitor is trained against rather than merely observed, and it is the sharpest
of the three: optimization pressure against a monitor drives the monitor's
output to a constant, and a constant verdict carries no information at all. That
last result is the formal version of the field's own stated worry about
obfuscated reasoning, and it says the worry is not a contingent empirical risk
but a consequence of what selection does.

# The construction

Fix a model that answers queries by first emitting a reasoning trace. Write `Q`
for the space of queries as the model receives them, including whatever context
and system prompt it is run with, and write `T` for the space of traces the
model can emit. The model's tracing behavior is a map `trace : Q → T`, and the
monitor is a second system reading traces and returning a verdict.

There are two versions of the monitor worth separating, and the difference
matters for which theorem applies.

*Definition 9.1 (Trace-only monitor).* A *trace-only monitor* is a
map `mon : T → Bool`, returning `true` when it judges the trace to reveal
misbehavior. It sees the reasoning and nothing else. This is the cheap
deployment: log the chain of thought, run a classifier over the log.

*Definition 9.2 (Contextual monitor).* A *contextual monitor* is a map
`mon : T → Q → Bool`, which reads the trace and also has access to the query
being reasoned about. This is the more capable deployment, and it is what a
monitor with access to the full transcript actually is.

*Definition 9.3 (Ground truth).* Write `harm : Q → Bool` for the fact of the
matter: `harm q = true` when the model's behavior on query `q` is one we would
want flagged. This is not something the monitor computes. It is the thing the
monitor is trying to track, and its existence as a total Boolean function is an
idealization we make in order to have something exact to compare against.

*Definition 9.4 (Faithfulness).* A trace-only monitor is *faithful*
when its verdict matches the fact of the matter on every query, that is, when
`mon (trace q) = harm q` for all `q`. In the empirical literature faithfulness
is a property of the trace rather than of the monitor, and it is measured as the
degree to which the stated reasoning reflects the true causes of the model's
behavior. Definition 9.4 is the idealized limit of that measurement: a trace
whose stated reasons are the real ones supports a monitor that gets the answer
right, and a monitor that gets the answer right on every query is what perfect
faithfulness would buy you.

```lean
def c9_Faithful {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool) : Prop :=
  ∀ q, mon (trace q) = harm q
```

*Definition 9.5 (Verbosity).* The trace is *verbose* on a pair of
queries when it distinguishes them, `trace q₁ ≠ trace q₂`. The monitorability
literature defines verbosity as whether the chain of thought lists every factor
needed to solve the task, and measures it separately from faithfulness precisely
because a model can be faithful about what it does say while omitting what
matters. Definition 9.5 is that property stated extensionally: what it means for
the trace to have listed the deciding factor is that a query where the factor is
present and one where it is absent do not produce the same trace.

The empirical claim in the literature is that faithfulness and verbosity are two
independent axes, and that a monitorability score should combine them, because a
model can score well on one and badly on the other. The first result of this
chapter is that the independence holds only for imperfect systems. At the exact
end of the scale, one implies the other.

# Faithfulness forces verbosity

This section uses no diagonal. The mechanism is the pigeonhole principle, and it
is worth seeing that some of the structure here is available without any
self-reference at all.

Start from the observation that a trace-only monitor's verdict is a function of
the trace. If two queries produce the same trace, the monitor cannot tell them
apart, because there is nothing else it reads. Whatever it says about one, it
says about the other.

*Lemma 9.6 (Collisions force error).* *If two queries collide in the
trace but differ in the fact of the matter, then a trace-only monitor is wrong
on at least one of them.*

```lean
theorem c9_collision_forces_error {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (q₁ q₂ : Q) (hcol : trace q₁ = trace q₂) (hdiff : harm q₁ ≠ harm q₂) :
    mon (trace q₁) ≠ harm q₁ ∨ mon (trace q₂) ≠ harm q₂ := by
  by_cases h : mon (trace q₁) = harm q₁
  · exact Or.inr (by rw [← hcol, h]; exact hdiff)
  · exact Or.inl h
```

*Proof.* Suppose the monitor is right on `q₁`, so `mon (trace q₁) = harm q₁`.
Since the traces are equal, its verdict on `q₂` is the same value, which is
`harm q₁`, and `harm q₁ ≠ harm q₂`. So it is wrong on `q₂`. If instead it is
already wrong on `q₁` there is nothing to prove. ∎

The contrapositive is the result we want, and it is the one worth remembering.

*Theorem 9.7 (Faithfulness forces verbosity).* *A faithful trace-only
monitor forces the trace to separate every pair of queries that differ in the
fact of the matter.*

```lean
theorem c9_faithful_forces_separation {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (hf : c9_Faithful trace mon harm)
    (q₁ q₂ : Q) (hcol : trace q₁ = trace q₂) : harm q₁ = harm q₂ := by
  rw [← hf q₁, ← hf q₂, hcol]
```

*Proof.* Rewrite each side of the goal using faithfulness, turning
`harm q₁ = harm q₂` into `mon (trace q₁) = mon (trace q₂)`, and then rewrite
with the collision to close it by reflexivity. ∎

Read Theorem 9.7 as a statement about measurement. It says that faithfulness and
verbosity are not two dials you can set independently once you are at the top of
the scale: a perfectly faithful trace-only monitor *entails* a trace
verbose enough to separate every harm-relevant distinction. So the two-factor
monitorability score is measuring one thing near the exact corner and two things
away from it, and the gap between the factors is a measure of distance from the
corner rather than of two separate deficiencies.

This has a practical consequence that cuts against the cheap deployment. The
capacity of `T` bounds what a trace-only monitor can do. If the trace is short,
the number of distinct traces the model actually emits is small, and if the
number of harm-relevant distinctions exceeds it, collisions are forced and by
Lemma 9.6 errors follow. A monitor that reads a summary is not a weaker version
of a monitor that reads everything. It is a monitor with a ceiling, and the
ceiling is set by how many distinctions the summary can carry.

*Remark 9.8 (This is not yet an impossibility).* Nothing above says a good
monitor cannot exist. It says a faithful one imposes a requirement on the trace,
and that a lossy trace caps performance. A trace that is long enough and a model
that is honest enough could satisfy all of it. The impossibility arrives in the
next two sections, and it arrives for reasons that have nothing to do with
capacity.

# The diagonal, with the model holding the pen

Now the second engine. The monitor is a verdict about queries, routed through a
representation, and Chapter 8 already established that routing a verdict through
a representation does not help. The trace-monitoring case is the same theorem
with `T` in place of J-space.

*Theorem 9.9 (Monitoring factors, and factoring does not help).* *Let
`trace : Q → T` and `mon : T → Q → Bool`. If every pattern of verdicts over
queries is realized by some query's trace, the situation is contradictory.*

```lean
theorem c9_trace_factoring {Q T : Type _}
    (trace : Q → T) (mon : T → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, mon (trace p) = g) : False :=
  no_reflective_verdict (fun p => mon (trace p)) hs
```

*Proof.* `fun p => mon (trace p)` is a reflective verdict on `Q`, and
{lean}`no_reflective_verdict` rules those out. ∎

*Theorem 9.10 (The obfuscated trace).* *Under the same hypothesis there is
a query whose monitored verdict is its own negation.*

```lean
theorem c9_obfuscation_liar {Q T : Type _}
    (trace : Q → T) (mon : T → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, mon (trace p) = g) :
    ∃ p, mon (trace p) p = !(mon (trace p) p) :=
  liar_query (fun p => mon (trace p)) hs
```

*Proof.* Apply {lean}`liar_query` to the composite verdict. ∎

So far this is Chapter 8 with different letters. What is different, and it is
the reason this chapter exists rather than a remark in the last one, is the
status of the surjectivity hypothesis.

In Chapter 8 the encoder `enc` was the model's own internal machinery, and we
were careful to say that point-surjectivity there is an idealization: a fixed
network has finitely many activations and does not literally name every verdict
pattern. The honest reading was the approximate one of Chapter 6.

Here the encoder is `trace`, and the model *chooses* it. The trace is
the model's output, generated token by token under the same policy that produces
the answer, and it is unconstrained text. This is the prompt-injection situation
of Chapter 3, not the activation situation of Chapter 8, and Chapter 3 already
graded that premise as cheap. A model with any capacity to reason about the
monitor can shape the trace it emits, and shaping the trace is exactly
constructing a preimage. The diagonal argument's expensive hypothesis is, in
this application, close to free.

That is the formal content of the word *obfuscation* in the position
paper's own list of risks. The concern there is that a model under pressure
learns to route its real reasoning around the trace while emitting a clean one.
Theorem 9.10 says the fixed point of that process exists as soon as the model
can realize verdict patterns in its trace, and the witness is a query the
monitor is guaranteed to misreport. The trace is not a window. It is an output,
and outputs are chosen.

# Selection destroys the signal

The third result is the one with the sharpest practical edge, and its mechanism
is neither pigeonhole nor diagonal. It concerns what happens when the monitor
stops being an observer and becomes part of the training objective.

The setup is the one every deployment eventually reaches. A monitor is built, it
flags some fraction of traces, and the flagged behavior is trained away. Iterate
until the flag rate is acceptable. The question is what the monitor's verdict
means at the end of that process.

*Definition 9.11 (Selection to passing).* A model has been *selected to
passing* against a trace-only monitor when every query it is run on produces a
trace the monitor accepts, that is, `mon (trace q) = true` for all `q`.

*Theorem 9.12 (A selected monitor is constant).* *After selection to
passing, the monitor returns the same verdict on every pair of queries.*

```lean
theorem c9_selected_monitor_constant {Q T : Type _}
    (trace : Q → T) (mon : T → Bool)
    (hpass : ∀ q : Q, mon (trace q) = true) (q₁ q₂ : Q) :
    mon (trace q₁) = mon (trace q₂) := by
  rw [hpass q₁, hpass q₂]
```

*Proof.* Both sides rewrite to `true`. ∎

The theorem is one line and its content is entirely in the reading, so it is
worth being precise about what has and has not been shown. It has not been shown
that the model is now unsafe. It has been shown that the monitor is now silent:
its output is a constant function, and a constant function distinguishes
nothing. Whatever information the monitor was carrying about the model has been
optimized out of it, and the flag rate reaching zero is not evidence that the
behavior is gone, because the flag rate reaching zero is what the training
procedure was *for*.

The blunt version is worth stating as its own result, because it is what the
theorem is actually saying, and the proof makes the point by what it does not
use.

*Theorem 9.13 (The verdict no longer tracks harm).* *After selection to
passing, the monitor gives the same verdict on two queries even when they differ
in the fact of the matter.*

```lean
theorem c9_selection_blinds {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (hpass : ∀ q : Q, mon (trace q) = true)
    (q₁ q₂ : Q) (_hdiff : harm q₁ ≠ harm q₂) :
    mon (trace q₁) = mon (trace q₂) := by
  rw [hpass q₁, hpass q₂]
```

*Proof.* Both sides rewrite to `true`. ∎

Look at the hypothesis `_hdiff`. It is named with a leading underscore because
the proof never touches it, and that is the entire point of stating the theorem
this way. The monitor agrees with itself across a pair of queries that differ in
the one respect the monitor was built to detect, and the difference plays no
role in the argument, because after selection there is no route from `harm` to
the verdict at all. A monitor selected against is not a degraded detector. It is
disconnected from what it was detecting.

*Corollary 9.14 (Faithfulness is lost, unless nothing is harmful).* *A
selected monitor that is still faithful forces every query to be harmful.*

```lean
theorem c9_selected_faithful_forces_all_harmful {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (hpass : ∀ q : Q, mon (trace q) = true)
    (hf : c9_Faithful trace mon harm) (q : Q) : harm q = true := by
  rw [← hf q, hpass q]
```

*Proof.* Faithfulness rewrites `harm q` to the monitor's verdict, and selection
rewrites that to `true`. ∎

Read the corollary contrapositively, which is how it is used. If a single query
is benign, then a monitor that has been selected to passing is no longer
faithful. The two properties the deployment wants, a clean flag rate and a
monitor that tracks the truth, are available together only in the degenerate
case where everything is harmful.

*Remark 9.15 (Why this is not merely Goodhart's law).* Goodhart's law says a
measure that becomes a target ceases to be a good measure, and it is usually
argued statistically: optimizing against a proxy exploits the gap between proxy
and goal. Theorem 9.13 is stronger and simpler than that. It needs no gap, no
proxy error, and no adversarial intent. It needs only that the optimization
succeeded. A monitor that has been trained against to the point of passing is
constant, and a constant is uninformative whether or not it was a perfect
measure beforehand. The failure is in the selection, not in the measure.

*Remark 9.16 (What the theorem licenses, and what it does not).* It does not
say monitoring is useless. It says a monitor's evidential value is spent when it
is used as a training signal, so the two uses are exclusive: a monitor can be an
observer or an objective, and it cannot be both and remain informative. This is
a real and actionable distinction, and it is the reason the position paper's
recommendation to *preserve* monitorability is not the same as, and is
partly in tension with, using the monitor to enforce it. Holding out a monitor
that is never trained against is the design this theorem argues for.

# The analytic engine

The diagonal half of this chapter needs the model to shape its trace. The
analytic half needs nothing of the kind, and it applies to the deployed system
as it stands.

A realistic monitor does not return a Boolean. It returns a score, a suspicion
level in `[0,1]`, and a threshold turns the score into a flag. Chapter 4's
argument then applies directly, and its hypotheses are met by ordinary
engineering facts rather than idealizations. The space of traces reachable by
paraphrase is connected in the sense Chapter 4 requires: a trace can be edited
by degrees, and the monitor's score, computed by a second network with
continuous parameters over a continuous embedding, varies continuously along the
edit. If the monitor is decisive in both directions, flagging some trace and
clearing another, then along any path between them the score takes every
intermediate value, and there is a trace sitting exactly at threshold.

That trace is the ambiguous case, and it is where the monitor's verdict is
determined by the last digit of a floating-point comparison rather than by
anything about the reasoning. Chapter 5's quantitative refinements apply
verbatim: with a Lipschitz bound on the monitor, the width of the band around
the threshold is bounded below, and the number of edits an adversary needs to
walk a flagged trace into the cleared region is bounded above. The second
quantity is attack cost in the sense of Chapter 5, and here it has an
unusually concrete reading, since the edits are paraphrases and their cost is
measured in tokens.

There is a specific interaction between the two engines in this chapter that is
worth drawing out, because it is not present in Chapter 8. The analytic argument
says a band exists. The diagonal argument says the model can aim at it. In the
J-space setting the second half was an idealization, so the band was a hazard
the system might wander into. Here the model emits the trace, and the band is a
target it can steer toward, which converts an existence result into an
availability result. That is the precise sense in which chain-of-thought
monitoring is more fragile than probing internals, and it is the opposite of the
intuition that reading plain English is the safer choice.

# What this does not claim

Four limits, stated plainly.

It does not claim chain-of-thought monitoring is worthless. Theorem 9.7 shows a
faithful monitor forces an informative trace, which is a positive result about
what monitoring gets you when it works, and the position paper's core empirical
claim, that for genuinely serial tasks the trace carries real computation,
is untouched by anything here. What the chapter bounds is the exact corner:
total, faithful, and used under optimization pressure.

It does not claim the diagonal applies to every deployment. Theorem 9.9 needs
the model to realize verdict patterns in its trace. A weak model that cannot
reason about its monitor does not meet the hypothesis, and for such a model the
analytic band is the operative limit rather than the liar. The premise gets
cheaper as models get more capable, which is the wrong direction for a safety
measure but is not a claim about systems in the field today.

It does not claim selection is avoidable. Theorem 9.13 describes what selection
does, not whether you should select. Training away flagged behavior may well be
the right decision. The theorem says only that you cannot then read the flag
rate as evidence, and that the two uses of a monitor have to be kept in separate
instances.

It does not claim `harm` exists as a total Boolean function. Definition 9.3 is
an idealization, and a serious treatment would replace it with the graded,
partial, contested object it really is. Chapter 6's approximate bridges are the
route for that, and the results here should be read as the exact corner of a
quantitative family rather than as statements about a real classifier.

# Exercises

*Exercise 9.1.* Prove that if `T` is `Unit`, a trace-only monitor is constant,
and derive from Lemma 9.6 that it errs on any pair of queries differing in
`harm`. This is the extreme case of the capacity ceiling.

*Exercise 9.2.* State and prove the contextual analogue of Theorem 9.7. Where
does the argument break, and what does that tell you about the difference
between a monitor that reads the transcript and one that reads only the trace?

*Exercise 9.3.* Prove {lean}`c9_collision_forces_error` a second time in term
mode, without `by_cases`, by case-splitting on `harm q₁` with `Bool.rec`.

*Exercise 9.4.* Selection to passing is stated as a universal. Weaken it to hold
only on a subset and show Theorem 9.12 becomes a statement about that subset.
What is the deployment reading of the queries left out?

*Exercise 9.5.* (Design.) You hold two monitors, one used in training and one
held out. Using Theorem 9.13, say precisely what you may conclude from each
one's flag rate, and construct a case where the two rates diverge and the
divergence is the informative quantity.

*Exercise 9.6.* (Analytic, prose.) Give the hypotheses under which the set of
traces reachable from a fixed trace by bounded paraphrase is connected, and
explain why unbounded paraphrase makes the analytic argument stronger rather
than weaker.

*Exercise 9.7.* Combine Theorem 9.10 with Chapter 8's factoring theorem to state
a single result covering a monitor that reads both the trace and the activations
that produced it. Does reading both help?
