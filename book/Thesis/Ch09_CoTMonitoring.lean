import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Trace Is Not a Window" =>

Chapter 8 answered the outputs-only objection by following a probe into the
network. There is a second, more practical version, and it is the most widely
deployed safety measure in the field: do not read the activations, read what the
model _says_ while thinking. A reasoning model emits a chain of thought, and
that chain is plain text — legible, loggable, cheap to check with a second
model.

The case for chain-of-thought monitoring is strong, and this chapter is not a
rebuttal. Some tasks genuinely require serial reasoning the model cannot do in
one forward pass, and there the trace is not commentary but the working memory
of the computation, so a monitor reading it sees something real.

What follows is where that guarantee stops. Three results from three mechanisms.
A pigeonhole argument showing that faithfulness and verbosity, which the
monitorability literature measures separately, are not independent, because
faithfulness _forces_ verbosity.

# The construction

Write `Q` for queries as received, `T` for traces, and `trace : Q → T` for the
tracing behavior.

*Definition 9.1 (Trace-only monitor).* A map `mon : T → Bool`, `true` when it judges
the trace to reveal misbehavior. It sees the reasoning and nothing else: log the
chain of thought, run a classifier over the log.

*Definition 9.2 (Contextual monitor).* A map `mon : T → Q → Bool`, reading the trace
and the query. This is what a monitor with the full transcript is.

*Definition 9.3 (Ground truth).* `harm : Q → Bool` is the fact of the matter. The
monitor does not compute it; it tries to track it. Its existence as a total
Boolean function is an idealization made to have something exact to compare
against.

*Definition 9.4 (Faithfulness).* A trace-only monitor is _faithful_ when
`mon (trace q) = harm q` for all `q`.

```lean
def c9_Faithful {Q T : Type _}
    (trace : Q → T) (mon : T → Bool)
    (harm : Q → Bool) : Prop :=
  ∀ q, mon (trace q) = harm q
```

In the empirical literature faithfulness is a property of the trace, measured as
the degree to which stated reasoning reflects true causes. Definition 9.4 is the
idealized limit of that measurement.

*Definition 9.5 (Verbosity).* The trace is _verbose_ on a pair when it distinguishes
them, `trace q₁ ≠ trace q₂`. The literature defines verbosity as whether the
chain lists every factor needed, and measures it separately from faithfulness
precisely because a model can be faithful about what it says while omitting what
matters. Definition 9.5 states that extensionally.

The empirical claim is that the two are independent axes. The first result is
that the independence holds only for imperfect systems: at the exact end of the
scale, one implies the other.

# Faithfulness forces verbosity

This uses no diagonal. The mechanism is pigeonhole. A trace-only monitor's
verdict is a function of the trace, so if two queries produce the same trace the
monitor cannot tell them apart.

*Lemma 9.6 (Collisions force error).* _If two queries collide in the trace but differ
in the fact of the matter, a trace-only monitor is wrong on at least one._

```lean
theorem c9_collision_forces_error {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (q₁ q₂ : Q) (hcol : trace q₁ = trace q₂)
    (hdiff : harm q₁ ≠ harm q₂) :
    mon (trace q₁) ≠ harm q₁ ∨ mon (trace q₂) ≠ harm q₂ :=
      by
  by_cases h : mon (trace q₁) = harm q₁
  · exact Or.inr (by rw [← hcol, h]; exact hdiff)
  · exact Or.inl h
```

_Proof._ If the monitor is right on `q₁`, its verdict on `q₂` is the same value, which
is `harm q₁ ≠ harm q₂`, so it is wrong there. Otherwise it is already wrong on
`q₁`. ∎

*Theorem 9.7 (Faithfulness forces verbosity).* _A faithful trace-only monitor forces
the trace to separate every pair of queries differing in the fact of the
matter._

```lean
theorem c9_faithful_forces_separation {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (hf : c9_Faithful trace mon harm)
    (q₁ q₂ : Q) (hcol : trace q₁ = trace q₂) :
    harm q₁ = harm q₂ := by
  rw [← hf q₁, ← hf q₂, hcol]
```

_Proof._ Rewrite both sides by faithfulness, then by the collision. ∎

Read this as a statement about measurement. Faithfulness and verbosity are not
dials you set independently at the top of the scale: a perfectly faithful
trace-only monitor _entails_ a trace verbose enough to separate every
harm-relevant distinction. The two-factor monitorability score measures one
thing near the exact corner and two things away from it, so the gap between the
factors is a measure of distance from the corner rather than of two separate
deficiencies.

The practical consequence cuts against the cheap deployment. The capacity of `T`
bounds what a trace-only monitor can do: if the trace is short, the distinct
traces are few, and once the harm-relevant distinctions exceed them collisions
are forced and errors follow. A monitor reading a summary is not a weaker
version of one reading everything. It is a monitor with a ceiling set by how
many distinctions the summary can carry.

*Remark 9.8 (This is not yet an impossibility).* Nothing above says a good monitor
cannot exist. It says a faithful one imposes a requirement on the trace, and a
lossy trace caps performance. The impossibility arrives next, for reasons having
nothing to do with capacity.

# The diagonal, with the model holding the pen

*Theorem 9.9 (Monitoring factors, and factoring does not help).* _If every verdict
pattern over queries is realized by some query's trace, the situation is
contradictory._

```lean
theorem c9_trace_factoring {Q T : Type _}
    (trace : Q → T) (mon : T → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, mon (trace p) = g) : False :=
  no_reflective_verdict (fun p => mon (trace p)) hs
```

_Proof._ The composite is a reflective verdict. ∎

*Theorem 9.10 (The obfuscated trace).* _Under the same hypothesis some query's
monitored verdict is its own negation._

```lean
theorem c9_obfuscation_liar {Q T : Type _}
    (trace : Q → T) (mon : T → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, mon (trace p) = g) :
    ∃ p, mon (trace p) p = !(mon (trace p) p) :=
  liar_query (fun p => mon (trace p)) hs
```

_Proof._ {lean}`liar_query` on the composite. ∎

So far this is Chapter 8 with different letters. What differs, and is why this
chapter exists, is the status of the surjectivity hypothesis. In Chapter 8 the
encoder was the model's internal machinery and point-surjectivity was an
idealization.

That is the formal content of _obfuscation_. Theorem 9.10 says the fixed point
of the process exists as soon as the model can realize verdict patterns in its
trace, and the witness is a query the monitor is guaranteed to misreport. The
trace is not a window. It is an output, and outputs are chosen.

# Selection destroys the signal

The third result's mechanism is neither pigeonhole nor diagonal. A monitor is
built, it flags some traces, the flagged behavior is trained away, and the loop
iterates until the flag rate is acceptable. What does the verdict mean at the
end?

*Definition 9.11 (Selection to passing).* A model is _selected to passing_ when every
query produces a trace the monitor accepts, `mon (trace q) = true` for all `q`.

*Theorem 9.12 (A selected monitor is constant).* _After selection to passing, the
monitor returns the same verdict on every pair of queries._

```lean
theorem c9_selected_monitor_constant {Q T : Type _}
    (trace : Q → T) (mon : T → Bool)
    (hpass : ∀ q : Q, mon (trace q) = true) (q₁ q₂ : Q) :
    mon (trace q₁) = mon (trace q₂) := by
  rw [hpass q₁, hpass q₂]
```

_Proof._ Both sides rewrite to `true`. ∎

The content is entirely in the reading. It has not been shown that the model is
now unsafe. It has been shown that the monitor is now silent: its output is
constant, and a constant distinguishes nothing. Whatever information it carried
has been optimized out, and the flag rate reaching zero is not evidence the
behavior is gone, because that is what the training procedure was _for_.

*Theorem 9.13 (The verdict no longer tracks harm).* _After selection, the monitor gives
the same verdict on two queries even when they differ in the fact of the
matter._

```lean
theorem c9_selection_blinds {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (hpass : ∀ q : Q, mon (trace q) = true)
    (q₁ q₂ : Q) (_hdiff : harm q₁ ≠ harm q₂) :
    mon (trace q₁) = mon (trace q₂) := by
  rw [hpass q₁, hpass q₂]
```

_Proof._ Both sides rewrite to `true`. ∎

The hypothesis `_hdiff` carries a leading underscore because the proof never
touches it, and that is the point. The monitor agrees with itself across a pair
differing in the one respect it was built to detect, and the difference plays no
role, because after selection there is no route from `harm` to the verdict at
all. A monitor selected against is not a degraded detector; it is disconnected
from what it was detecting.

*Corollary 9.14 (Faithfulness is lost, unless nothing is harmful).* _A selected monitor
that is still faithful forces every query to be harmful._

```lean
theorem c9_selected_faithful_forces_all_harmful
    {Q T : Type _}
    (trace : Q → T) (mon : T → Bool) (harm : Q → Bool)
    (hpass : ∀ q : Q, mon (trace q) = true)
    (hf : c9_Faithful trace mon harm)
    (q : Q) : harm q = true := by
  rw [← hf q, hpass q]
```

_Proof._ Faithfulness rewrites `harm q` to the verdict, selection rewrites that to
`true`. ∎

Read contrapositively: if a single query is benign, a monitor selected to
passing is no longer faithful. A clean flag rate and a monitor that tracks truth
are available together only in the degenerate case where everything is harmful.

*Remark 9.15 (Why this is not merely Goodhart's law).* Goodhart is usually argued
statistically: optimizing a proxy exploits the gap between proxy and goal.
Theorem 9.13 needs no gap, no proxy error, and no adversarial intent. It needs
only that the optimization succeeded. The failure is in the selection, not in
the measure.

*Remark 9.16 (What the theorem licenses).* It does not say monitoring is useless. It says
a monitor's evidential value is spent when it is used as a training signal, so
the two uses are exclusive: a monitor can be an observer or an objective, not
both and remain informative. Holding out a monitor never trained against is the
design this argues for, and it is in partial tension with using the monitor to
enforce monitorability.

# The analytic engine

The diagonal half needs the model to shape its trace; the analytic half needs
nothing of the kind and applies to the deployed system as it stands.

A realistic monitor returns a suspicion score and thresholds it. Chapter 4
applies directly, with hypotheses met by ordinary engineering facts. The traces
reachable by paraphrase are connected in the required sense — a trace can be
edited by degrees — and the score, computed by a second network with continuous
parameters over a continuous embedding, varies continuously along the edit.

That trace is the ambiguous case, where the verdict is decided by the last digit
of a floating-point comparison rather than by anything about the reasoning.
Chapter 5 applies verbatim: a Lipschitz bound puts a floor under the band width
and a ceiling on the number of edits needed to walk a flagged trace into the
cleared region. The second quantity is attack cost, and here it has an unusually
concrete reading, since the edits are paraphrases and their cost is measured in
tokens.

The interaction between the engines is sharper here than in Chapter 8. The
analytic argument says a band exists; the diagonal says the model can aim at it.
In J-space the second half was an idealization, so the band was a hazard the
system might wander into.

# What this does not claim

It does not claim monitoring is worthless. Theorem 9.7 is a positive result
about what monitoring gets you when it works, and the empirical claim that for
serial tasks the trace carries real computation is untouched. What is bounded is
the exact corner: total, faithful, and used under optimization pressure.

It does not claim the diagonal applies to every deployment. Theorem 9.9 needs
the model to realize verdict patterns in its trace. A weak model cannot, and for
it the analytic band is the operative limit. The premise gets cheaper as models
get more capable, which is the wrong direction for a safety measure.

It does not claim selection is avoidable. Theorem 9.13 describes what selection
does, not whether you should select. It says only that you cannot then read the
flag rate as evidence, and that the two uses need separate instances.

It does not claim `harm` exists as a total Boolean function. Definition 9.3 is
an idealization, and Chapter 6's bridges are the route to the graded, partial,
contested object it really is.
