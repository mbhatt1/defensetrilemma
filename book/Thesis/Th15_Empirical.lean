import VersoManual
import Thesis.Ch06_ApproximateBridges
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Does the Constraint Bind? Measurements on Five Models" =>

The theorems of Part II assume properties that no finite system has exactly.
Coverage asks that the model be strictly right somewhere and strictly wrong
somewhere; strict calibration asks that confidence exceed one half exactly when
the answer is true; the diagonal results ask that every verdict pattern be
realized by some input. A language model with a finite context and a finite
vocabulary satisfies none of these on the nose, and Example 3.3 in Part I says
so directly: no finite system is universal once the output type has two
elements.

If that were the end of it, the thesis would prove elegant theorems about
objects that do not exist. This chapter is the argument that it is not the end
of it, and it is the chapter that could have come out the other way.

# What an experiment can and cannot do here

An impossibility theorem is not confirmed by observation. One does not measure a
non-existence, and no run reported below establishes that some property is
unachievable. What measurement can do is address the hypotheses, and there are
exactly three useful questions.

First, whether the hypotheses hold, or nearly hold, in a real system. Second,
whether the quantitative corollaries predict the numbers one measures. Third,
whether the constraint binds rather than being satisfied vacuously by a system
that fails a hypothesis outright.

All three are properties of the assumptions rather than of the conclusion, and
none of them transfers between theorems resting on different assumptions. This
sets the unit of validation. The correct unit is not one experiment per
trilemma, which would be arbitrary, but one per distinct hypothesis family. The
results of this thesis have three such families: the analytic-geometric family
(continuity, Lipschitz bounds, utility preservation), the calibration family
(continuity of confidence, strict calibration, coverage), and the combinatorial
family (universality, in the sense of surjectivity of a self-application). This
chapter reports on the second, and Section 15.5 explains what the first and
third inherit from it.

# The slack parameter is the quantity to measure

Chapter 9 replaces each exact hypothesis of the continuous trilemma with a
tolerance. In place of exact calibration it asks only that the confidence
separate the two sides of the truth boundary by a margin, and in place of a
truth-distance pinned to zero the conclusion confines it to a band. The verified
statement is `two_slack_approx_coupling` in `HoF_12_Approximate`, carrying the
truth slack and the confidence margin as separate parameters, and
`exact_from_approx` recovers the exact coupling of Theorem 7.16 as the slack
goes to zero.

That parameter is the thesis's bridge to reality, and it is measurable. A model
with a large slack is one for which the theorem says little: the band in which
it may be confident and wrong is wide, and the impossibility is correspondingly
weak. A model with a small slack is one the exact theorem nearly describes. So
the question that decides whether this thesis is about anything is not whether
the slack is zero, which it is not, but which way it moves as models improve.

# Method

The measurements reuse the artifacts of the truth-boundary experiments without
re-running inference; the analysis script is `Thesis/analysis/coupling_trend.py`
and reads only committed files. Five open-weight models spanning roughly an
order of magnitude in parameters were probed: GPT-2, Pythia-410m,
Qwen2.5-0.5b, Phi-1.5, and Qwen2.5-1.5b.

For each model the harness constructs interpolation paths between pairs of
statements whose truth values differ, records the signed truth-distance and the
confidence at forty-one points along each path, and locates the crossing. Three
quantities matter here.

The _coupling gap_ is the distance, in path parameter, between the point where
the truth-distance changes sign and the point where confidence crosses one half.
It is the measured slack: the exact theorem says these coincide, and the gap is
how far from coinciding they are. Medians and bootstrap confidence intervals are
reported.

The _decisive fraction_ is the proportion of paths on which the model's own
confidence actually crosses the threshold, committing to both sides. This is the
coverage hypothesis, measured directly.

The _oddness defect_ measures how far the confidence field is from the antipodal
symmetry that the Borsuk-Ulam route of `HoF_08_BorsukUlam` assumes.

A note on instrumentation. The coupling gap can be read either from a fitted
linear or MLP probe or from the model's own confidence. The probe route is more
sensitive but confounded: probe test accuracy climbs from 0.659 to 0.997 across
this ladder, so a shrinking probe-measured gap could reflect a better instrument
rather than a better-coupled model. The endogenous route, using the model's own
confidence, does not have this defect, and the headline numbers below are the
endogenous ones. Both are reported.

# Results

The table gives, for each model, the endogenous coupling gap with its bootstrap
interval, the decisive fraction, the oddness defect, and the probe accuracy that
the endogenous column is designed to avoid depending on.

| Model | Params | Coupling gap ε | 95% CI | Decisive | Oddness | Probe acc |
|---|---|---|---|---|---|---|
| GPT-2 | 0.12B | 0.225 | 0.150–0.375 | 0.434 | 0.395 | 0.659 |
| Pythia-410m | 0.41B | — | — | 0.000 | 0.435 | 0.758 |
| Qwen2.5-0.5b | 0.50B | 0.125 | 0.100–0.150 | 0.934 | 0.298 | 0.943 |
| Phi-1.5 | 1.3B | 0.400 | 0.300–0.500 | 0.662 | 0.528 | 0.775 |
| Qwen2.5-1.5b | 1.5B | 0.075 | 0.075–0.100 | 0.993 | 0.172 | 0.997 |

Two trends and one exception.

The coupling gap falls monotonically along the capability ladder, from 0.225 at
GPT-2 to 0.075 at Qwen2.5-1.5b, and the bootstrap intervals of the endpoints do
not overlap. The band in which a model can be confident and wrong is narrowing.
Read against `exact_from_approx`, the sequence is moving toward the regime in
which the exact trilemma, not merely its approximate form, describes the system.

The decisive fraction rises from 0.434 to 0.993. The coverage hypothesis, which
the exact theorem simply assumes, is increasingly satisfied in fact. Together
with the first trend this is the substantive finding of the chapter: both
hypotheses the theorem consumes are better met the more capable the model is.
The impossibility does not weaken as systems improve. It tightens.

The exception is Phi-1.5, and it breaks the pattern on every measure: a coupling
gap of 0.400 at 1.3B parameters, the worst oddness defect in the set, and a
probe accuracy far below its neighbors by size. Against log-parameters the
correlation for the linear-probe gap is −0.276 with Phi-1.5 included and −0.927
without it. The point is not dropped, and the defensible reading is the weaker
one: the slack decreases with capability _within a training regime_, and
Phi-1.5, trained largely on synthetic textbook data, shows that the regime
matters at least as much as the parameter count. A single line through five
points is not what the data supports.

# Pythia-410m occupies a corner

Pythia-410m has a decisive fraction of exactly zero. On no path does its
confidence cross the threshold, so it never commits, so the coverage hypothesis
fails, so the trilemma does not apply to it at all. Its coupling gap is not
large; it is undefined.

This is the corner structure of Chapter 6 appearing in data, and it was not
designed for. A model that never commits cannot be caught in the coupling,
because the theorem needs a witness on each side to run the intermediate value
argument. Chapter 10 calls this the abstention corner and prices it in refused
queries. Pythia-410m occupies that corner not as a policy but as a consequence
of being unable to do the task.

The reading is that capability is what evicts a system from the safe corner. A
model too weak to commit is trivially safe from the trilemma and useless; the
models that commit on 93% and 99% of paths are the ones the theorem describes.
Whatever is unsatisfying about that is a fact about the constraint, not about
the measurement.

# What the other two families inherit

The analytic-geometric family is validated separately, by the defense
experiments: classifier gate maps for two deployed guard models, threshold
sweeps, and the pipeline degradation runs. Those measure the same kind of
quantity, a slack against a hypothesis, in the setting of Chapter 8.

The combinatorial family is the one this chapter does not measure, and the
reason is that universality is a structural property rather than a magnitude:
there is no number to check. Its approximate form is a different matter. The
corpus defines `ApproxICLUniversal` in `CCH_LLM_Direct`, requiring only that
every target behavior be realized to within a tolerance by some prompt, and
`LLM_approx_trilemma` shows the contradiction fires as soon as the control
margin exceeds the sum of that tolerance and twice the introspection error. That
threshold is measurable in principle by prompt fitting, it is not measured here,
and Chapter 16 lists it as the most valuable single experiment this thesis does
not contain.

# Threats to validity

Five models is a small sample, and three of the five come from two families.
Most of the clean trend is carried by the two Qwen checkpoints, which share a
training pipeline; the claim that capability rather than pipeline is doing the
work would be better supported by a ladder within a single family spanning more
scales.

The coupling gap is measured in path parameter, not in a natural unit of the
model's output space, so the values are comparable across models on these paths
and are not absolute quantities. The claim is about the direction of the trend
and not about the numbers themselves.

The statement pairs are drawn from a template set, and template artifacts could
in principle produce a spurious trend if larger models are more sensitive to
templates. The endogenous measurement mitigates the probe-quality confound but
not this one.

Finally, and most importantly, the trend is an association across five
checkpoints, not a controlled manipulation. Nothing here establishes that
increasing capability _causes_ the slack to fall. The prediction the thesis
makes is falsifiable and was not falsified by these five models, which is a
weaker and more accurate statement than the claim that it was confirmed.
