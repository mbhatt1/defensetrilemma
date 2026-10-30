import VersoManual
import Thesis.Ch06_ApproximateBridges
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Limitations" =>

This chapter states what is wrong with the thesis, or most likely to be. It is
organized from the assumptions whose failure would cost the most to the ones
whose failure would cost the least.

# The unification claim is not fully supported

The thesis statement says the impossibility results are instances of two
schemas. Two of the four case studies are not.

Chapter 13 reaches its main result by a counting argument: two reporters
agreeing on a checkable subset may disagree off it, and nothing self-referential
is required. Chapter 14 reaches its main result by invariance: a detector
constant along paraphrase orbits cannot track a mark that varies along them, and
again no diagonal appears. Both chapters contain diagonal corollaries, and both
say plainly that the corollary is not what does the work.

The accurate version of the thesis statement is therefore weaker than the
headline: the two schemas generate a large family of these results, they
generate every result in Part II, and they do not generate everything in the
neighborhood. I have preferred to report the boundary rather than to define the
family so as to exclude the counterexamples, which would make the claim true and
empty.

# Continuity and connectedness of prompt space

The analytic engine requires a connected domain and continuous maps on it.
Prompt space is a set of finite token sequences, which is discrete, and no
amount of topology-talk changes that.

Three responses appear in the thesis, and none is fully satisfying. Chapter 9's
discrete bridge proves the arithmetic core over the integers with no analysis at
all, which shows the conclusion does not depend on the continuum, but at the
cost of assuming a discrete sign change that is itself a hypothesis about the
model. `MoF_ContinuousRelaxation` uses a Tietze extension to carry discrete data
into the continuous theory, which is legitimate and does assume the extension is
the right idealization. And embeddings are genuinely continuous, so a model
factoring through an embedding inherits continuity on that factor.

An examiner who rejects all three is left with theorems about an idealization.
I think the discrete bridge answers the objection, and I record that it is the
assumption most often challenged and the one I would attack first.

# Pointwise calibration is stronger than the literature's

The trilemma's calibration hypothesis is pointwise and exact, and the calibration
literature's is statistical and averaged. The trilemma is therefore not a result
about reliability diagrams, and the temptation to present it as one should be
resisted. Its force in the statistical setting comes only through the
approximate results of Chapter 9, and how much force survives that translation
is a question this thesis does not settle.

# The empirical claim rests on five checkpoints

Chapter 15's threats to validity are not repeated here, but the headline is
that five models, dominated by two families, with an outlier that breaks the
trend, is thin evidence for a claim about capability in general. The trend is
consistent with the thesis and does not establish it.

# The most valuable missing experiment

The combinatorial family is unmeasured. `ApproxICLUniversal` gives the
tolerance that a real system would have to meet, and `LLM_approx_trilemma` gives
the threshold at which the contradiction fires, but no measurement of that
tolerance appears in this thesis.

The experiment is well-defined: fix a query set and a verdict class, fit system
prompts to targets drawn from that class, and record how closely the fitted
prompt drives the model to the target. Run it on the ladder of Chapter 15 and
compare against the introspection error. If the tolerance descends across the
ladder and crosses the threshold, the diagonal family gains the same
applicability argument the calibration family now has. If it plateaus, finite
context is a real ceiling and the diagonal results apply to no system that can
be built, which would be a more interesting finding than the one I expect.

I did not run it, and its absence is the largest gap in Part III.

# Deployment claims are not theorems

Three propositions in Chapter 10 concern cost rather than mathematics: the
effect of abstention on the surviving vertices, the default corner by archetype,
and the traffic-dependence of felt cost. Each is marked "Not formalized." in its
own text, and the build gate requires that marking rather than permitting a
silent gap. They are engineering arguments and should be read as such.

# What would falsify the thesis

Stating this is the point of the chapter. The unification claim fails if a
central impossibility in this area is shown to require an essentially different
mechanism; Chapters 13 and 14 are partial instances of exactly that, which is
why the claim is stated in the restricted form it is. The applicability claim
fails if the coupling slack is stable or increasing across a properly controlled
capability ladder. The verification claim fails if the corpus does not build,
which is the one component a reader can check in an afternoon.
