import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Related Work and Positioning" =>

This chapter says what has been done before and why it does not already contain
the present contribution. It is organized by the kind of claim each body of work
makes, because the relevant question differs by kind: for the unification
literature the question is whether the AI-safety results are already covered,
for the impossibility literature it is whether the results are already unified,
and for the formalization literature it is whether anything of this shape has
been machine-checked.

# Unifications of the diagonal

The claim that the classical self-referential impossibilities share one
structure is not new and is not claimed as new here.

Lawvere's 1969 paper is the origin. It proves that in a cartesian closed
category, a point-surjective map forces every endomorphism of the codomain to
have a fixed point, and observes that Cantor, Russell, Gödel, Tarski, and Turing
fall out by choosing the category and the endomorphism. Yanofsky's 2003 account
works the instances out concretely and without categorical machinery, and it is
the presentation Chapter 4 follows.

What these do not do is instantiate the schema at machine learning. Lawvere's
targets are set theory, logic, and computability; the systems he quantifies over
are mathematical objects whose self-application is exact. The gap this thesis
closes is not the observation that a schema exists but the demonstration that
particular safety properties of statistical models are instances of it, and the
demonstration is nontrivial precisely because the instantiation fails on a
literal reading: a finite model is not point-surjective. Chapter 9 is the work
that repairs this, and it has no counterpart in the unification literature.

# Impossibility results in machine learning

There is a substantial literature of individual impossibility results. The
fairness-tradeoff theorems, the no-free-lunch results, the limits on calibration
under distribution shift, and the security analyses of prompt injection each
establish that some desirable conjunction is unachievable.

These are the results this thesis claims to unify, and the relationship is
asymmetric in an important way. Each is stated and proved within its own
formalism, and each is correct within it. The contribution here is not a better
proof of any one of them; several of the original arguments are shorter than
mine. The contribution is that the same two lemmas generate them, which is a
claim about the collection rather than about any member, and which therefore
cannot be established by improving any single result.

The honest form of the claim matters. I do not derive every published
impossibility result from the schemas. I derive the ones stated in Part III,
name the load-bearing step in each, and in two of the four case studies find
that the load-bearing step is _not_ the diagonal. Chapters 13 and 14 reach their
main results by counting and by invariance respectively. That is evidence
against the strongest version of the unification thesis, and Chapter 16 treats
it as such.

# Calibration and hallucination

The calibration literature asks when a model's stated confidence matches its
empirical accuracy, and the reliability diagram is its central instrument. The
hallucination literature asks when a model asserts what is not so.

The relation to Chapter 7 is a matter of what is being quantified over. The
statistical notion of calibration is a property of a distribution: averaged over
a population of queries at a stated confidence level, the accuracy matches. The
notion this thesis uses is pointwise and exact, as Remark 3.11 sets out, and it
is strictly stronger. The trilemma is therefore not a statement that models
cannot be statistically calibrated, and reading it as one would be an error. It
is a statement about a stronger property, and its practical force comes from the
approximate versions of Chapter 9, where the pointwise requirement is relaxed to
a band.

This is the clearest place where the thesis could be overclaimed, and I have
tried to state the hypothesis precisely enough that the overclaim is visible
when it occurs.

# Interpretability and probing

The interpretability program seeks to read a model's internal state and recover
what the model represents. J-space probing reads the derivative of the
computation rather than its activations; eliciting latent knowledge asks for a
reporter that tells the truth about a latent state even where humans cannot
check.

Chapter 11's result is negative and is best understood as bounding a goal rather
than criticizing a method: a probe that reads every verdict pattern of the model
it probes is a reflective verdict, and no such thing exists. This does not say
probes are useless, and Chapter 11 is careful to say what it does not say. It
says that the complete version of the goal is unavailable, which relocates the
research question from whether a full readout exists to how much of one is
attainable.

For eliciting latent knowledge the relationship is different again, and it is
the case that most constrains the thesis. The obstruction there is a counting
fact about functions agreeing on a subset. It requires no self-reference, and
the diagonal contributes nothing to it. Chapter 13 reports this.

# Formal verification of machine learning

Formal verification in machine learning has concentrated on properties of
specific networks: robustness certificates within a ball, output-range bounds,
and monotonicity, discharged by SMT solvers or abstract interpretation. These
verify a particular trained model against a particular specification.

The corpus here does something different in kind. It verifies theorems about
_every_ system satisfying stated hypotheses, which is why it is written in a
proof assistant with a dependent type theory rather than in a solver. There is
no trained network anywhere in the four libraries. The tradeoff is the usual
one: the statements are far more general and say nothing whatever about any
particular deployed model, which is why Chapter 15 exists.

I am not aware of prior work that machine-checks impossibility results for AI
safety properties. If the claim of novelty in this thesis is anywhere at its
strongest, it is here, and it is also the easiest to check: the corpus builds,
or it does not.

# Summary of the gap

The unification literature has the schemas but not the instances. The
impossibility literature has the instances but not the unification. The
calibration literature studies a weaker hypothesis than the one the trilemma
consumes. The verification literature checks models rather than theorems about
models. This thesis occupies the intersection, and Chapter 15 tests whether the
intersection is inhabited by anything real.
