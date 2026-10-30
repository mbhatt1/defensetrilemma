import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Introduction" =>

A trustworthy language model should not assert falsehoods with confidence. It
should not follow instructions that arrive inside the data it was asked to
process. It should report on its own reasoning in a way that a monitor can
check. Each of these is a reasonable engineering goal, each has a substantial
literature proposing mechanisms to achieve it, and each has a published
impossibility result showing that some natural formulation of it cannot be
achieved at all.

The literature treats these as separate findings. Hallucination bounds come from
learning theory and calibration; prompt-injection limits come from security
analysis; the obstructions to eliciting latent knowledge come from a counting
argument about functions; watermark removal comes from the geometry of
paraphrase. They are published in different venues, proved by different methods,
and cited by different communities.

This thesis argues that they are not separate.

# Thesis statement

_The impossibility results that constrain trustworthy machine learning are
instances of two mathematical schemas: a diagonal schema, which produces a
self-referential witness whenever a system can name its own behaviors, and a
value-crossing schema, which produces a boundary witness whenever a continuous
quantity changes sign on a connected domain. Both schemas can be stated and
proved in a proof assistant, both can be instantiated to recover the published
results as corollaries, and the quantitative form of the second schema makes
predictions that measurably tighten as model capability increases._

Three claims, and they are separable. The first is a claim about mathematical
structure, and I defend it by exhibiting the schemas and deriving the
instances. The second is a claim about verification, and I defend it with a
machine-checked corpus that the reader can rebuild. The third is a claim about
the physical world, and I defend it with measurements on five language models.

The third claim is the one that can fail, and stating it in a falsifiable form
is deliberate. The exact impossibility theorems assume properties no finite
system has: perfect calibration, exact coverage, genuine self-naming. If real
systems sat permanently far from those assumptions, the theorems would be
elegant and irrelevant. Chapter 6 replaces each exact hypothesis with a slack
parameter, and Chapter 13 measures that parameter. If the measured slack were
constant across capability, or grew, the applicability claim would be false and
I would report it as false.

# What is not claimed

Three disclaimers, stated here because each corresponds to a way the argument
could be overread.

I do not claim the schemas are original. Lawvere's fixed-point theorem is from
1969, the intermediate value theorem is older than the calculus that proves it,
and the observation that Cantor, Gödel, Turing, and Tarski share a diagonal is
standard. What is new is the specific claim that the AI-safety results are
further instances, the formal derivations that establish it, and the
quantitative bridge in Part III.

I do not claim the results forbid useful systems. Every theorem here is a
constraint on a conjunction of properties, and every one of them is escaped by
weakening one conjunct. Chapter 8 works out what each escape costs. A theorem
that says you cannot have all three of a triple is a design constraint, not a
prohibition, and the practical content is in which corner a deployment should
choose and why.

I do not claim the impossibilities are the whole story of AI safety. They bound
what guarantees are available in principle. They say nothing about how often a
system encounters the boundary, how hard the boundary is to find, or what a
failure costs. Chapters 6 and 13 supply what quantitative content I can, and
Chapter 15 is explicit about the rest.

# Contributions

The contributions of this thesis are as follows.

 * _A unified formalization._ Two schemas, stated in Lean 4 and proved from
   first principles, from which the classical diagonal results and the
   AI-safety impossibilities follow as instances. The claim that a specific
   published result is an instance is discharged by a proof, not by an
   analogy: {lean}`no_reflective_verdict` and its relatives are derived from
   the same lemma that yields Cantor's theorem.

 * _A machine-checked corpus._ Four Lean libraries totaling 738 declarations
   across 94 modules, with no `sorry` and no axioms beyond the three that
   Mathlib itself uses. Every numbered result in this thesis is either proved
   in the text, where the proof is elaborated as the document is built, or
   cited to a declaration in that corpus, and a build gate rejects the document
   if a citation fails to resolve or a claim is left unbacked.

 * _The analytic engine and its trilemma._ A proof that a continuous model on a
   connected question space cannot be simultaneously faithful, covering, and
   strictly calibrated, together with its approximate form, in which each exact
   hypothesis is replaced by a slack parameter and the exact statement is
   recovered in the limit.

 * _Four case studies with distinct load-bearing steps._ J-space probing,
   chain-of-thought monitoring, eliciting latent knowledge, and watermark
   detection. Two of the four reach their main results without self-reference,
   which bounds the diagonal schema's reach and is reported as a limitation of
   the unification claim rather than concealed.

 * _An empirical bridge._ Measurements of the coupling slack on five language
   models, showing that it falls from 0.225 to 0.075 across a capability
   ladder, and that the coverage hypothesis the theorems require is satisfied
   on 43% of paths for the weakest model and 99% for the strongest. The
   impossibility binds harder as systems improve.

# Structure of the thesis

Part I is background. Chapter 2 introduces the Lean vocabulary and the topology
the later arguments use, Chapter 3 develops the diagonal schema, and Chapter 4
recovers the classical impossibility theorems from it. A reader who knows
Lawvere's theorem and its classical instances can begin at Chapter 5.

Part II is the theoretical contribution. Chapter 6 states the trilemmata in
their combinatorial form, Chapter 7 develops the analytic engine and proves the
continuous trilemma, Chapter 8 turns to the geometry of attack surfaces, and
Chapter 9 builds the approximate bridges that connect the exact theorems to
systems that satisfy their hypotheses only within a tolerance.

Part III is application and evidence. Chapter 10 draws the consequences for
deployment. Chapters 11 through 14 are the four case studies. Chapter 15 is the
empirical chapter, and it is where the applicability claim is tested.

Part IV closes. Chapter 16 states the limitations, including the assumptions
most likely to be wrong and the results that would be affected if they were.
Chapter 17 concludes.

# Declaration of collaborative work

Parts of the material in this thesis have appeared in co-authored work, and the
division of labor is stated here.

The defense impossibility results of Part II and the geometric analysis of
Chapter 8 appeared in _Geometric Limits of Defense Design_, co-authored with
S. Munshi, V. S. Narajala, I. Habler, A. Al-Kahfah, K. Huang, and B. Gatto. The
Lean formalization in `ManifoldProofs`, the statements and proofs of the
three-tier impossibility, and the meta-theorem are mine. The empirical
validation harness was built jointly.

The truth-boundary results of Chapter 7 and the experiments of Chapter 15
appeared in the truth-boundary manuscript. The formalization in
`HallucinationProofs` and the analysis reported in Chapter 15 are mine.

The expository treatment in Part I is adapted from a book co-authored with
K. Huang. The Lean development it presents is mine; the pedagogical framing was
developed jointly.

All Lean code in the four companion libraries is my own work. Where a proof
follows a known argument, the text says so and names the source.
