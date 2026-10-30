import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Conclusion" =>

The thesis set out to show that the impossibility results constraining
trustworthy machine learning are instances of two schemas, that the claim can be
machine-checked, and that the constraint is not an artifact of idealization.

On the first, the result is a qualified yes. The diagonal schema generates the
classical impossibilities and the verdict trilemmata, the value-crossing schema
generates the continuous and geometric results, and Part II derives them from
the two lemmas rather than by analogy. Two of the four case studies fall outside
both schemas, and Chapter 16 states the restriction that leaves.

On the second, the answer is unqualified, and it is the part of this work with
the longest useful life. The corpus is 738 declarations with no `sorry` and no
axioms beyond Mathlib's three, and the document that cites it will not build if
a citation dangles or a numbered claim goes unbacked. A reader who doubts any
theorem here can rebuild it.

On the third, the evidence points the right way without settling the question.
The coupling slack falls from 0.225 to 0.075 across a capability ladder and the
coverage hypothesis rises from 43% to 99% satisfaction, so the theorems describe
capable models better than weak ones. Pythia-410m, which never commits, escapes
the trilemma by failing its hypotheses, which is the abstention corner arrived at
by incapacity rather than by design.

# The claim worth carrying forward

If one sentence survives from this thesis, it should be that these limits
tighten with capability rather than receding.

The intuition the field works from is the opposite. Hallucination, injection
susceptibility, and unfaithful reasoning are treated as defects of immature
systems, to be engineered away as models improve. For the properties studied
here that intuition is backwards. The hypotheses that make the impossibility
theorems apply — committing to answers on both sides of a boundary, coupling
confidence to correctness, realizing a wide range of behaviors on demand — are
the same properties that make a model useful. A system escapes the theorems by
failing to have them.

That is not a counsel of despair, and Chapter 10 is the constructive half: every
trilemma is escaped by giving up one vertex, the three corners have different
costs, and the costs are legible enough to choose between. What the theorems
remove is the option of not choosing.

# Future work

Three directions, in order of what I would do first.

The measurement of Chapter 16, on approximate in-context universality, would
extend the applicability argument from one hypothesis family to two, and the
apparatus for it already exists in the corpus and the harness.

A capability ladder within a single training pipeline, spanning more scales than
five checkpoints across four families, would convert Chapter 15's association
into something closer to a controlled result. Phi-1.5's deviation suggests that
training data composition is a second factor worth isolating rather than
noise to be averaged over.

Finally, the corpus is a starting point rather than a finished artifact. The
schemas are stated generally enough that a new impossibility claim in this area
can be tested against them cheaply: instantiate, and see whether the instance
proof goes through. A claim that resists instantiation is either wrong or genuinely
new, and telling those apart quickly is worth more than any single theorem here.
