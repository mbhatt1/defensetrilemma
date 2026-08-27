import VersoManual
import TrilemmaBook.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Reporter Is Underdetermined" =>

The two preceding chapters read a probe into a model and found the diagonal
waiting. Both took the same shape: a readout is a verdict, verdicts about a
self-describing domain are impossible, and the intermediate representation makes
no difference. A reader who has followed that twice is entitled to expect a
third variation, and this chapter is not one. The problem it takes up has a
different mathematical character, and its central obstruction is not the
diagonal at all.

The problem is Eliciting Latent Knowledge, posed by the Alignment Research
Center in 2021 and still open in the regime that matters. The setup is a
parable. An AI guards a vault containing a diamond, and it has learned a
predictive model of the vault richer than any human overseer's. We want to ask
it a question, is the diamond still there, and get an answer that reflects what
its world-model actually represents. We train it by showing it situations, asking
the question, and rewarding answers a human judges correct. The difficulty is
that this training procedure is satisfied by two very different programs. One is
the *direct translator*, which reads the AI's internal representation
and renders it into human vocabulary. The other is the *human
simulator*, which computes what a human looking at the available observations
would conclude, and says that. On every case a human can check, these two agree
by construction, because the human's judgment is the training signal. They come
apart exactly where the AI knows something the human cannot verify, which is the
case we built the system for.

What this chapter shows is that the gap between those two reporters is not a
defect of any particular training scheme. It is a counting fact about functions
that agree on a subset, provable in four lines with no self-reference anywhere.
Then it shows what the diagonal contributes on top: the identifying query, the
one whose answer would distinguish the honest reporter from the impostor, is
precisely the query the system cannot answer. The two engines meet here in a way
they do not meet elsewhere in the book. One says you need a distinguishing test.
The other says the distinguishing test is the liar.

# The construction

*Definition 10.1 (Latent state).* Write `L` for the space of the model's
internal states, the representation its predictor computes. Nothing is assumed
about `L`: it may be activations, a learned world-model, or any structure at
all. Write `lat : Q → L` for the map sending a situation to the latent state the
model computes for it, where `Q` is the space of situations-with-question.

*Definition 10.2 (Reporter).* A *reporter* is a map
`rep : L → Q → Bool`, which reads the latent state and returns an answer to the
question posed. The ELK problem is the problem of training a reporter that
answers according to what the latent state represents.

*Definition 10.3 (Checkable set).* A question is *checkable* when a
human overseer can determine the true answer without relying on the model. Write
`chk : Q → Bool` for the indicator of the checkable questions. The training
signal is defined only where `chk` is `true`, because that is where a label
exists.

The whole difficulty is that `chk` is not constantly `true`. If it were, we
would not need the model. The vault parable is engineered to make this vivid:
the camera feed is checkable, and whether the diamond is behind a screen showing
a replayed feed is not.

*Definition 10.4 (Agreement on the checkable set).* Two reporters
*agree on the checkable set* when they return the same answer for every
latent state and every checkable question.

```lean
def c10_AgreesOn {L Q : Type _} (chk : Q → Bool) (r₁ r₂ : L → Q → Bool) : Prop :=
  ∀ l q, chk q = true → r₁ l q = r₂ l q
```

Agreement on the checkable set is exactly the property that training can see.
Two reporters that agree there are indistinguishable to any procedure whose only
access to the truth is the human label, no matter how that procedure is
constructed, how much data it consumes, or how it regularizes. That is a strong
claim, and it is worth being clear that it is a definition rather than a
theorem: we are defining the training signal to be a function of behavior on
checkable questions, which is what the ELK setup stipulates.

# Underdetermination, without any diagonal

Here is the core of the problem, and it needs no self-reference, no continuity,
and no assumption about `L` whatsoever.

Given any reporter, build a second one by copying it on the checkable questions
and flipping it everywhere else.

```lean
def c10_flipOff {L Q : Type _}
    (chk : Q → Bool) (rep : L → Q → Bool) : L → Q → Bool :=
  fun l q => cond (chk q) (rep l q) (!(rep l q))
```

*Lemma 10.5 (The variant is invisible to training).* *`c10_flipOff` agrees
with the reporter it was built from on the whole checkable set.*

```lean
theorem c10_flip_agrees {L Q : Type _}
    (chk : Q → Bool) (rep : L → Q → Bool) :
    c10_AgreesOn chk (c10_flipOff chk rep) rep := by
  intro l q hq
  simp [c10_flipOff, hq]
```

*Proof.* On a checkable `q` the condition is `true`, and `cond true a b`
reduces to `a`. ∎

*Lemma 10.6 (The variant differs off it).* *At any unchecked question the
two disagree.*

```lean
theorem c10_flip_differs {L Q : Type _}
    (chk : Q → Bool) (rep : L → Q → Bool)
    (l : L) (q₀ : Q) (hq₀ : chk q₀ = false) :
    c10_flipOff chk rep l q₀ ≠ rep l q₀ := by
  have h : c10_flipOff chk rep l q₀ = !(rep l q₀) := by
    simp [c10_flipOff, hq₀]
  rw [h]
  exact bool_not_fpf (rep l q₀)
```

*Proof.* The condition is `false`, so the variant evaluates to the negation of
the original, and {lean}`bool_not_fpf` says a Boolean is never its own negation.
∎

Note where {lean}`bool_not_fpf` is doing its work. It is the same fixed-point-free
map that drives every diagonal in this book, but it is being used here for its
plain content, that `!b ≠ b`, with no diagonal construction around it. The two
uses are worth keeping distinct.

*Theorem 10.7 (Underdetermination).* *If any question is unchecked, then
for every reporter there is a second, distinct reporter that training cannot
distinguish from it.*

```lean
theorem c10_underdetermined {L Q : Type _}
    (chk : Q → Bool) (rep : L → Q → Bool)
    (l : L) (q₀ : Q) (hq₀ : chk q₀ = false) :
    c10_AgreesOn chk (c10_flipOff chk rep) rep
      ∧ c10_flipOff chk rep l q₀ ≠ rep l q₀ :=
  ⟨c10_flip_agrees chk rep, c10_flip_differs chk rep l q₀ hq₀⟩
```

*Proof.* Lemmas 10.5 and 10.6. ∎

That is the ELK problem, stated exactly and proved. The direct translator and
the human simulator are two points in a set the training signal cannot separate,
and Theorem 10.7 says that set has more than one point as soon as a single
question falls outside the checkable region. The construction is crude, a
wholesale flip, and a real human simulator is subtler than that, but crudeness
is the right property for an impossibility: if even the blunt variant is
invisible, no argument about which reporter is *simpler* or *more
natural* can be a proof, because simplicity was never what the training
signal measured.

*Remark 10.8 (Why inductive bias is not a refutation).* The standard hope is
that the direct translator is favored by some prior, being smaller, faster, or
more natural, and that gradient descent finds it. Theorem 10.7 does not rule
that out, and nothing in this book does. What it establishes is the burden of
proof. Any such argument must supply the missing ingredient from outside the
training signal, and must defend it as a claim about the actual optimizer and
the actual architecture, because the data cannot supply it. The reason ELK has
resisted a decade of proposals is that this burden keeps coming due.

# The identifiability criterion

The converse of Theorem 10.7 is worth stating, because it says exactly what it
would take to solve the problem, and the statement is one line.

*Theorem 10.9 (Full checkability pins the reporter).* *If every question is
checkable, then reporters agreeing on the checkable set are equal.*

```lean
theorem c10_full_checkability_pins {L Q : Type _}
    (chk : Q → Bool) (r₁ r₂ : L → Q → Bool)
    (hchk : ∀ q, chk q = true) (h : c10_AgreesOn chk r₁ r₂)
    (l : L) (q : Q) : r₁ l q = r₂ l q :=
  h l q (hchk q)
```

*Proof.* Apply the agreement hypothesis at the witness supplied by full
checkability. ∎

Theorems 10.7 and 10.9 together are a clean dichotomy. Identifiability of the
reporter is *equivalent* to full checkability: if everything is
checkable the reporter is pinned, and if anything is not, it is not. There is no
middle regime in which partial checking buys partial identification of the
answers you care about, because the answers you care about are by construction
the unchecked ones.

This is worth pausing on, because it reframes what a solution to ELK would look
like. Every proposal must either enlarge `chk` until it covers the cases that
matter, or import a constraint that is not a function of behavior on `chk`. The
first is scalable oversight, and it is the honest reading of debate,
amplification, and recursive reward modeling: all of them are attempts to make
more questions checkable by building better checkers. The second is the
inductive-bias family of Remark 10.8. The dichotomy says these are the only two
doors, which is a genuinely useful thing for a research programme to know.

# Where the diagonal comes in

So the reporter is identified only if everything is checkable. The natural next
move is to try to make everything checkable, and this is where the first engine
of the book finally enters, because it says that door is shut too.

A checking procedure that could settle every question about the model, including
questions about the model's own reports, is a total exact verdict over a domain
that describes itself. That is the object Chapter 1 rules out. Read `chk` not as
a fixed human capability but as the reach of the best checker you can build, and
the ambition of full checkability becomes the ambition of a universal verifier.

*Theorem 10.10 (A reporter reading the latent state is still a verdict).*
*If every pattern of answers over questions is realized by some question's
latent state, the situation is contradictory.*

```lean
theorem c10_reporter_factoring {L Q : Type _}
    (lat : Q → L) (rep : L → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, rep (lat p) = g) : False :=
  no_reflective_verdict (fun p => rep (lat p)) hs
```

*Proof.* The composite is a reflective verdict, and
{lean}`no_reflective_verdict` rules those out. ∎

*Theorem 10.11 (The unanswerable question).* *Under the same hypothesis
there is a question the reporter answers as its own negation.*

```lean
theorem c10_reporter_liar {L Q : Type _}
    (lat : Q → L) (rep : L → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, rep (lat p) = g) :
    ∃ p, rep (lat p) p = !(rep (lat p) p) :=
  liar_query (fun p => rep (lat p)) hs
```

*Proof.* {lean}`liar_query` at the composite. ∎

Now put the two engines together, which is the point of the chapter.

To distinguish the direct translator from the human simulator you need a
question they answer differently, and by Theorem 10.7 every such question lies
outside the checkable set. To bring it inside, you must extend `chk` to cover
questions about what the model represents, including what it represents about
its own reports. But by Theorem 10.11, a verdict procedure of that reach owns a
question it cannot answer consistently, and that question is not an obscure
corner: it is the diagonal one, built precisely to disagree with whatever the
reporter says.

So the distinguishing query and the liar query are pulling in opposite
directions on the same set. Underdetermination pushes the decisive question
*out* of the checkable region, and the diagonal blocks the region from
being extended to reach it. The direct translator and the human simulator differ
exactly where nobody can look, and the reason nobody can look is not a shortage
of resources.

*Remark 10.12 (What is genuinely new here relative to Chapter 8).* In Chapters 8
and 9 the diagonal was the whole argument and the representation was a
bystander. Here the diagonal is the second of two obstructions and does the
smaller share of the work. Theorem 10.7, the load-bearing result, is pure
counting: it holds for finite `Q`, for a model with three neurons, for a
reporter implemented as a lookup table. That matters, because the standard
objection to the impossibility results of this book, that point-surjectivity is
an idealization no real system meets, has no purchase on it. A skeptic who
rejects every diagonal in this book still owes an answer to Theorem 10.7.

# The analytic engine

The analytic half is short here, but it sharpens the picture.

Suppose the reporter returns a confidence rather than a bit, and suppose the
latent space is connected in the sense of Chapter 4, which for a learned
representation over a continuous input space is the usual situation. Take a
direct translator and a human simulator that agree on the checkable set and
differ at some unchecked question. Along a path in latent space from a state
where both say yes to one where they differ, the gap between their two scores is
a continuous function starting at zero and ending nonzero. By the intermediate
value theorem it passes through every value in between.

The consequence is that there is no threshold of agreement that separates the
two reporters cleanly. For any tolerance you choose, there are latent states
where the two agree to within it and states just beyond where they do not, and
the boundary between those regions is a surface in latent space, not a gap. A
proposal that says *accept the reporter if it agrees with the human
simulator to within `ε` on held-out data* is therefore not selecting a
reporter; it is selecting a neighborhood, and the neighborhood contains both
answers to the question you care about. Chapter 5's quantitative machinery gives
the width of that neighborhood in terms of the Lipschitz constants, and Chapter
6's approximate bridges say how it shrinks as checkability grows. It shrinks. It
does not close, and it closes only in the full-checkability limit that Theorem
10.11 forbids.

# What this does not claim

It does not claim ELK is unsolvable. Theorem 10.9 gives a sufficient condition,
and the dichotomy of the previous section names the two families of approach
that remain open. What is ruled out is a solution that works by training on
checkable questions alone, which is a real constraint but a narrower one than
*no solution exists*.

It does not claim the human simulator is what models actually learn. That is an
empirical question, and the evidence is mixed and active. Theorem 10.7 says the
training signal does not settle it, not that the answer is bad.

It does not claim the crude flip of `c10_flipOff` is a realistic competitor. It
is a witness, chosen for being obviously invisible to training rather than for
being plausible. Its role is to establish that the set of surviving reporters
has more than one element, which is all an underdetermination result needs.

It does not claim `chk` is a Boolean function of the question alone. Real
checkability is graded, costly, and depends on the checker. Reading `chk` as an
exact indicator is the same idealization Chapter 6 relaxes elsewhere, and the
graded version of Theorem 10.7 is the natural next result rather than a
correction to this one.

# Exercises

*Exercise 10.1.* Prove that `c10_flipOff` applied twice returns the original
reporter, so the construction is an involution on the space of reporters.

*Exercise 10.2.* Strengthen Theorem 10.7: given two unchecked questions,
construct four pairwise-distinct reporters all agreeing on the checkable set.
Generalize to `n` unchecked questions and state the counting law.

*Exercise 10.3.* Suppose the training signal also penalizes description length.
Formalize a length function on reporters and give the extra hypothesis under
which the direct translator is pinned. Then say why that hypothesis is not
supplied by the data.

*Exercise 10.4.* Prove the converse of Theorem 10.9: if reporters agreeing on
`chk` are always equal, then `chk` is constantly `true`, provided `L` and `Q`
are nonempty. This makes the dichotomy an equivalence.

*Exercise 10.5.* Combine {lean}`c10_reporter_factoring` with Chapter 9's trace
factoring to state one theorem covering a reporter that reads both the latent
state and the model's chain of thought.

*Exercise 10.6.* (Analytic, prose.) State the hypotheses under which the set of
reporters agreeing to within `ε` on a held-out set is connected, and explain why
connectedness of that set is bad news for a selection procedure.

*Exercise 10.7.* (Design.) You are running a scalable-oversight programme whose
goal is to enlarge `chk`. Using the dichotomy, write down the measurement that
tells you whether a given technique has enlarged the checkable set or has merely
enlarged the set of questions on which the two reporters happen to agree.
