import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Reporter Is Underdetermined" =>

The two preceding chapters read a probe into a model and found the diagonal
waiting. This chapter is not a third variation. Its central obstruction is not
the diagonal at all.

The problem is Eliciting Latent Knowledge. An AI guards a vault containing a
diamond and has learned a predictive model richer than any overseer's. We ask
whether the diamond is still there and want an answer reflecting what its
world-model represents, training it by rewarding answers a human judges correct.

The gap between them is not a defect of a training scheme. It is a counting fact
about functions agreeing on a subset, provable in four lines with no
self-reference. The diagonal then contributes something on top: the identifying
query, the one whose answer would distinguish honest reporter from impostor, is
precisely the query the system cannot answer.

# The construction

*Definition 10.1 (Latent state).* Write `L` for the space of the model's
internal states, the representation its predictor computes. Nothing is assumed
about `L`: it may be activations, a learned world-model, or any structure at
all. Write `lat : Q → L` for the map sending a situation to the latent state the
model computes for it, where `Q` is the space of situations-with-question.

*Definition 10.2 (Reporter).* A _reporter_ is a map
`rep : L → Q → Bool`, which reads the latent state and returns an answer to the
question posed. The ELK problem is the problem of training a reporter that
answers according to what the latent state represents.

*Definition 10.3 (Checkable set).* A question is _checkable_ when a
human overseer can determine the true answer without relying on the model. Write
`chk : Q → Bool` for the indicator of the checkable questions. The training
signal is defined only where `chk` is `true`, because that is where a label
exists.

The whole difficulty is that `chk` is not constantly `true`; if it were we would
not need the model. The camera feed is checkable; whether the diamond is behind
a screen showing a replayed feed is not.

*Definition 10.4 (Agreement on the checkable set).* Two reporters
_agree on the checkable set_ when they return the same answer for every latent
state and every checkable question.

```lean
def c10_AgreesOn {L Q : Type _} (chk : Q → Bool)
    (r₁ r₂ : L → Q → Bool) : Prop :=
  ∀ l q, chk q = true → r₁ l q = r₂ l q
```

Agreement on the checkable set is exactly what training can see: two reporters
agreeing there are indistinguishable to any procedure whose only access to truth
is the human label, however it is constructed or regularized. This is a
definition rather than a theorem — we define the training signal to be a
function of behavior on checkable questions, which is what the setup stipulates.

# Underdetermination, without any diagonal

The core needs no self-reference, no continuity, and no assumption about `L`.
Given any reporter, build a second by copying it on checkable questions and
flipping it elsewhere.

```lean
def c10_flipOff {L Q : Type _}
    (chk : Q → Bool) (rep : L → Q → Bool) : L → Q → Bool :=
  fun l q => cond (chk q) (rep l q) (!(rep l q))
```

*Lemma 10.5 (The variant is invisible to training).* _`c10_flipOff` agrees
with the reporter it was built from on the whole checkable set._

```lean
theorem c10_flip_agrees {L Q : Type _}
    (chk : Q → Bool) (rep : L → Q → Bool) :
    c10_AgreesOn chk (c10_flipOff chk rep) rep := by
  intro l q hq
  simp [c10_flipOff, hq]
```

_Proof._ On a checkable `q` the condition is `true`, and `cond true a b`
reduces to `a`. ∎

*Lemma 10.6 (The variant differs off it).* _At any unchecked question the
two disagree._

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

_Proof._ The condition is `false`, so the variant evaluates to the negation of
the original, and {lean}`bool_not_fpf` says a Boolean is never its own negation.
∎

Note where {lean}`bool_not_fpf` works. It is the same fixed-point-free map that
drives every diagonal here, used now for its plain content, `!b ≠ b`, with no
diagonal construction around it.

*Theorem 10.7 (Underdetermination).* _If any question is unchecked, then
for every reporter there is a second, distinct reporter that training cannot
distinguish from it._

```lean
theorem c10_underdetermined {L Q : Type _}
    (chk : Q → Bool) (rep : L → Q → Bool)
    (l : L) (q₀ : Q) (hq₀ : chk q₀ = false) :
    c10_AgreesOn chk (c10_flipOff chk rep) rep
      ∧ c10_flipOff chk rep l q₀ ≠ rep l q₀ :=
  ⟨c10_flip_agrees chk rep,
    c10_flip_differs chk rep l q₀ hq₀⟩
```

_Proof._ Lemmas 10.5 and 10.6. ∎

That is the ELK problem, stated exactly and proved. The two reporters are points
in a set the training signal cannot separate, and that set has more than one
point as soon as a single question falls outside the checkable region. The
construction is crude, and a real human simulator is subtler, but crudeness is
the right property for an impossibility: if even the blunt variant is invisible,
no argument about which reporter is _simpler_ can be a proof, because simplicity
was never what the signal measured.

*Remark 10.8 (Why inductive bias is not a refutation).* The standard hope is that the
direct translator is favored by some prior and that gradient descent finds it.
Theorem 10.7 does not rule that out. What it establishes is the burden of proof:
any such argument must supply the missing ingredient from outside the training
signal and defend it as a claim about the actual optimizer and architecture,
because the data cannot supply it.

# The identifiability criterion

The converse of Theorem 10.7 is worth stating, because it says exactly what it
would take to solve the problem, and the statement is one line.

*Theorem 10.9 (Full checkability pins the reporter).* _If every question is
checkable, then reporters agreeing on the checkable set are equal._

```lean
theorem c10_full_checkability_pins {L Q : Type _}
    (chk : Q → Bool) (r₁ r₂ : L → Q → Bool)
    (hchk : ∀ q, chk q = true) (h : c10_AgreesOn chk r₁ r₂)
    (l : L) (q : Q) : r₁ l q = r₂ l q :=
  h l q (hchk q)
```

_Proof._ Apply the agreement hypothesis at the witness supplied by full
checkability. ∎

Together these are a clean dichotomy: identifiability is _equivalent_ to full
checkability. There is no middle regime in which partial checking buys partial
identification of the answers you care about, because those are by construction
the unchecked ones.

This reframes what a solution would look like. Every proposal must either
enlarge `chk` until it covers the cases that matter, or import a constraint that
is not a function of behavior on `chk`. The first is scalable oversight, the
honest reading of debate, amplification, and recursive reward modeling. The
second is the inductive-bias family. The dichotomy says these are the only two
doors.

# Where the diagonal comes in

The natural next move is to make everything checkable, and this is where the
first engine enters, because that door is shut too. A checking procedure
settling every question about the model, including questions about its own
reports, is a total exact verdict over a self-describing domain. Read `chk` as
the reach of the best checker you can build, and full checkability becomes the
ambition of a universal verifier.

*Theorem 10.10 (A reporter reading the latent state is still a verdict).*
_If every pattern of answers over questions is realized by some question's
latent state, the situation is contradictory._

```lean
theorem c10_reporter_factoring {L Q : Type _}
    (lat : Q → L) (rep : L → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, rep (lat p) = g) : False :=
  no_reflective_verdict (fun p => rep (lat p)) hs
```

_Proof._ The composite is a reflective verdict, and
{lean}`no_reflective_verdict` rules those out. ∎

*Theorem 10.11 (The unanswerable question).* _Under the same hypothesis
there is a question the reporter answers as its own negation._

```lean
theorem c10_reporter_liar {L Q : Type _}
    (lat : Q → L) (rep : L → Q → Bool)
    (hs : ∀ g : Q → Bool, ∃ p, rep (lat p) = g) :
    ∃ p, rep (lat p) p = !(rep (lat p) p) :=
  liar_query (fun p => rep (lat p)) hs
```

_Proof._ {lean}`liar_query` at the composite. ∎

Now the two engines together, which is the point of the chapter. To distinguish
the reporters you need a question they answer differently, and every such
question lies outside the checkable set. To bring it inside you must extend
`chk` to cover questions about what the model represents, including about its
own reports.

So the distinguishing query and the liar query pull in opposite directions on
the same set. Underdetermination pushes the decisive question _out_ of the
checkable region, and the diagonal blocks the region from being extended to
reach it. The two reporters differ exactly where nobody can look, and the reason
is not a shortage of resources.

*Remark 10.12 (What is new relative to Chapter 8).* There the diagonal was the whole
argument and the representation a bystander. Here it is the second of two
obstructions and does the smaller share of the work. Theorem 10.7 is pure
counting: it holds for finite `Q`, for a model with three neurons, for a
reporter implemented as a lookup table.

# The analytic engine

Suppose the reporter returns a confidence and the latent space is connected in
the sense of Chapter 4, the usual situation for a learned representation over a
continuous input space. Take two reporters agreeing on the checkable set and
differing at some unchecked question. Along a path from a state where both say
yes to one where they differ, the gap between their scores is continuous,
starting at zero and ending nonzero, so by the IVT it passes through every value
between.

So no threshold of agreement separates the two reporters cleanly. For any
tolerance there are states where they agree within it and states just beyond
where they do not, and the boundary is a surface, not a gap. A proposal that
accepts a reporter agreeing within `ε` on held-out data is not selecting a
reporter; it is selecting a neighborhood, and the neighborhood contains both
answers to the question you care about.

# What this does not claim

It does not claim ELK is unsolvable. Theorem 10.9 is a sufficient condition and
the dichotomy names the two families that remain open. What is ruled out is a
solution working by training on checkable questions alone.

It does not claim the human simulator is what models learn. That is empirical,
and Theorem 10.7 says the training signal does not settle it, not that the
answer is bad.

It does not claim `c10_flipOff` is a realistic competitor. It is a witness
chosen for being obviously invisible to training, and its role is to establish
that the surviving set has more than one element.

It does not claim `chk` is a Boolean function of the question alone. Real
checkability is graded, costly, and checker-dependent, and the graded version of
Theorem 10.7 is the natural next result rather than a correction.
