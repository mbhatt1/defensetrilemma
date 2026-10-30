import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Diagonal" =>

Every impossibility here descends from one move. Assume a system expressive
enough to describe its own behavior. Build a description that disagrees with
whatever the system does on itself.

The code blocks are core Lean 4 with no libraries, elaborated as this document
builds. The technical core is Theorem 1.4 and Corollary 1.10; everything else
argues that the single hypothesis of Theorem 1.4 is exactly "the system can
describe itself," and that five famous theorems are one theorem read five ways.

# One move, five disguises

The five arguments below were found separately over sixty years. They look
different because their subject matter differs: sets, then logic, then
computation. Each builds a function computing what the system does to a
description and then changing the answer. Each derives its contradiction from
the same place: nothing equals its own change.

_Cantor (1891)._ Suppose `f : A → P(A)` hits every subset. Let `D = { a ∈ A : a ∉ f a }`,
and let `f a₀ = D`. Is `a₀ ∈ D`?

The uncountability argument is the same with the pool taken to be `ℕ`. Given a
list `r₀, r₁, …` of reals, build one whose `n`-th digit differs from the `n`-th
digit of `rₙ`. The system is `n ↦ rₙ`, outcomes are digits, self-application
reads the `n`-th digit of the `n`-th real, and the change is a fixed-point-free
digit swap.

_Russell (1901)._ Unrestricted comprehension gives `R = { x : x ∉ x }`, and `R ∈ R`
holds exactly when `R ∉ R`. This is Cantor's `D` with the indexing removed: the
universe plays both roles, `f` is the identity, and the diagonal `a ↦ a ∉ f a`
becomes `x ↦ x ∉ x`. It is more violent than Cantor, because it needs no extra
assumption; comprehension alone suffices.

The two standard repairs are the two escapes every later chapter uses. Zermelo
restricts comprehension, so there is no ambient universe to carve from: this
denies universality. Russell's theory of types stratifies levels so `x ∈ x` is
ill-formed: this breaks the coincidence of domains in `A → A → Y`, forcing judge
and judged into different types so the diagonal cannot form.

_Gödel (1931)._ The same move inside arithmetic, and the performance is what
made it hard. Gödel numbered formulas and proofs, then showed "the proof coded
by `p` proves the sentence coded by `n`" is itself arithmetic. Once provability
is a predicate `Prov`, arithmetic quotes itself.

The diagonal lemma is this chapter's theorem with `t` negation of provability.
Representability is universality: the theory names, and correctly names,
properties of its own sentences. Weak theories fail here, which is why
incompleteness needs a strength lower bound.

_Tarski (1936)._ Gödel's move aimed at truth. If `True(x)` held exactly of true
sentences, the diagonal lemma on "`x` is not true" gives `L` equivalent to "`L`
is not true," so `L` is true iff it is not. No such `True` is definable in its
own language.

_Turing (1936)._ Suppose `H` decides whether `p` halts on `x`. Build `Dgn` which
on input `p` runs `H` on `(p, p)` and does the opposite. Then `Dgn` halts on
`Dgn` exactly when `H` says it does not. Self-application is the diagonal; "do
the opposite" is the fixed-point-free transformation; universality is the
universal machine.

The universal machine deserves its own sentence, since it is the computational
form of Definition 1.2. `U` simulates any `p` on any `x`, so `f p` ranges over
all computable behaviors. The subtlety is that it reaches only the computable
ones.

_Kleene._ The recursion theorem points the move forwards. For any total
computable transformation on programs there is a program behaving exactly like
its own transform. Where Turing chose a transformation with no fixed point and
derived impossibility, Kleene took the fixed point as a gift.

_Lawvere (1969)._ In any cartesian closed category, a point-surjective map `A → Y^A`
forces every endomap `t : Y → Y` to have a fixed point. Contrapositively, a
fixed-point-free `t` forbids the point-surjection. Every classical instance is a
choice of category, `Y`, and `t`: sets with `Y = Bool` and `t = not` gives
Cantor; a syntactic category gives Gödel and Tarski; computable maps give Turing
and Rice.

_Yanofsky (2003)._ The readable modern account, and the template for Chapter 2.
It strips the category theory to a diagram of sets and writes each paradox as
one commuting square with different labels. The recipe becomes mechanical: name
the indices, the outcomes, and a transformation with no fixed point, then check
universality.

_The shared skeleton._ Four ingredients and one collapse. The ingredients are a
pool of things, a set of outcomes, a way of applying a thing to a thing, and a
change on outcomes. In Cantor: elements and subsets, membership values, asking
whether an element lies in a subset, swapping the values.

The collapse is that the pool plays both roles in the applying step, so a thing
can be applied to itself. That is the only genuine self-reference needed, and it
is the coincidence of domains that Definition 1.1 builds in by writing `A → A → Y`
with the same `A` twice. Form the self-application map, post-compose with the
change, and you have the diagonal description.

# Systems that describe themselves

Fix a domain `A` of _indices_ and a set `Y` of _outcomes_. Read an element of
`A` as a name, program, prompt, activation, or Gödel number.

*Definition 1.1 (System).* A _system_ is a function `f : A → A → Y`. Read `f a`
as the _behavior_ named by `a`, and `f a b` as that behavior's outcome on input
`b`. The _diagonal_ is `a ↦ f a a`.

The domains coincide, and that coincidence is the chapter's whole subject. It
lets a behavior be applied to a name of its own kind, in particular its own. In
different sets there would be no diagonal and no theorem.

*Definition 1.2 (Universality).* `f : A → A → Y` is _universal_, or
_point-surjective_, when every `g : A → Y` is named: `∀ g, ∃ a, f a = g`.

This is "the system can talk about itself," made precise. A proof-checker handed
the code of any predicate on proofs, an in-context learner promptable to any
behavior over prompts, a representation encoding any pattern over its own
states: each claims universality for the appropriate `A` and `Y`.

Two features matter downstream. First, the quantifier is over _every_ `g`, with
no restriction. Naming the nice or computable or intended behaviors is not
enough; the hypothesis must reach the pathological diagonal behavior too. This
is why real systems often escape: a programming language names only computable
functions. Chapter 3's hard work is exactly here.

Second, only point-surjectivity is asked: each `g` is `f a` for _some_ `a`, with
no uniqueness. A behavior may have many names or share one. That low bar is what
makes the impossibility strong; you cannot escape by making naming many-to-one.

Currying makes `A → A → Y` and `A → (A → Y)` the same type, so "a system" and "a
map from names to behaviors" are interchangeable. Under Curry-Howard a function
type is an implication and evaluation is modus ponens, so universality reads as
"every behavior is inhabited by a name." That is why the same three-line proof
appears in set theory, logic, and type theory texts with only the nouns changed.

Lawvere used a weaker cousin, _weak point-surjectivity_: for every `g` some `f a`
agrees with `g` on points. In `Set` the two coincide, so no theorem here is
affected, but it is why the categorical statement is more general than it looks.
When someone claims a system "is not really universal," the honest question is
whether it fails even the weak form, and usually it does, by naming only a
restricted class.

## The finite case, by counting

*Example 1.3.* No finite system is universal when `|Y| ≥ 2`. With `|A| = n` there
are `n` behaviors `f a` but `|Y|ⁿ` functions `A → Y`, and `n < 2ⁿ ≤ |Y|ⁿ`. Some
`g` is unnamed, for lack of room.

The smallest case shows counting and diagonalizing are one fact seen twice. Take
`A = {0, 1}`, `Y = Bool`, so there are four functions and `f` supplies two. Set
`g 0 = not (f 0 0)` and `g 1 = not (f 1 1)`. Then `g ≠ f 0`, since they differ
at `0`, and `g ≠ f 1`, since they differ at `1`. Pigeonhole says an unnamed
function exists; the diagonal points at one.

That is the whole difference, and it is why the diagonal survives into the
infinite case. When `A` is infinite there is no size comparison to make without
already knowing Cantor's theorem. The diagonal needs no count: it writes down `a ↦ not (f a a)`
and checks it differs from `f a` at `a`, uniformly in `a`.

*A worked infinite instance.* No `f : ℕ → ℕ → Bool` is universal. Define `g n = not (f n n)`.
For each `n`, `g` and `f n` disagree at `n`, so `g` is unnamed.

# Lawvere's fixed-point theorem

*Theorem 1.4 (Lawvere, 1969).* _Let `f : A → A → Y` be universal. Then every
`t : Y → Y` has a fixed point._

```lean
theorem lawvere {A Y : Type _} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g)
    (t : Y → Y) : ∃ y, t y = y :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨f a₀ a₀, (congrFun ha₀ a₀).symm⟩
```

_Proof._ Let `d a = t (f a a)`. By universality `f a₀ = d` for some `a₀`. Equal
functions agree at every point, so evaluating at `a₀` gives `f a₀ a₀ = d a₀ = t (f a₀ a₀)`.
In the Lean term, `congrFun ha₀ a₀` is that evaluation and `.symm` orients the
equation. ∎

Three moves. First, `d` is not chosen cleverly; `t` and `f` write it, by running
the diagonal and post-composing. It is an ordinary function, dangerous only
because of what universality forces.

*Remark 1.5 (Where the self-application happens).* In `f a₀ a₀ = t (f a₀ a₀)` the
index `a₀` plays three roles at once: the name of the behavior, the input it
runs on, and the point of evaluation. All three coincide because `d` was built
from the diagonal. That collapse is the diagonal in one symbol. Every proof
below has such an `a₀`; in Chapter 3 it is a query, in Chapter 4 a point of a
connected space.

*Remark 1.6 (Constructive content).* Given the witness for the single function
`d`, the fixed point is computed with no further choices: it is `f a₀ a₀`, and
the equation is verified by evaluating a known equality. No case split, no
excluded middle, no choice. Hence the Lean proof is a plain term, and the
boolean instances below need no axioms. Any nonconstructive step later is
charged to the reading of `t`, never to Lawvere.

*Three misreadings.* First, that the theorem says self-reference is paradoxical.
It says self-reference _plus a fixed-point-free transformation_ is impossible;
with a fixed point the identical construction yields Kleene's useful
self-referential object. Second, that it needs infinity or set-theoretic
strength.

# The section and retract form

*Definition 1.7 (Section).* A _section_ of `f : A → A → Y` is `s : (A → Y) → A`
with `f (s g) = g` for every `g`.

A section is a uniform chosen naming; point-surjectivity only promises names
exist. Every section gives point-surjectivity; the converse needs choice. The
section form holds verbatim in any cartesian closed category, which is how
Lawvere stated it.

*Theorem 1.8 (Lawvere, section form).* _If `f : A → A → Y` has a section, every
`t : Y → Y` has a fixed point._

```lean
theorem c1_lawvere_section {A Y : Type _} (f : A → A → Y)
    (s : (A → Y) → A)
    (hs : ∀ g : A → Y, f (s g) = g)
    (t : Y → Y) : ∃ y, t y = y := by
  refine ⟨f (s (fun a => t (f a a)))
    (s (fun a => t (f a a))), ?_⟩
  have h := congrFun (hs (fun a => t (f a a)))
      (s (fun a => t (f a a)))
  exact h.symm
```

_Proof._ Theorem 1.4 with the chosen name in place of the existential one. With
`d = fun a => t (f a a)` and `a₀ = s d`, the equation `hs d` says `f a₀ = d`,
and `congrFun` at `a₀` gives `f a₀ a₀ = t (f a₀ a₀)`. Since `s` is given rather
than extracted, the proof is a closed term with no case analysis. ∎

The section form makes visible that full point-surjectivity was never needed.
The proof consumed one name for one behavior.

```lean
theorem c1_section_universal {A Y : Type _} (f : A → A → Y)
    (s : (A → Y) → A)
    (hs : ∀ g : A → Y, f (s g) = g) :
    ∀ g : A → Y, ∃ a, f a = g :=
  fun g => ⟨s g, hs g⟩
```

_Proof._ `s g` witnesses the existential, since `f (s g) = g` is `hs g`. ∎

_Sections and retracts._ The condition `f ∘ s = id` says `A → Y` is a _retract_
of `A`. Lawvere's theorem is often stated this way: if `Y^A` is a retract of
`A`, every endomap of `Y` has a fixed point. Retracts are categorical, defined
by one equation and needing no elements, which is why the statement transports.

*Remark 1.9 (The cartesian closed statement).* A category is _cartesian closed_
when it has a terminal object `1`, binary products, and exponentials `Y^A` with
evaluation `ev : Y^A × A → Y`. In `Set` these are the one-point set, the
product, and the function set. These are exactly the structure the diagonal
proof consumes, and no more.

There, `f : A → Y^A` is _weakly point-surjective_ when every global point `g : 1 → Y^A`
has `a : 1 → A` with `f ∘ a = g` as points. Lawvere's theorem is that such an
`f` forces every `t : Y → Y` to have a fixed point `y` with `t ∘ y = y`. The
proof is the diagram our Lean term draws: form the diagonal `A → A × A`, follow
with `f × id` and evaluation, post-compose with `t`, transpose back, name the
result, and chase it around the square.

Nothing uses that the category is `Set`. This is the sense in which Cantor,
Gödel, Turing and the rest are literally one theorem. Cantor lives in `Set`.

# The contrapositive is the impossibility

*Corollary 1.10.* _If `t : Y → Y` satisfies `t y ≠ y` for all `y`, then no
`f : A → A → Y` is universal._

```lean
theorem no_universal {A Y : Type _} (t : Y → Y)
    (ht : ∀ y, t y ≠ y)
    (f : A → A → Y) : ¬ (∀ g : A → Y, ∃ a, f a = g) :=
  fun hf => match lawvere f hf t with
    | ⟨y, hy⟩ => ht y hy
```

_Proof._ Universality would give a fixed point of `t`, contradicting `ht`. ∎

*Remark 1.11.* This is the engine. A specific impossibility needs a reading of `Y`
and a fixed-point-free `t`. The classical pairs are in Chapter 2, the AI-safety
pairs in Chapter 3.

Two more shapes, quoted downstream. The first denies that any candidate exists,
rather than refuting one handed to it.

```lean
theorem c1_no_universal_exists {A Y : Type _} (t : Y → Y)
    (ht : ∀ y, t y ≠ y) :
    ¬ ∃ f : A → A → Y, ∀ g : A → Y, ∃ a, f a = g :=
  fun ⟨f, hf⟩ => match lawvere f hf t with
    | ⟨y, hy⟩ => ht y hy
```

_Proof._ Such an `f` would be universal, giving a fixed point of `t`. ∎

The second returns the diagonal index rather than the fixed point, which is what
most downstream proofs want: they need to point at the offending behavior.

```lean
theorem c1_lawvere_diagonal {A Y : Type _} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g)
    (t : Y → Y) : ∃ a, f a a = t (f a a) :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Name the diagonal behavior by `a₀` and evaluate the naming equation at
`a₀`. ∎

Same construction, two returns. When `t` is fixed-point-free the equation is a
contradiction; when `t` has a fixed point it is a self-referential program in
Kleene's sense. The theorem does not know which case it is in; `t` decides.

Concretely: with `Y = Bool` and `t` the identity, the diagonal gives `f a₀ a₀ = f a₀ a₀`,
a tautology and a harmless self-description. Replace `t` by negation and the
same index gives `f a₀ a₀ = not (f a₀ a₀)`, which cannot hold. The construction
did not change; only the transformation did.

# Three classical instances

*Example 1.12 (Cantor).* Take `Y = Bool` and `t` the negation. No boolean equals
its own negation, checked by exhaustion:

```lean
theorem bool_not_fpf : ∀ b : Bool, (!b) ≠ b := by decide
```

```lean
theorem cantor {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  match lawvere f hf (fun b => !b) with
  | ⟨y, hy⟩ => bool_not_fpf y hy
```

`hf` is the assumed surjection, `fun b => !b` the transformation, `lawvere`
returns `y` with `(!y) = y`, and `bool_not_fpf` refutes it. That one line
carries the entire mathematical content, decided by two-case exhaustion, which
is why Cantor for booleans needs no axioms.

The identification with textbook Cantor is definitional, not approximate. A
subset `S ⊆ A` is its indicator `χ_S : A → Bool`, so `P(A)` is `A → Bool` and a
surjection `A → P(A)` is a universal system `f : A → A → Bool`. Cantor's `D = { a : a ∉ f a }`
has indicator `a ↦ not (f a a)`, our diagonal for `t = not`.

*Example 1.13 (Russell).* Take `Y` to be propositions and `t` logical negation.
The behavior "indices not containing themselves" is the diagonal, and its own
membership is fixed by negation, which has no fixed point. This is Russell's
paradox as Corollary 1.10 with `t = ¬`. It is stated in prose because the
fixed-point-free step for propositions needs a classical principle.

That contrast is the first appearance of axiom-accounting. On `Bool`, negation
is a computation and `bool_not_fpf` is `decide`, importing nothing. On
propositions there is no finite set to try, and the smooth classical statement
leans on two-valuedness.

*Proposition 1.14 (The liar, named).* The diagonal points at the exact behavior on
which the system breaks.

```lean
theorem liar_query {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) :
    ∃ a, f a a = !(f a a) :=
  match hf (fun a => !(f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Name `a ↦ !(f a a)` by `a₀` and evaluate at `a₀`. ∎

This is `c1_lawvere_diagonal` at `Y = Bool`, `t = not`, and it does not conclude
`False`. It returns a live equation describing the pathology: a query the system
answers with the opposite of its own answer. Keeping the query rather than
collapsing to `False` is what lets Chapter 3 treat the offending input as an
object with meaning.

## What the flip needs

Whether a fixed-point-free endomap exists is a property of `Y` alone, and it is
the true precondition for an impossibility.

```lean
theorem c1_bool_has_fpf : ∃ t : Bool → Bool, ∀ b, t b ≠ b :=
  ⟨fun b => !b, bool_not_fpf⟩
```

```lean
theorem c1_unit_has_fixed_point
    (t : Unit → Unit) : ∃ u : Unit, t u = u :=
  ⟨(), rfl⟩

theorem c1_no_fpf_unit :
    ¬ ∃ t : Unit → Unit, ∀ u, t u ≠ u :=
  fun ⟨_t, ht⟩ => ht () rfl
```

_Proof._ `Unit` has one element, which every endomap fixes. ∎

Carry the reading forward. A system whose only outcome is "accept" cannot be
caught by the diagonal, because "accept" is a fixed point of everything. A
verifier that can only say yes is trivially consistent about itself.

_Manufacturing flips._ A fixed-point-free `t` on finite `Y` is a derangement. On
two points there is exactly one, the swap, which is boolean negation; on three,
the three-cycle, the shape of `c1_optFlip` below; on one, none. A sufficient
condition in general is that `Y` carry a free involution, or more weakly a
fixed-point-free permutation.

One caution. An exotic `t` is easy to write and yields a worthless
impossibility. The honest work is arguing that `t` is forced by the problem
rather than chosen for convenience. In Cantor, `t` is negation because
membership is two-valued. In Chapter 3 the flips are forced by the meanings of
"hallucinate," "inject," and "misclassify."

# A partial-function preview: toward Rice

Model a partial outcome as `Option Y`: `some y` means the behavior returned `y`,
`none` that it did not. A partial system is `f : A → A → Option Y`, and the
impossibility follows whenever `t` is fixed-point-free on `Option Y`.

The subtlety Rice exploits is that a useful `t` must disturb `none` as well. A
transformation fixing `none` would have a fixed point there and the argument
would stall. So the flip changes both whether a behavior returns and what it
returns.

```lean
def c1_optFlip : Option Bool → Option Bool
  | none => some true
  | some true => some false
  | some false => none

theorem c1_optFlip_fpf :
    ∀ o : Option Bool, c1_optFlip o ≠ o := by
  intro o
  cases o with
  | none => decide
  | some b => cases b <;> decide
```

_Proof._ A three-cycle on three concrete outcomes, checked case by case. ∎

By Corollary 1.10 no partial system into `Option Bool` is universal. The reading
is undecidability of a nontrivial behavioral property: the three-cycle builds a
behavior disagreeing with its own classification.

The pure definedness-flip is the cleanest computational instance. Track only
whether a behavior halts and let `t` swap the two outcomes. A universal partial
system is then exactly a halting decider, and the diagonal behavior is Turing's
`Dgn`.

# The engine, named once

*Definition 1.15 (Reflective verdict).* A _reflective verdict_ on `Q` is a
universal system `v : Q → Q → Bool`: every pattern of verdicts over `Q` is named
by an element of `Q`.

Read `v p q` as the verdict item `p` renders on item `q`. Both are drawn from
`Q`, so an item can judge itself and, crucially, can encode a whole judging
policy. Universality claims every policy `Q → Bool` is some single item's
policy.

*Theorem 1.16.* _No reflective verdict exists._

```lean
theorem no_reflective_verdict {Q : Type _}
    (v : Q → Q → Bool)
    (hv : ∀ g : Q → Bool, ∃ p, v p = g) : False :=
  cantor v hv
```

_Proof._ Immediate from Example 1.12. ∎

*Remark 1.17.* Theorem 1.16 is verbatim the Hallucination Trilemma, the Defense
Trilemma, and the truth-boundary coupling of Chapter 3. Nothing there adds to
the engine; only the intended meaning of `v p q` changes. The work is entirely
in the reading.

Be blunt about what this means. The mathematics of the AI-safety impossibilities
is finished; it is the one line above. Every remaining page of Chapter 3 argues
that a particular real system satisfies `hv`. Those are modeling claims, not
mathematical subtleties. If you doubt a Chapter 3 theorem, the place to press is
never the diagonal. It is always `hv`.

_The diagonal in a learning system._ Let `Q` be prompts and read `v p q` as the
verdict given to `q` when behavior has been fixed by prompt `p`. In-context
learning is the claim that a suitable `p` steers the model to a wide range of
verdict policies. If the range is all of them, the model is a reflective
verdict.

The diagonal prompt writes itself: the prompt asking for the opposite of the
verdict the model would give when steered to evaluate this very prompt.
Universality supplies `p₀` realizing that policy, and `v p₀ p₀` must equal its
own negation. The model cannot answer consistently, not through bad training,
but because the capability making it universal is inconsistent with a stable
answer.

Two caveats keep this honest. A real model ranges over the policies its
architecture and training make reachable, not all functions, which is why
Chapter 3 argues reachability rather than assuming it. And the diagonal prompt
is a construction, not necessarily a sentence a user would type, so part of the
modeling is arguing it is within reach of the steering mechanism.

# What the diagonal cannot give

*Remark 1.18.* The diagonal is silent on everything quantitative: not how many
liars there are, not how hard `a₀` is to find, not what reaching one costs an
adversary. And it requires genuine self-application. When a system instead lives
on a _connected_ domain with _continuous_ maps, the intermediate value theorem
takes over and delivers the same boundary object with metric content. That is
Chapter 4, and its refinements are Chapter 5.

Three questions it cannot answer, posed here because Chapters 4 and 5 exist to
answer them. _How many:_ the theorem produces one index and no measure of
whether the liar set is a point or a fat region. _How hard to find:_ it tells
you `a₀` exists and nothing about the cost of locating it, which is the whole
question against a resource-bounded adversary.

There is also a hypothesis it cannot do without. The engine needs genuine
universality, and when a system lacks it the theorem is silent, which is
correct: a system that cannot describe itself in full may well be consistent.
The interesting cases are those powerful enough that universality is plausible.

# Roadmap

Every later chapter is either an instantiation of the diagonal with a chosen `Y`
and `t`, or a change of engine when the diagonal's hypothesis is unavailable.

Chapter 2 does the work this chapter deferred: the arithmetization behind Gödel
and Tarski, the computability behind Turing and Rice, each as Yanofsky's square
filled in. Nothing there strengthens the engine; the labor is verifying
universality.

Chapter 3 is the payoff. It reads `Q`, `v`, and the boolean flip three ways. The
Hallucination Trilemma: a model cannot be faithful, calibrated, and covering at
once, because those three make its verdict reflective.

Chapter 4 changes engines, producing a boundary object with metric content.
Chapters 5 and 6 make that quantitative through attack-basin geometry and the
approximate bridges linking discrete to continuous. Chapter 7 returns to
concrete settings with both engines. Chapter 8 develops J-space, where a system
carries both a self-application and a topology, so both engines apply at once.

# Historical notes

The unification is Lawvere's _Diagonal arguments and cartesian closed
categories_ (1969), reprinted with commentary in 2006. It is terse; most readers
do better starting with a modern exposition.

Yanofsky's _A universal approach to self-referential paradoxes, incompleteness
and fixed points_ (2003) is that exposition, working Cantor, Russell, Gödel,
Tarski, Turing, and the recursion theorem as instances of one diagram using only
sets. It is the template for Chapter 2.

For the originals: Cantor's 1891 note; Russell's 1902 letter to Frege, in van
Heijenoort's _From Frege to Gödel_ (1967); Gödel (1931), with the diagonal lemma
treated cleanly in Boolos, Burgess and Jeffrey, _Computability and Logic_;
Tarski (1936); Turing (1936); and Kleene's _Introduction to Metamathematics_
(1952) for the recursion theorem.

The reading of these as constraints on learning systems is recent, and the
trilemmata of Chapter 3 are, as far as we know, first stated and machine-checked
in the companion Lean libraries this thesis tracks.
