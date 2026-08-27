import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Diagonal" =>

Every impossibility theorem in these notes descends from one move. You assume a
system is expressive enough to describe its own behavior, you build a description
that disagrees with whatever the system would do on itself, and the disagreement
is the theorem. Cantor used it against surjections onto power sets, Russell
against unrestricted comprehension, Gödel against provability, Tarski against
truth, Turing against halting. In 1969 F.\ William Lawvere showed these are not
five tricks but one, a single statement about maps in a cartesian closed
category. This chapter states that statement, proves it, and extracts the schema
that the rest of the book instantiates.

The mathematics here is elementary and entirely finite in spirit. The code
blocks are core Lean 4 with no libraries; they are elaborated when the book is
built, so the proofs you read are the proofs the kernel accepts. Read them as
part of the text, not as an appendix to it.

A word on how to use the chapter. The technical core is short. A reader in a
hurry can take Theorem 1.4 and its contrapositive, Corollary 1.6, and skip to
Chapter 3, where they do their work. Everything else here earns that shortness.
The long middle sections argue that the one hypothesis of Theorem 1.4 is exactly
the informal idea "the system can describe itself," and the long historical
section argues that five famous theorems are the one theorem read five ways. If
you already believe both claims, you already know this chapter. If you do not,
the point of the next forty pages is to make you believe them without hand
waving.

# One move, five disguises

Before any definitions, it helps to see the move in its natural habitats. The
five arguments below were discovered separately over sixty years, by people who
mostly did not think of themselves as doing the same thing. They look different
because their subject matter is different: sets, then logic, then computation.
The claim of this chapter, which we make precise in Theorem 1.4, is that the
differences are decoration. Underneath, each argument builds a function that
computes what the system does to a description and then changes the answer, and
each derives its contradiction from the same place: nothing can equal its own
change.

Read this section as motivation. Nothing in it is used later as a hypothesis;
the formal development starts fresh in the following section. What the section
buys you is the right to trust that Theorem 1.4 is not a toy. It is the shared
skeleton of the deepest limitative results in mathematics, and the AI-safety
theorems of Chapter 3 join that list by exhibiting the same skeleton.

## Cantor: more subsets than elements

In 1891 Cantor proved that no set is as large as its own collection of subsets.
Fix a set `A` and suppose, for contradiction, that some function
`f : A → P(A)` hits every subset, that is, for every subset `S` there is an
element `a` with `f a = S`. Cantor's subset is the set of elements that their own
image excludes:

`D = { a ∈ A : a ∉ f a }`.

By assumption `D` is `f a₀` for some `a₀`. Now ask the one question that the set
`D` was designed to make unanswerable: is `a₀` in `D`? If `a₀ ∈ D`, then by the
definition of `D` we have `a₀ ∉ f a₀ = D`, a contradiction. If `a₀ ∉ D`, then
`a₀` satisfies the membership condition, so `a₀ ∈ D`, again a contradiction. No
`a₀` survives, so no such `f` exists.

The whole argument turns on the phrase "their own image excludes." The element
`a` is fed its own description `f a`, and `D` records the disagreement between
`a` and `f a` on the single bit "does `a` belong." When we later replace subsets
by their indicator functions `A → Bool`, membership becomes a boolean, exclusion
becomes boolean negation, and `D` becomes the function `a ↦ not (f a a)`. That
function is the diagonal, and negation is the change that nothing can equal. Hold
that translation in mind; it is Example 1.12, and it is the reason `bool_not_fpf`
below is the entire content of Cantor's theorem.

Cantor's earlier and more famous use of the diagonal, from 1874 and refined in
1891, was to show the real numbers are uncountable, and it is the same argument
with the pool taken to be the natural numbers. Suppose a list `r₀, r₁, r₂, …`
claims to enumerate every real in `[0,1]` by their decimal expansions. Build a new
real whose `n`-th digit differs from the `n`-th digit of `rₙ`, say by replacing
each digit with a fixed different one. The new real differs from `rₙ` in its
`n`-th place, for every `n`, so it is not on the list, and the list was not
complete. Here the "system" is the enumeration `n ↦ rₙ`, the outcomes are digits,
the self-application is reading the `n`-th digit of the `n`-th real, and the change
is "pick a different digit," which has no fixed point among digits. The two
Cantor arguments, the power-set theorem and the uncountability of the reals, are
one theorem: a list of functions cannot include the function that disagrees with
each entry on the diagonal. We recover this from Theorem 1.4 by taking `A = ℕ`,
`Y` the digits, and `t` a fixed-point-free digit change; the failure of
universality is the incompleteness of the list.

## Russell: the set that lists the modest sets

Russell found his paradox in 1901 while reading Frege, and he sent it to Frege in
1902 in a letter that arrived as the second volume of the _Grundgesetze_ was in
press. Frege's system allowed unrestricted comprehension: any property carves out
the set of things having it. Russell chose the property "is not a member of
itself" and formed

`R = { x : x ∉ x }`.

Then `R ∈ R` holds exactly when `R ∉ R`. The sentence is its own negation, and no
sentence can be that. Frege's foundation collapsed on a single line.

Russell's `R` is Cantor's `D` with the indexing removed. Cantor kept a set `A` on
the outside and a candidate surjection `f`; Russell let the universe of sets play
both roles at once, so `f` becomes the identity "a set is its own description" and
the diagonal `a ↦ a ∉ f a` becomes `x ↦ x ∉ x`. Stripped of the surrounding `f`,
the paradox is more violent, because it does not derive a contradiction from an
extra assumption. It derives one from comprehension alone. The lesson the
twentieth century drew, and the lesson our Definition 1.2 encodes, is that the
danger is not self-reference as such but unrestricted self-reference: a system
that can name _every_ pattern over its own descriptions, with no gatekeeper, is
already inconsistent about the diagonal pattern.

The two standard repairs are both instructive, because they are the two ways every
later chapter escapes an impossibility. One repair, Zermelo's, restricts
comprehension: you may not form the set of all `x` with a property, only the subset
of an already-given set with that property. This breaks the step where `R` is
formed at all, because there is no ambient set of "all sets" to carve from.
Translated into our terms, it denies universality: not every pattern over the
universe is named by an object of the universe. The other repair, Russell's own
theory of types, stratifies the universe into levels and forbids a set from taking
itself as a member, so `x ∈ x` is not even a well-formed question. Translated into
our terms, it breaks the coincidence of domains in `A → A → Y`: the judge and the
judged are forced into different types, the diagonal cannot form, and the engine
has nothing to grip. Chapter 3's positive results use both moves. Sometimes a
safety property is achievable because the relevant behaviors are not all namable,
the Zermelo escape; sometimes it is achievable because the system is typed so that
it cannot be applied to itself, the Russell escape. Knowing which escape a design
relies on is knowing why it works.

## Gödel: a sentence that reads its own unprovability

Gödel's 1931 theorem is the same move performed inside arithmetic, and the
performance is what made it hard. Cantor and Russell could write `∉` directly.
Gödel had to build, out of nothing but addition and multiplication, a way for
arithmetic to talk about its own sentences and proofs. He assigned a number to
each formula and each proof, a coding now called Gödel numbering, and then showed
that the relation "the proof coded by `p` proves the sentence coded by `n`" is
itself expressible by an arithmetic formula. Once provability is an arithmetic
predicate `Prov`, arithmetic can quote itself.

The engine is the diagonal lemma: for any formula `φ(x)` with one free variable
there is a sentence `G` such that the theory proves `G ↔ φ(⌜G⌝)`, where `⌜G⌝` is
the numeral coding `G`. Feed the lemma the formula "`x` is not provable" and you
get a sentence `G` equivalent to "`G` is not provable." Now suppose the theory is
consistent and proves or refutes every sentence. If it proves `G`, then `G` is
provable, but `G` says it is not, so the theory proves a falsehood about itself
and is inconsistent. If it refutes `G`, it proves "`G` is provable," which in a
consistent theory forces an actual proof of `G`, and again both `G` and its
negation are theorems. Either way completeness and consistency cannot both hold.

The diagonal lemma _is_ the fixed-point theorem of this chapter, in the special
case where the transformation `t` is negation of provability. The theory's
ability to represent `Prov` is universality: it is the assumption that every
arithmetic property of sentences, including the property we build by diagonalizing,
is itself named by a sentence. The sentence `G` is the fixed point. What Gödel
added to Cantor was not a new idea about self-reference but a heroic amount of
coding to make an unassuming system, arithmetic, rich enough to be its own `f`.
In Chapter 2 we make this exact, and there the coding is where the labor lives;
the diagonal is one line.

Two features of the arithmetization are worth flagging now, because they are where
the diagonal's abstract hypothesis meets a concrete system, and Chapter 2 will
have to check them by hand. The first is representability. It is not enough that
provability be _definable_ by some formula; the formula must _track_ provability
in the theory itself, so that when a proof exists the theory proves that it does,
and the coding of "the proof `p` checks `n`" is a formula the theory can verify on
numerals. This is the arithmetic version of universality: the theory names, and
correctly names, properties of its own sentences. Weak theories fail here, which
is why incompleteness needs a lower bound on strength, usually a fragment of
arithmetic strong enough to represent all computable relations. The second is the
distinction between the first and second incompleteness theorems. The first, which
is the diagonal above, produces an undecided sentence `G`. The second observes
that the whole argument "if the theory is consistent then `G` is unprovable" can
itself be carried out inside the theory, so the theory proves "consistency implies
`G`," and since it cannot prove `G` it cannot prove its own consistency. The
second theorem is the first theorem read inside the system, and it is the
prototype for the self-defeating safety guarantees of Chapter 3, where a defense
that could certify its own soundness would thereby refute it.

Löb's theorem, from 1955, sharpens the picture and is worth naming because it is
the fixed-point theorem for the modality "is provable." It says that if the theory
proves "if `S` is provable then `S`," then it already proves `S` outright. The
only sentences a sound theory can honestly assert to be self-guaranteeing are the
ones it can prove anyway. Read through Lawvere, Löb is the statement that the
provability operator has no nontrivial fixed points of a certain shape, and it is
the reason a system cannot bootstrap trust in itself. We do not use Löb directly,
but it stands behind the recurring theme that self-certification collapses, and a
reader who wants the deepest version of "no system validates itself" should read
Löb after this chapter.

## Tarski: truth is not one of the definable notions

Tarski's undefinability theorem, from work of the early 1930s, is Gödel's move
aimed at truth instead of provability. Suppose arithmetic could define its own
truth predicate: a formula `True(x)` such that `True(⌜S⌝)` holds exactly when `S`
is true. Apply the diagonal lemma to the formula "`x` is not true" and obtain a
sentence `L` equivalent to "`L` is not true." Then `L` is true iff `L` is not
true, which is impossible. So no such `True` is definable in the language it
would be about.

`L` is the liar sentence, "this sentence is false," and Tarski's theorem is the
observation that a sufficiently expressive language cannot host its own liar
without contradiction. The transformation `t` is again negation; the output set
`Y` is truth values; universality is the assumed definability of truth. The moral
Tarski drew, the separation of object language from metalanguage, is the same
gatekeeping move that set theory used against Russell. You may speak of truth for
a language, but only from outside it. Our Corollary 1.6 states the abstract
reason: negation has no fixed point, so nothing over which negation acts can be
universal about itself.

## Turing: no program decides halting

Turing's 1936 paper introduced the machines that bear his name and used the
diagonal to show that halting is undecidable. Suppose a program `H` decides, for
every program `p` and input `x`, whether `p` halts on `x`. Build a program `Dgn`
that on input `p` runs `H` on the pair `(p, p)` and then does the opposite: if
`H` says `p` halts on `p`, then `Dgn` loops forever; if `H` says `p` does not
halt on `p`, then `Dgn` halts. Now run `Dgn` on its own code. `Dgn` halts on
`Dgn` exactly when `H` reports that it does not, and loops exactly when `H`
reports that it does. `H` is wrong about `Dgn`, so no correct `H` exists.

The self-application `p` on `p` is the diagonal; the "do the opposite" step is the
fixed-point-free transformation. Universality here is the existence of a universal
machine, which Turing also constructed: the fact that programs can be run on the
codes of programs, including their own. The halting problem, Rice's theorem, and
the rest of computability's negative results are this construction with the output
set and the transformation changed. Exercise 1.13 and Chapter 2 develop the
partial-function version, where the outputs may be undefined and the relevant
transformation flips definedness.

The universal machine deserves a sentence of its own, because it is the exact
computational form of Definition 1.2. Turing showed there is one machine `U` that,
given the code of any machine `p` and an input `x`, simulates `p` on `x`. That is
universality: a single `f` such that `f p` ranges over all the behaviors, at least
all the computable ones. The subtlety, and the reason computability is subtler
than set theory here, is that `U` only reaches the _computable_ behaviors, not all
functions. So the diagonal program `Dgn` is computable relative to `H`, and if `H`
were computable then `Dgn` would be a computable behavior that `U` names,
completing the contradiction. When `H` is dropped the diagonal still names a
perfectly good function, but not a computable one, so no contradiction follows and
the reals stay uncountable without arithmetic collapsing. The lesson carries into
AI safety directly: a system is exposed to the diagonal only over the behaviors it
can actually realize, and the force of an impossibility theorem is exactly the
size of that class. Chapter 3's theorems work to show the class is large enough to
contain the diagonal behavior they build.

## Kleene: the same move, run forwards

The diagonal usually appears as a weapon, producing contradictions. Kleene's
recursion theorem points it the other way and produces programs. It says that for
any total computable transformation on programs there is a program that behaves
exactly like its own transform: a fixed point in code. This is the constructive
face of the same result. Where Turing chose a transformation with no fixed point
and derived impossibility, Kleene took the guaranteed fixed point as a gift and
built self-reproducing and self-referential programs from it.

We flag Kleene because it warns against a misreading. The theorem of this chapter
does not say self-reference is bad. It says self-reference plus a fixed-point-free
transformation is impossible. When the transformation _has_ a fixed point, the
same universality that would have caused a paradox instead hands you a useful
self-referential object. Chapter 3's positive results, the places where a safety
property _is_ achievable, all live on this side of the line: they exhibit the
fixed point rather than forbid it.

## Lawvere: one theorem behind all of them

In 1969 Lawvere published _Diagonal arguments and cartesian closed categories_
and proved that the arguments above are instances of a single theorem about maps.
His setting is any cartesian closed category, an abstract universe of "spaces" and
"functions" with enough structure to form function spaces `Y^A` and to evaluate.
His hypothesis is that some map `A → Y^A` is point-surjective, meaning it reaches
every point of the function space `Y^A`. His conclusion is that every endomap
`t : Y → Y` has a fixed point. The contrapositive, the form we use, is that a
fixed-point-free `t` forbids any such point-surjection.

Every classical instance is a choice of category, of `Y`, and of `t`. In the
category of sets, `Y = Bool` and `t = not` gives Cantor. In a category built from
a theory's sentences, `Y` a two-valued object and `t` negation gives Gödel and
Tarski. In a category of computable maps, `Y` a type of outcomes and `t` an
outcome flip gives Turing and Rice. The categorical wrapper is what makes "the
same theorem" a literal statement rather than an analogy. We will not need the
full category theory; the set-level version in Theorem 1.4 carries all the weight
in these notes, and Remark 1.16 records the one categorical upgrade, the section
form, that we prove in Lean.

## Yanofsky: the schema written out

Yanofsky's 2003 paper _A universal approach to self-referential paradoxes,
incompleteness and fixed points_ is the most readable modern account of Lawvere's
insight, and it is the template for Chapter 2. Yanofsky strips the category theory
down to a diagram of sets and functions and writes each classical paradox as the
same commuting square with different labels. The value of his presentation, for
us, is that it makes the recipe explicit and mechanical. To produce an
impossibility theorem you name the indices, name the outcomes, name the
transformation with no fixed point, and check universality. Everything else is
filled in by the schema.

That recipe is what the rest of this chapter formalizes. The formal core is one
theorem and its contrapositive; the classical instances are three short
corollaries; and the AI-safety instances of Chapter 3 are the same corollaries
with `Y` and `t` reinterpreted. We now leave the history and build the machine.

## The shared skeleton, abstractly

Before the definitions, it is worth writing the common pattern down once, in the
vocabulary the five arguments share, so that the formal statement in the next
section reads as a transcription rather than a surprise. Each argument has four
ingredients and one collapse.

The four ingredients are a pool of _things_, a set of _outcomes_, a way of
_applying_ a thing to a thing, and a _change_ on outcomes. In Cantor the things
are elements and subsets, the outcomes are the two membership values, applying is
asking whether an element lies in a subset, and the change is swapping the two
values. In Turing the things are programs and inputs, the outcomes are halting and
looping, applying is running, and the change is doing the opposite. In Gödel the
things are sentences, the outcomes are provable and not, applying is asking
whether a sentence proves another, and the change is negating provability. The
labels differ; the four slots are always filled.

The collapse is that the pool of things plays both roles in the applying step. A
thing is both something that acts and something that can be acted upon, so a thing
can be applied to itself. This is the only place the arguments need genuine
self-reference, and it is exactly the coincidence of domains that Definition 1.1
below builds in by writing `A → A → Y` with the same `A` twice. Once a thing can
be applied to itself, you can form the _self-application_ map that sends each
thing to the outcome of applying it to itself, and then post-compose with the
change. Call the result the diagonal description. It is a perfectly legitimate
description of a behavior over the pool, so if the system describes _everything_,
it describes the diagonal description too. That is where the argument dies: the
thing describing the diagonal description, applied to itself, must produce an
outcome that the change moves to itself, and the change was chosen to move nothing
to itself.

Yanofsky draws this as a single commuting square. Up one side you take a thing to
its self-application and read off an outcome; along the other you apply the change;
and universality closes the square by naming the composite inside the pool. The
square commutes for structural reasons, and its commuting at the diagonal point is
the equation `y = t y`. Everything in this chapter is that square, drawn in `Set`,
with the labels left as variables so that Chapter 3 can relabel them. If you keep
the four slots and the one collapse in mind, you will recognize the pattern in
every later theorem before you have read its proof.

# Systems that describe themselves

Fix two sets, a domain `A` of _indices_ and a set `Y` of _outcomes_.
Think of an element of `A` as a name, a program, a prompt, an activation, or
a Gödel number; think of `Y` as the possible answers the system can give.

**Definition 1.1 (System).** A _system_ is a function `f : A → A → Y`. We read
`f a` as the _behavior_ named by the index `a`, a function `A → Y`; and `f a b`
as the outcome that behavior `a` produces on input `b`. The _diagonal_ of the
system is the function `a ↦ f a a`: what each behavior does when applied to its
own name.

The two-argument shape `A → A → Y` is doing quiet work, so it is worth reading
slowly. The first argument is the name of a behavior and the second is the input
that behavior consumes. The domains coincide, both are `A`, and that coincidence
is the whole subject of the chapter. It is what lets a behavior be applied to a
name of its own kind, and in particular to its own name. If the two roles lived in
different sets there would be no diagonal and no theorem. The move we are studying
is available exactly when the things a system talks about and the things a system
is are drawn from one pool.

**Definition 1.2 (Universality).** A system `f : A → A → Y` is _universal_, or
_point-surjective_, if every function `g : A → Y` is named by some index: for all
`g` there is an `a` with `f a = g`. Formally, `∀ g : A → Y, ∃ a, f a = g`.

Universality is what "the system can talk about itself" means precisely. A
proof-checker that can be handed the code of any predicate on proofs, an
in-context learner that can be prompted to imitate any behavior over prompts, a
representation that encodes any pattern over its own states: each is a claim of
universality for the appropriate `A` and `Y`.

Two features of the definition deserve emphasis, because later chapters lean on
them and because the theorem is stronger than it first looks.

First, universality quantifies over _every_ function `g : A → Y`, with no
restriction. It is not enough for `f` to name the nice behaviors, or the
computable ones, or the ones a designer intended. The hypothesis demands that the
naming reach the pathological behaviors too, including the one we are about to
build by diagonalizing. This is why real systems often escape the theorem: a
programming language names only the computable functions, not all functions, so
its `f` is not universal in the sense of Definition 1.2. The AI-safety arguments
of Chapter 3 do their hard work exactly here, arguing that some particular class
of behaviors really is named in full.

Second, the definition asks only for point-surjectivity, that each `g` is `f a`
for _some_ `a`. It says nothing about uniqueness. A behavior may have many names,
or a name may be shared, and the theorem does not care. All it uses is that a
name exists for the one behavior it constructs. That is a low bar, which is what
makes the impossibility strong: you cannot escape by making the naming
many-to-one or wasteful.

A note on the shape `A → A → Y`. We could equally have written a system as a
single function `A → (A → Y)` into the function space, and in Lean these are the
same type: `A → A → Y` is read as `A → (A → Y)`, and a value `f a` is literally an
element of `A → Y`. This identity, currying, is why "a system" and "a map from
names to behaviors" are interchangeable descriptions, and it is the set-level
shadow of the exponential object in Remark 1.9. It also connects to logic through
the Curry-Howard correspondence, under which a function type is an implication and
evaluation is modus ponens. Universality then reads as "every behavior is
inhabited by a name," and the diagonal construction is the proof-theoretic move
that turns unrestricted self-reference into a contradiction. We will not lean on
Curry-Howard, but it is the reason the same three-line proof appears in a set
theory book, a logic book, and a type theory book with only the nouns changed.

Point-surjectivity has a weaker cousin that Lawvere actually used and that is
worth knowing by name, because it is the minimal hypothesis. A map is _weakly
point-surjective_ if for every `g : A → Y` there is an `a` such that `f a` and `g`
agree, which for our purposes is the same as `f a = g` since we are in `Set`; in a
general category the weak form asks only for agreement on points, which is
strictly weaker than equality of maps. The distinction does not affect any theorem
in these notes, because all our instances live in `Set` where the two coincide,
but it is why the categorical statement of Remark 1.9 is more general than a naive
reading suggests. When someone claims a system "is not really universal," the
honest question is whether it fails even the weak form, and usually it does, by
naming only a restricted class of behaviors.

## The finite case, by counting

**Example 1.3.** No _finite_ system is universal when `Y` has at least two
elements. If `A` has `n` elements then there are exactly `n` behaviors of the
form `f a`, one for each index. But the set of _all_ functions `A → Y` has
`|Y|` choices at each of the `n` inputs, hence `|Y|ⁿ` functions in total. For
`|Y| ≥ 2` we have `n < 2ⁿ ≤ |Y|ⁿ`, so there are strictly more functions than
names, and some `g` is left unnamed. Universality fails for sheer lack of room.

It is worth doing the smallest case by hand, because it shows the counting and
the diagonal are the same fact seen twice. Take `A = { 0, 1 }` and `Y = Bool`, so
`n = 2` and there are `2² = 4` functions `A → Bool`. A system `f` supplies two of
them, `f 0` and `f 1`. Write out the diagonal values `f 0 0` and `f 1 1` and form
the function `g` that flips each: `g 0 = not (f 0 0)` and `g 1 = not (f 1 1)`.
Then `g` cannot be `f 0`, because they differ at input `0`, and `g` cannot be
`f 1`, because they differ at input `1`. So `g` is one of the four functions that
`f` does not name, whatever `f` was. The pigeonhole count told us an unnamed
function exists; the diagonal _points at one_.

That last sentence is the whole difference between counting and diagonalizing, and
it is why the diagonal survives into the infinite case where counting says
nothing. When `A` is infinite there is no comparison of sizes to make. There are
infinitely many names and infinitely many functions, and a naive count cannot
distinguish the two infinities without already knowing Cantor's theorem. The
diagonal needs no count. It writes down a specific function, `a ↦ not (f a a)`,
and checks that this one function differs from `f a` at the input `a`, for every
`a` at once. The construction is uniform in `a` and indifferent to whether `A` is
finite. Counting is a special effect of finiteness; the diagonal is the reason,
and it keeps working when the effect is gone.

Exercise 1.1 asks you to turn the two-element case into the general finite claim
and then to notice that your unnamed `g` is exactly the function produced by
`liar_query` below. The counting proof and the diagonal proof are not two proofs.
They are one proof with the arithmetic removed.

## The infinite case, by diagonal

**A worked infinite instance.** No system `f : ℕ → ℕ → Bool` is universal. There is no counting
here to save us: there are infinitely many names `f 0, f 1, f 2, …` and infinitely
many behaviors `ℕ → Bool`, and the two infinities cannot be compared without
already knowing the answer. The diagonal settles it directly. Define
`g : ℕ → Bool` by `g n = not (f n n)`. For each `n` the behaviors `g` and `f n`
disagree at the single input `n`, because `g n = not (f n n)` while `f n` at `n`
is `f n n`, and a boolean differs from its negation. So `g` is not `f n` for any
`n`, and `g` is unnamed. Universality fails, and it fails by pointing at a
specific unnamed behavior rather than by an existence count.

This is the whole of the boolean Cantor theorem, and it is exactly `cantor`
specialized to `A = ℕ`, but writing it out for `ℕ` is worth the space because it
shows the machinery running where intuition is weakest. Nothing about `ℕ` was
used except that we could form `g` and evaluate it at each `n`. The same lines
work for any `A` at all: replace `n` by `a` throughout and the argument is
unchanged, which is why the general theorem below carries no cardinality
hypothesis. The infinite case is not harder than the finite case. It is the finite
case with the counting step, which was never load-bearing, deleted. Readers who
first met the diagonal as a trick for the uncountability of the reals often carry
away the impression that it is about sizes of infinity. It is not. It is about a
function that disagrees with a list on the diagonal, and sizes of infinity are one
downstream consequence.

# Lawvere's fixed-point theorem

**Theorem 1.4 (Lawvere, 1969).** _Let `f : A → A → Y` be universal. Then every
map `t : Y → Y` has a fixed point: some `y` with `t y = y`._

```lean
theorem lawvere {A Y : Type _} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g) (t : Y → Y) : ∃ y, t y = y :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨f a₀ a₀, (congrFun ha₀ a₀).symm⟩
```

_Proof._ Consider the _diagonal behavior_ `d : A → Y`, `d a = t (f a a)`: apply
each behavior to its own name, then transform the outcome by `t`. By
universality `d` is named, so there is an index `a₀` with `f a₀ = d`. Two
functions that are equal are equal at every point, so evaluate at `a₀`:
`f a₀ a₀ = d a₀ = t (f a₀ a₀)`. Thus `f a₀ a₀` is fixed by `t`. In the Lean
proof, `congrFun ha₀ a₀` is exactly the step "equal functions agree at `a₀`," and
`.symm` orients the equation as a fixed point. ∎

Three lines, no arithmetic, no topology, no continuity. Everything downstream is
a reading of these three lines. It is worth dwelling on what the proof used:
only that behaviors can be applied to their own names, and that a named behavior
can be recovered. That is the whole of self-reference.

Let us take the proof apart once, at the pace of someone seeing it for the first
time, because the same three moves recur in every instance and it pays to
recognize them by name.

The first move is the construction of `d`. We do not pick `d` cleverly; we let the
transformation `t` and the system `f` write it for us. The recipe is fixed: run
the diagonal `a ↦ f a a`, then post-compose with `t`. This `d` is a perfectly
ordinary function `A → Y`, and nothing about it announces that it is dangerous. It
is dangerous only because of what universality will force.

The second move is the appeal to universality. We hand `d` to the hypothesis and
receive an index `a₀` with `f a₀ = d`. This is the only place the hypothesis is
used, and it is used on the single function `d`, not on any others. If you were
building a system and wanted to dodge the theorem, this is the equation you would
have to prevent, and Definition 1.2 says you cannot: universality names
everything, `d` included.

The third move is evaluation on the diagonal. We have an equation between
functions, `f a₀ = d`. Functions are equal when they agree everywhere, so in
particular they agree at the point `a₀`. Evaluating both sides at `a₀` turns the
functional equation into a numerical one, `f a₀ a₀ = d a₀`, and unfolding `d` on
the right gives `f a₀ a₀ = t (f a₀ a₀)`. The quantity `f a₀ a₀` is now visibly a
fixed point of `t`. The Lean term names this quantity `f a₀ a₀`, produces the
equation with `congrFun ha₀ a₀`, and flips its direction with `.symm` to match the
`t y = y` we promised.

**Remark 1.5 (Where the self-application happens).** The subtlety, such as it is,
is that `a₀` appears in three roles at once in the line `f a₀ a₀ = t (f a₀ a₀)`.
It is the name of the behavior `f a₀`; it is the input that behavior is run on;
and it is the point at which we evaluate the naming equation. All three coincide
because `d` was built from the diagonal, where name and input are forced equal,
and universality then supplies a single `a₀` that names this particular `d`. The
collapse of three roles into one index is the diagonal, in one symbol. Every proof
in the book has an `a₀` like this. In Chapter 3 it is a specific query; in Chapter
4 it is a specific point of a connected space.

**Remark 1.6 (Constructive content).** The proof is constructive in a precise
sense. Given the witness `a₀` that universality provides for the one function `d`,
the fixed point is computed with no further choices: it is literally `f a₀ a₀`,
and the equation `t (f a₀ a₀) = f a₀ a₀` is verified by evaluating a known
equality at a known point. There is no case split, no excluded middle, no appeal
to choice. This matters for two reasons. It is why the Lean proof is a plain term
rather than a tactic script fighting with classical logic, and it is why the
boolean instances below need no axioms at all, a point we return to when we
contrast Cantor with Russell. When Chapter 3 audits which safety theorems are
constructive and which import a classical principle, the audit starts here: the
engine adds nothing, so any nonconstructive step is charged to the reading of `t`,
not to Lawvere.

**Three common misreadings.** The proof is short enough that its meaning is easy
to over- or under-state, and three misreadings recur often enough to name.

The first is to think the theorem says self-reference is paradoxical. It does not.
It says self-reference together with a fixed-point-free transformation is
impossible. When the transformation has a fixed point, the identical construction
produces that fixed point as a useful self-referential object, which is Kleene's
recursion theorem. The theorem is neutral about self-reference; it is the
combination with an "always change the answer" map that cannot coexist with
universality.

The second is to think the theorem needs infinity, or large cardinals, or some
subtle set-theoretic strength. It needs none. The proof is finite, it is
constructive, and it runs verbatim when `A` and `Y` are finite, where it reduces to
the counting of Example 1.3. Cantor's theorem about infinite sets is a corollary,
not the content. The content is that a function which disagrees with each named
behavior on the diagonal cannot itself be named, and that is a statement about one
function and one evaluation.

The third is to think universality is a mild or generic hypothesis. It is the
whole game. Almost no natural system is universal, because naming _every_ behavior,
including the deliberately perverse diagonal one, is a severe demand. Every
impossibility theorem in the book is, in the end, an argument that some specific
system meets this severe demand, and every escape from an impossibility theorem is,
in the end, a demonstration that it does not. If you remember one thing from this
chapter, remember that the diagonal is trivial and the hypothesis is everything.

# The section and retract form

Definition 1.2 asked for point-surjectivity: for each `g` there _exists_ an index.
Lawvere's own statement uses a slightly different and often more convenient
hypothesis, a section. A section is a chosen inverse to naming, a single function
`s : (A → Y) → A` that hands you, for each behavior `g`, a specific name `s g`
that works.

**Definition 1.7 (Section).** A _section_ of a system `f : A → A → Y` is a
function `s : (A → Y) → A` such that `f (s g) = g` for every `g : A → Y`.

The two hypotheses are close but not identical. A section is a uniform, chosen
naming; point-surjectivity only promises that names exist, without choosing them.
Every section gives point-surjectivity, since `s g` is a witness. The converse
needs a choice principle to pick one witness per behavior, which is why the
categorical literature prefers sections: the section form is the one that holds
verbatim in any cartesian closed category, with no appeal to choice, and it is how
Lawvere stated the theorem. The section form is also strictly weaker as a
hypothesis in constructive settings, hence strictly stronger as a theorem. Our
downstream needs only the point-surjective form, but the section form is worth
proving once, because it is the version that transports to categories and it makes
the constructive content of Remark 1.6 fully explicit.

**Theorem 1.8 (Lawvere, section form).** _If `f : A → A → Y` has a section
`s : (A → Y) → A`, then every `t : Y → Y` has a fixed point._

```lean
theorem c1_lawvere_section {A Y : Type _} (f : A → A → Y) (s : (A → Y) → A)
    (hs : ∀ g : A → Y, f (s g) = g) (t : Y → Y) : ∃ y, t y = y := by
  refine ⟨f (s (fun a => t (f a a))) (s (fun a => t (f a a))), ?_⟩
  have h := congrFun (hs (fun a => t (f a a))) (s (fun a => t (f a a)))
  exact h.symm
```

_Proof._ The proof is Theorem 1.4 with the chosen name in place of the existential
one. Write `d = (fun a => t (f a a))` for the diagonal behavior and let
`a₀ = s d` be the name the section assigns it. The section equation `hs d` says
`f a₀ = d`, and evaluating it at `a₀` with `congrFun` gives `f a₀ a₀ = t (f a₀ a₀)`.
The witness is `f a₀ a₀`, and `.symm` orients the equation. Because `s` is given
rather than extracted, the whole proof is a closed term with no case analysis. ∎

The section form makes visible that point-surjectivity was never really needed in
full. All the proof consumed was one name for one behavior, `d`. A section is just
a systematic way of always having that name to hand. The next lemma records the
easy direction of the relationship, that a section is at least as strong as
universality, which is what lets Theorem 1.8 subsume Theorem 1.4 in practice.

```lean
theorem c1_section_universal {A Y : Type _} (f : A → A → Y) (s : (A → Y) → A)
    (hs : ∀ g : A → Y, f (s g) = g) : ∀ g : A → Y, ∃ a, f a = g :=
  fun g => ⟨s g, hs g⟩
```

_Proof._ Given any `g`, the name `s g` works: `f (s g) = g` is exactly `hs g`. So
`s g` witnesses the existential. ∎

**Sections, retracts, and why the name.** The word _section_ comes from the
picture of `f` as a projection: `s` is a one-sided inverse, a way of sectioning
back up through `f`. The dual word is _retract_. The condition `f ∘ s = id` on
behaviors says the function space `A → Y` is a _retract_ of the index set `A`
along `f` and `s`: you can embed every behavior into `A` by `s` and recover it by
`f`, so `A → Y` sits inside `A` as a retract. Lawvere's theorem is often stated in
exactly this retract language, "if `Y^A` is a retract of `A` then every endomap of
`Y` has a fixed point," and that is the cleanest way to see why it transports to any
cartesian closed category: retracts are a categorical notion, defined by the single
equation `f ∘ s = id`, needing no elements. The set-level `hs : ∀ g, f (s g) = g`
is that equation written pointwise. When Chapter 3 wants to claim a system is
universal, the strongest and most transportable way to do it is to exhibit `s`
explicitly, that is, to give a construction that produces, for any target behavior,
an index realizing it. A retract is a construction; a surjection is only an
existence claim. Whenever a proof can afford the retract, it should prefer it,
because it is constructive and it is the form the categorical statement wants.

**Remark 1.9 (The cartesian closed statement).** A category is _cartesian closed_
when it has three things: a terminal object `1`, whose global points `1 → X` play
the role of "elements" of `X`; binary products `X × Z`, packaging a pair of maps
into one; and, for each pair of objects, an exponential object `Y^A` together with
an evaluation map `ev : Y^A × A → Y` that is universal among ways of applying an
`A`-indexed family to an argument. In `Set` these are the one-point set, the
cartesian product, and the set of functions `A → Y` with ordinary function
application. The point of the abstraction is that products, exponentials, and
evaluation are exactly the structure the diagonal proof consumes, and no more.

In such a category, a map `f : A → Y^A` is _weakly point-surjective_ if for every
global point `g : 1 → Y^A` there is a point `a : 1 → A` with `f ∘ a = g` as points,
that is, they evaluate the same on every argument. Lawvere's theorem is that such
an `f` forces every endomap `t : Y → Y` to have a fixed point `y : 1 → Y` with
`t ∘ y = y`. The proof is the exact diagram our Lean term draws. Form the diagonal
`A → A × A`, follow it with `f × id` and then evaluation to get the
self-application `A → Y`, post-compose with `t`, and transpose back to a point of
`Y^A`. Weak point-surjectivity names this point by some `a`, and chasing `a`
around the resulting square yields `y = t y` at the diagonal. Every arrow in that
chase is built from a product, an exponential, or evaluation.

Nothing in the argument uses that the ambient category is `Set`. This is the sense
in which Cantor, Gödel, Turing, and the rest are literally the same theorem: they
are Theorem 1.8 in different cartesian closed categories. Cantor lives in `Set`.
Gödel and Tarski live in a syntactic category built from a formal theory, where
objects are formulas-with-free-variables and maps are provable substitutions, and
where the exponential encodes "formulas about formulas"; the coding Gödel labored
over is precisely the construction of enough cartesian closure for the diagonal to
run. Turing and Rice live in a category of computable maps, where the exponential
is the set of programs and evaluation is the universal machine. Each classical
theorem is the failure of weak point-surjectivity forced by a fixed-point-free `t`
in its own category. We do the categorical proof in prose and keep the Lean
development in `Set`, since every instance in these notes is a set-level statement
and the set proof is what the kernel checks. A reader who wants the diagram drawn
in full should consult Lawvere's paper or Yanofsky's exposition; our
`c1_lawvere_section` is the same statement with the section made explicit, which is
the form that transports to any cartesian closed category without a choice
principle.

# The contrapositive is the impossibility

Read Theorem 1.4 backwards. If some transformation of outcomes has _no_ fixed
point, then no system can be universal. This is the shape every later result
takes: name a behavior-flip that nothing is fixed by, and universality collapses.

**Corollary 1.10.** _If `t : Y → Y` satisfies `t y ≠ y` for all `y`, then no
`f : A → A → Y` is universal._

```lean
theorem no_universal {A Y : Type _} (t : Y → Y) (ht : ∀ y, t y ≠ y)
    (f : A → A → Y) : ¬ (∀ g : A → Y, ∃ a, f a = g) :=
  fun hf => match lawvere f hf t with
    | ⟨y, hy⟩ => ht y hy
```

_Proof._ If `f` were universal, Theorem 1.4 would produce a fixed point `y` of
`t`, contradicting `t y ≠ y`. ∎

**Remark 1.11.** Corollary 1.10 is the engine. To obtain a specific impossibility
one supplies (i) a reading of `Y`, and (ii) a fixed-point-free `t`. The rest of
this book is a catalogue of such pairs. The classical ones are in Chapter 2; the
AI-safety ones in Chapter 3.

It is worth stating the corollary in two more shapes, because downstream files
quote whichever is most ergonomic and it helps to see they are the same fact. The
first packages the impossibility as the nonexistence of any universal system for a
type with a fixed-point-free flip, rather than as a property of a given `f`.

```lean
theorem c1_no_universal_exists {A Y : Type _} (t : Y → Y) (ht : ∀ y, t y ≠ y) :
    ¬ ∃ f : A → A → Y, ∀ g : A → Y, ∃ a, f a = g :=
  fun ⟨f, hf⟩ => match lawvere f hf t with
    | ⟨y, hy⟩ => ht y hy
```

_Proof._ Suppose such an `f` existed. It would be universal, so Theorem 1.4 gives
a fixed point of `t`, contradicting `ht`. ∎

The difference between `no_universal` and `c1_no_universal_exists` is only where
the `f` is quantified: the first refutes a candidate handed to it, the second
denies that any candidate exists. Use whichever the context supplies. Chapter 3's
theorems arrive with a specific verdict system in hand, so they call the first;
existence-style corollaries call the second.

The second extra shape returns the diagonal index itself, not just the fixed
point. This is the form that most downstream proofs actually consume, because they
want to point at the offending behavior, not merely to know one exists.

```lean
theorem c1_lawvere_diagonal {A Y : Type _} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g) (t : Y → Y) : ∃ a, f a a = t (f a a) :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Name the diagonal behavior `a ↦ t (f a a)` by some `a₀`, then evaluate
the naming equation at `a₀`. The result is `f a₀ a₀ = t (f a₀ a₀)`, which says
that the outcome `f a₀ a₀` is moved to itself by `t` only if `t` fixes it, and in
general exhibits the exact index where the diagonal bites. ∎

Compare `c1_lawvere_diagonal` with `lawvere`. They run the same construction; one
returns the fixed value `f a₀ a₀`, the other returns the index `a₀`. When `t` is
fixed-point-free the returned equation `f a₀ a₀ = t (f a₀ a₀)` is a contradiction,
and this is how the classical instances below extract `False`. When `t` has a
fixed point the same equation is instead a self-referential program in the sense
of Kleene. The theorem does not know which case it is in; that is decided entirely
by `t`.

A concrete example makes the two faces vivid. Suppose `Y = Bool` and `t` is the
identity rather than negation. Then for a universal `f` the diagonal produces an
index `a₀` with `f a₀ a₀ = f a₀ a₀`, which is no contradiction at all; it is a
tautology, and `f a₀ a₀` is a legitimate value that "describes its own behavior"
in the harmless sense of agreeing with itself. Now replace `t` by negation and the
same index yields `f a₀ a₀ = not (f a₀ a₀)`, which cannot hold. The construction
did not change. Only the transformation did, and with it the character of the
output flipped from a harmless self-description to an impossible one. This is the
sharp version of the moral that self-reference is not the problem. A universal
system always has fixed points of the transformations that admit them; it is
forbidden only the transformations that admit none. Kleene's recursion theorem is
the systematic exploitation of the first case, building quines and self-optimizing
programs; the impossibility theorems are the systematic exploitation of the
second. They are two readings of one line.

# Three classical instances

We now instantiate Corollary 1.10 three times. Each instance is a choice of `Y`
and a proof that some `t : Y → Y` is fixed-point-free. The instances are Cantor,
Russell, and, in a sharpened form that names the offending index, the liar.

**Example 1.12 (Cantor).** Take `Y = Bool` and `t` the negation `(!·)`. No boolean
equals its own negation, which Lean settles by checking both cases:

```lean
theorem bool_not_fpf : ∀ b : Bool, (!b) ≠ b := by decide
```

By Corollary 1.10, no system with boolean behaviors is universal over its own
behaviors:

```lean
theorem cantor {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  match lawvere f hf (fun b => !b) with
  | ⟨y, hy⟩ => bool_not_fpf y hy
```

The proof is worth reading against the historical Cantor of the first section.
The function `hf` is the assumed surjection onto behaviors; the flip `fun b => !b`
is the transformation; `lawvere` runs the diagonal and returns a boolean `y` with
`(!y) = y`; and `bool_not_fpf` says no such `y` exists. The one line `bool_not_fpf`
carries the entire mathematical content, and it is decided by two-case exhaustion,
which is why Cantor's theorem for booleans needs no axioms beyond computation.

Let us make the identification with the textbook Cantor precise, since it is the
prototype for every reading in the book. A subset `S ⊆ A` is the same data as its
indicator function `χ_S : A → Bool`, where `χ_S a` is `true` exactly when `a ∈ S`.
Under this identification the power set `P(A)` is the function space `A → Bool`,
and a surjection `A → P(A)` is a surjection `A → (A → Bool)`. A surjection of
that type is precisely a universal system `f : A → A → Bool` in the sense of
Definition 1.2: `f a` is the indicator of the subset named by `a`, and
universality says every subset is named. Cantor's set
`D = { a : a ∉ f a }` has indicator `a ↦ not (f a a)`, which is our diagonal
behavior for `t = not`. The index `a₀` that names `D` is Cantor's `a₀`, and the
contradiction `not (f a₀ a₀) = f a₀ a₀` is his "is `a₀ ∈ D`?" answered both ways
at once. So `cantor` above is not an analogue of Cantor's theorem. Up to the
indicator-function dictionary, it is Cantor's theorem, and the dictionary is a
definitional identity, not an approximation.

**Example 1.13 (Russell).** Take `Y` to be propositions and `t` logical negation.
The behavior "the set of indices that do not contain themselves" is the diagonal;
its own membership status is fixed by negation, and negation has no fixed point,
so the behavior is unnamed. This is Russell's paradox, and it is Corollary 1.10
with `t = ¬`. We state it in prose rather than code because the fixed-point-free
step for propositions needs a classical principle, whereas the boolean version
above needs nothing; the distinction will matter when we audit axioms.

The contrast between Examples 1.12 and 1.13 is the first place the book's
axiom-accounting shows up, so it is worth naming. On `Bool`, negation is a
computation and "no `b` has `not b = b`" is decided by trying both values;
`bool_not_fpf` is proved by `decide` and imports nothing. On the type of
propositions, negation is `¬`, and "no proposition `P` has `(¬P) = P`" is not
decidable by exhaustion, because there is no finite set of propositions to try.
Establishing it requires reasoning about `P ↔ ¬P`, which in a constructive setting
you can still refute, but the smooth classical statement "`¬P ≠ P` for all `P`"
leans on treating propositions as a two-valued type, which is a classical
assumption. The engine is the same in both examples. What differs is the cost of
proving the transformation fixed-point-free, and that cost is charged to the
reading, exactly as Remark 1.6 predicted.

**Proposition 1.14 (The liar, named).** Corollary 1.10 refutes universality, but
the diagonal does more: it points at the exact behavior on which the system
breaks. For the boolean flip this witness is the _liar_, an index whose
self-application equals its own negation.

```lean
theorem liar_query {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : ∃ a, f a a = !(f a a) :=
  match hf (fun a => !(f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Name the diagonal behavior `a ↦ !(f a a)` by some `a₀`; evaluating the
naming equation at `a₀` gives `f a₀ a₀ = !(f a₀ a₀)`. ∎

Notice that `liar_query` is `c1_lawvere_diagonal` specialized to `Y = Bool` and
`t = not`, and that it does not conclude `False`. It hands back a live equation,
`f a₀ a₀ = not (f a₀ a₀)`. That equation is the contradiction only after you add
`bool_not_fpf`; on its own it is a description of the pathology, a query the
system answers with the opposite of its own answer. Keeping the query rather than
collapsing to `False` is what lets Chapter 3 talk about the offending input as an
object with meaning: the hallucination boundary, the injected prompt, the query a
truth probe misplaces.

Hold onto this `a₀`. In Chapter 3 it becomes, in turn, the hallucination model's
boundary question, the prompt injection no wrapper can neutralize, and the query
a truth probe cannot place on either side. They are the same index under three
readings.

## What the flip needs: two small facts about `Y`

Corollary 1.10 needs a fixed-point-free endomap of `Y`. Whether one exists is a
property of `Y` alone, independent of any system, and it is the true precondition
for an impossibility. Two boundary cases make the point, and both are one-line
checks in Lean.

The output type `Bool` admits a fixed-point-free flip, so it can host
impossibilities. This is `bool_not_fpf` repackaged as an existence statement about
`Bool`, which is the form the type-level arguments of Chapter 3 quote.

```lean
theorem c1_bool_has_fpf : ∃ t : Bool → Bool, ∀ b, t b ≠ b :=
  ⟨fun b => !b, bool_not_fpf⟩
```

The output type `Unit`, by contrast, admits no fixed-point-free endomap, because
it has only one element and any endomap fixes it.

```lean
theorem c1_unit_has_fixed_point (t : Unit → Unit) : ∃ u : Unit, t u = u :=
  ⟨(), rfl⟩

theorem c1_no_fpf_unit : ¬ ∃ t : Unit → Unit, ∀ u, t u ≠ u :=
  fun ⟨t, ht⟩ => ht () rfl
```

_Proof._ There is only one element `()`, and `t ()` must equal it, so `t` fixes
`()`. A supposed fixed-point-free `t` would then contradict its own promise at
`()`. ∎

The reading is immediate and it is one you should carry into every later chapter.
A system whose only outcome is "accept" cannot be caught by the diagonal, because
"accept" is a fixed point of every transformation. A verifier that can only ever
say yes is trivially consistent about itself; the impossibility needs at least two
distinguishable verdicts and a way to swap them. This is why the safety theorems
are always about systems that can both accept and reject, both assert and deny.
The moment a system's outcome space collapses to one value, the engine has nothing
to grip. Chapter 3 uses this in the other direction: to prove a safety property is
_achievable_ in some regime, it exhibits a collapse of the outcome space, or a
value the relevant flip fixes.

## Manufacturing fixed-point-free flips

Since every impossibility is a fixed-point-free `t`, it pays to know how to build
one, and to know when you cannot. A map `t : Y → Y` is fixed-point-free exactly
when it moves every element, which for a finite `Y` is a familiar object: a
permutation with no fixed point, a derangement, or more generally any endomap
whose graph avoids the diagonal. On two points there is exactly one derangement,
the swap, and it is boolean negation; this is why `Bool` is the smallest interesting
outcome type and why `bool_not_fpf` is a two-case check. On three points the
three-cycle is fixed-point-free, which is the shape of `c1_optFlip` below. On one
point there is no derangement at all, which is `c1_no_fpf_unit`.

The general principle is that a fixed-point-free endomap exists on `Y` precisely
when `Y` admits an endomap avoiding the diagonal, and a clean sufficient condition
is that `Y` carries a free involution or, more weakly, a fixed-point-free
permutation. Two-valued outcome types always do, by the swap. Outcome types that
are contractible in the relevant sense, of which `Unit` is the extreme case, never
do. This is the exact dividing line between outcome spaces that can host an
impossibility and those that cannot, and it is worth stating because Chapter 3
sometimes engineers the outcome space precisely to sit on one side of it. A verdict
system whose outcomes admit a fixed-point-free flip is exposed; one whose outcomes
collapse to a point, or to a set the intended flip fixes, is safe. The design
question "can this be made safe" is often, underneath, the question "can the
outcome flip be given a fixed point," and the answer is read off the geometry of
`Y`.

There is a converse caution. A fixed-point-free `t` on a large `Y` is easy to
write down, but the impossibility it yields is only as strong as the claim that the
system's outcomes really range over all of `Y` and that `t` really is the relevant
transformation. It is tempting to manufacture an exotic `t` and announce an
impossibility; the honest work is always to argue that `t` is forced by the problem,
not chosen for convenience. In Cantor `t` is negation because membership is
two-valued and exclusion is the only nontrivial move. In Chapter 3 the flips are
forced by the meanings of "hallucinate," "inject," and "misclassify," and a large
part of each proof is showing that the natural transformation on that outcome space
has no fixed point.

# A partial-function preview: toward Rice

The instances so far used total behaviors: `f a` is defined on every input. Much
of computability is about _partial_ behaviors, where `f a` may be undefined on
some inputs because a program loops. The diagonal adapts, and the adaptation is
the shape of Rice's theorem, which Chapter 2 proves in full. This section is a
preview, enough to see where the engine reappears.

Model a partial outcome as an element of `Option Y`: the value `some y` means "the
behavior returned `y`," and `none` means "the behavior did not return." A partial
behavior is then a total function `A → Option Y`, and a partial system is
`f : A → A → Option Y`. Universality now asks that every partial behavior be
named. The transformation `t` acts on `Option Y`, and the impossibility follows
whenever `t` is fixed-point-free on `Option Y`.

The subtlety Rice's theorem exploits is that a useful `t` on `Option Y` must
disturb the value `none` as well as the values `some y`. A transformation that
fixed `none`, say by leaving nonreturning behaviors alone, would have a fixed
point at `none` and the argument would stall. So the flip that drives the partial
diagonal is one that moves `none` too: it changes both whether a behavior returns
and, when it does, what it returns. Here is such a flip on `Option Bool`, cycling
the three concrete outcomes so that none is fixed.

```lean
def c1_optFlip : Option Bool → Option Bool
  | none => some true
  | some true => some false
  | some false => none

theorem c1_optFlip_fpf : ∀ o : Option Bool, c1_optFlip o ≠ o := by
  intro o
  cases o with
  | none => decide
  | some b => cases b <;> decide
```

_Proof._ The map sends `none ↦ some true`, `some true ↦ some false`, and
`some false ↦ none`, a three-cycle with no fixed point, checked by exhausting the
three cases. ∎

By Corollary 1.10 applied with `Y` replaced by `Option Bool` and `t = c1_optFlip`,
no partial system `f : A → A → Option Bool` is universal. The reading is the
undecidability of a nontrivial behavioral property. If some machine could name
every partial behavior over `A` and a decision procedure could sort behaviors by
their `Option Bool` value, then the three-cycle would build a behavior that
disagrees with its own classification, which is impossible. Rice's theorem is the
general statement that any nontrivial property of the behavior of programs, one
that holds of some and fails of others, is undecidable, and its proof is this
diagonal with the flip chosen to move across the property's boundary. The details,
including why "nontrivial" is exactly the condition that supplies a fixed-point-free
flip, are Chapter 2. We flag it here only to show that partiality changes the
outcome type and nothing else: the engine is untouched.

Exercise 1.13 asks you to state the partial analogue of Theorem 1.4 carefully and
to identify which classical instance it becomes when `t` is a pure
definedness-flip, one that only toggles `none` against "returns." That flip is the
halting problem; `c1_optFlip` above is a slightly richer flip that also scrambles
the returned value, which is closer to the full Rice statement.

The pure definedness-flip is worth picturing on its own, because it is the cleanest
computational instance. Collapse the returned value and track only whether a
behavior halts, so outcomes are the two-element type "returns" versus "does not,"
and let `t` swap them. A universal partial system over this two-valued outcome is
exactly a decider for halting, and the diagonal behavior `a ↦ swap (halts a on a)`
is Turing's `Dgn`: it halts when its self-application does not and fails to halt
when its self-application does. The fixed-point-free swap forbids the universal
system, which is the statement that no such decider exists. Rice's theorem
generalizes this from "halts" to any nontrivial behavioral property by choosing a
`t` that moves across the property's boundary, and the word _nontrivial_ is doing
precise work: a property that holds of all behaviors, or of none, corresponds to an
outcome value that the natural flip fixes, and then there is no fixed-point-free
`t` and no impossibility. This is the computability face of the same dividing line
drawn in "Manufacturing fixed-point-free flips": trivial properties collapse the
outcome space, nontrivial ones keep it flippable. Chapter 2 makes the
correspondence exact, including the care needed to handle partiality without the
argument accidentally deciding halting for free.

# The engine, named once

We give the schema the name the rest of the notes use.

**Definition 1.15 (Reflective verdict).** A _reflective verdict_ on a domain `Q`
is a universal system `v : Q → Q → Bool`: a boolean self-application in which
every pattern of verdicts over `Q` is itself named by some element of `Q`.

It helps to read the two arguments of `v p q` in the intended application. Think of
`Q` as a space of items a system passes judgment on, say claims, prompts, or
states, and `v p q` as "the verdict that item `p` renders on item `q`." The first
argument is an item playing the role of a judge; the second is the item being
judged. Because both are drawn from `Q`, an item can judge itself, `v p p`, and,
what matters, an item can encode a whole judging policy. Universality is the claim
that every possible policy of verdicts over `Q`, every function `Q → Bool`, is the
policy of some single item. This is a strong closure property, and it is exactly
what the modeling in Chapter 3 sets out to establish for particular systems: that
a faithful, calibrated, covering model can be driven to realize any verdict policy
over the relevant domain, or that an adversary supplying part of a prompt can force
a defense to evaluate any policy it likes. When such a closure holds, the system is
a reflective verdict, and the next theorem applies with no further work.

**Theorem 1.16.** _No reflective verdict exists._

```lean
theorem no_reflective_verdict {Q : Type _} (v : Q → Q → Bool)
    (hv : ∀ g : Q → Bool, ∃ p, v p = g) : False :=
  cantor v hv
```

_Proof._ Immediate from Example 1.12. ∎

**Remark 1.17.** Theorem 1.16 is one line, and it is, verbatim, the Hallucination
Trilemma, the Defense Trilemma, and the truth-boundary coupling theorem of
Chapter 3. Nothing about those results adds to the engine; what changes is only
the intended meaning of `v p q`. The work in Chapter 3 is entirely in the
_reading_, in arguing that faithful-plus-calibrated-plus-covering really does make
a model's verdict reflective, and that prompt injection really does make a
defense's verdict reflective.

It is worth being blunt about what this means for the rest of the book, because a
reader can misjudge where the difficulty lies. The mathematics of the AI-safety
impossibilities is finished. It is the theorem you have just read, proved in one
line from `cantor`. Every remaining page of Chapter 3 is an argument that a
particular real system satisfies the hypothesis `hv`, that its verdicts really are
universal over the relevant domain. Those arguments are not mathematical
subtleties hiding in the diagonal. They are modeling claims about what a faithful,
calibrated, covering model can be prompted to do, or about what an adversary
controlling part of a prompt can force a defense to evaluate. If you doubt a
Chapter 3 theorem, the place to press is never the diagonal. It is always the
claim that `hv` holds.

## The diagonal in a learning system, informally

It is worth walking once through how universality could arise for a learned model,
since the abstraction can make the hypothesis feel unreachable when in fact it is
the natural reading of familiar capabilities. Take `Q` to be a space of prompts,
and imagine a model that answers a prompt with a yes-or-no verdict. Read `v p q`
as the verdict the model gives to prompt `q` when its behavior has been fixed by
prompt `p`, for instance by `p` being a system prompt or an in-context
specification that tells the model which policy to follow. In-context learning is
exactly the claim that a suitable `p` can steer the model to a wide range of
verdict policies over prompts. If the range is _all_ policies `Q → Bool`, the model
is a reflective verdict, and Theorem 1.16 says no such model can be consistent
about the diagonal prompt.

The diagonal prompt writes itself. It is the prompt `q` that asks, in effect, "give
the opposite of the verdict you would give when steered to evaluate this very
prompt." Universality supplies a steering prompt `p₀` that realizes exactly this
policy, and then `v p₀ p₀` must equal its own negation. The model cannot answer
consistently, not because it is badly trained, but because the capability that
made it universal, the ability to be steered to any policy including this one, is
inconsistent with there being a stable answer. This is the honest shape of the
Chapter 3 arguments, before the modeling is made careful. Whether the range really
is all policies is the whole question, and the answer depends on what "faithful,
calibrated, covering" buys you, which is where the real analysis lives.

Two caveats keep this preview honest. First, a real model does not literally range
over all functions `Q → Bool`; it ranges over the policies its architecture and
training make reachable, which is why Chapter 3 argues reachability carefully
rather than assuming it. Second, the diagonal prompt is a construction, not
necessarily a natural-language sentence a user would type; part of the modeling is
arguing that the constructed policy is genuinely within reach of the steering
mechanism. When both caveats are discharged, the impossibility is not a quirk of
phrasing. It is the same wall Cantor hit, standing where a learning system's
generality meets a transformation of its own verdicts that nothing can satisfy.

# What the diagonal cannot give

It is as important to know the limits of an engine as its reach, and half of
this book lives outside this one.

**Remark 1.18.** The diagonal produces a fixed point, or a contradiction, from
self-reference. It is silent on everything quantitative: not how many liars there
are, not how hard `a₀` is to find, not what it costs an adversary to reach one.
And it requires genuine self-application, the hypothesis `∀ g, ∃ a, f a = g`. When
a system cannot name its own behaviors but instead lives on a _connected_ domain
with _continuous_ maps, a different engine takes over, the intermediate value
theorem, and it delivers the same boundary object with metric content the
diagonal never had. That is Chapter 4, and its quantitative refinements, the
geometry of attack basins, are Chapter 5.

It is worth being precise about the three questions the diagonal cannot answer,
because Chapters 4 and 5 exist to answer them and it helps to have them posed
here. The first is _how many_. The theorem produces one index `a₀`, or as many as
there are names for the diagonal behavior, but it gives no measure of how large
the set of liars is, whether it is a single point or a fat region. The second is
_how hard to find_. The proof is nonconstructive about `a₀` in the sense that
matters operationally: it tells you `a₀` exists, but nothing about the cost of
locating it, which is the whole question when the adversary is resource-bounded.
The third is _how stable_. The diagonal's `a₀` is a discrete object with no
neighborhood; there is no sense in which points near `a₀` are nearly-liars,
because "near" is not defined. A connected domain carries a topology, and on it
the boundary object acquires a size, a basin, and a cost, which is why the second
half of the book changes engines. The diagonal is the right tool for "impossible";
the intermediate value theorem is the right tool for "impossible, and here is how
far the impossibility reaches."

There is also a hypothesis the diagonal cannot do without, and naming it guards
against overclaiming. The engine needs genuine universality, the ability to name
_every_ behavior. Real systems frequently fail this, and when they do the theorem
is silent, which is correct: a system that cannot describe itself in full is not
subject to the diagonal, and may well be consistent. The interesting cases, the
ones the book is about, are the systems powerful enough that universality is
plausible. For those, the diagonal is decisive. For the rest, one must argue
universality first, and that argument, not the diagonal, is where the real content
of an impossibility claim lives.

# A roadmap through the book

It is worth saying, once and plainly, how the rest of the notes reuse this
chapter, so that the reader can see the single engine turning under each later
result. Every chapter is one of two things: an instantiation of the diagonal with
a chosen `Y` and `t`, or a change of engine to the intermediate value theorem when
the diagonal's hypothesis is not available.

Chapter 2 revisits the classical instances in their own settings and does the work
this chapter deferred. It builds the arithmetization behind Gödel and Tarski, the
computability behind Turing and Rice, and it presents each as Yanofsky's commuting
square filled in. Nothing there strengthens the engine; the labor is in verifying
universality for arithmetic and for the computable maps, which is exactly the
representability and universal-machine content the history section previewed.

Chapter 3 is the payoff and the reason the book exists. It reads `Q`, `v`, and the
boolean flip three ways, and each reading is a named impossibility. The
Hallucination Trilemma says a model cannot be simultaneously faithful, calibrated,
and covering, because those three properties together make its verdict reflective
and Theorem 1.16 forbids that. The Defense Trilemma says a prompt-injection defense
cannot be simultaneously sound, complete, and closed under composition, for the
same reason applied to a defense's verdict. The truth-boundary coupling theorem
says a truth probe cannot cleanly separate the states it is meant to classify.
Each proof is one line once the reflective-verdict hypothesis is granted, and each
chapter section is an argument that the hypothesis is granted.

Chapter 4 changes engines. When a system does not name its own behaviors but lives
on a connected domain with continuous maps, the diagonal has no grip, and the
intermediate value theorem takes over. It produces the same kind of boundary
object, a place where a continuous verdict must cross a threshold, but now the
object has metric content: a location, a neighborhood, a size. Chapters 5 and 6
make that quantitative, studying the geometry of attack basins and the
approximate bridges that connect the discrete diagonal picture to the continuous
one. Chapter 7 returns to concrete AI-safety settings with both engines in hand,
and Chapter 8 develops J-space, where a system carries both a self-application and
a topology, so that both engines apply at once.

The through-line is that impossibility in these notes is never mysterious. It is
always a fixed-point-free transformation meeting a system rich enough to describe
itself, or a threshold-crossing forced by continuity on a connected domain. If you
hold those two pictures, the diagonal and the boundary, you hold the book.

# Historical and bibliographic notes

The unification is Lawvere's _Diagonal arguments and cartesian closed categories_
(1969), reprinted with an author commentary in _Reprints in Theory and
Applications of Categories_ (2006), which is the most convenient source today.
Lawvere's paper is terse and categorical; readers meeting it for the first time
usually do better to start with a modern exposition and return to the original for
its economy.

Yanofsky's _A universal approach to self-referential paradoxes, incompleteness and
fixed points_ (Bulletin of Symbolic Logic, 2003) is that modern exposition. It
works out Cantor, Russell, Gödel, Tarski, Turing, and the recursion theorem as
instances of one diagram, using only sets and functions, and it is the direct
template for Chapter 2. If you read one background paper, read this one.

For the classical instances in their original settings: Cantor's diagonal appears
in his 1891 note on the uncountability of the reals and the power-set theorem;
Russell's paradox is in his 1902 correspondence with Frege, reproduced in van
Heijenoort's _From Frege to Gödel_ (1967), which remains the standard sourcebook
for this whole lineage. Gödel's incompleteness theorems are in his 1931 paper, and
the diagonal lemma abstracted from it is treated cleanly in any modern logic text;
Boolos, Burgess, and Jeffrey's _Computability and Logic_ is a good one. Tarski's
undefinability of truth is in his 1936 monograph on the concept of truth in
formalized languages. Turing's halting argument is in his 1936 paper on computable
numbers, and Kleene's recursion theorem, the constructive companion, is in his
_Introduction to Metamathematics_ (1952).

The reading of these theorems as constraints on learning systems is recent, and
the specific trilemmata of Chapter 3 are, as far as we know, first stated and
machine-checked in the companion Lean library that these notes track. The
categorical fixed-point tradition after Lawvere, including the fixed-point results
of Lambek and the modal fixed-point theorems descended from Löb, is surveyed in
several places; we do not use it beyond the section form of Theorem 1.8, but a
reader who wants the full categorical picture should look there next.

# Exercises

Exercises marked (Lean) ask for a machine-checked term; the others are on paper.
The starred exercises are harder or open-ended. Several build directly on the
theorems above, whose names are `lawvere`, `no_universal`, `bool_not_fpf`,
`cantor`, `liar_query`, `no_reflective_verdict`, and the `c1_`-prefixed helpers
proved in this chapter.

**Exercise 1.1.** Verify Example 1.3 in detail. For `|A| = n` and `|Y| = 2`,
exhibit a function `A → Y` not of the form `f a`, using a diagonal that flips
`f a a`. Conclude that your construction is exactly `liar_query` specialized to a
finite `A`, and explain in one sentence why the finiteness of `A` played no role
in the diagonal step even though it was essential to the counting step.

**Exercise 1.2 (Lean).** Prove the section form of Theorem 1.8 yourself, from
scratch, without reading `c1_lawvere_section`: given `f : A → A → Y`,
`s : (A → Y) → A`, and `hs : ∀ g, f (s g) = g`, show every `t : Y → Y` has a fixed
point. Then compare your term to `c1_lawvere_section` and to `lawvere`, and say in
one sentence which hypothesis each uses and why the section form needs no `match`.

**Exercise 1.3.** Show the converse of Corollary 1.10 fails: exhibit a `Y` and a
fixed-point-free `t` for which some non-universal `f : A → A → Y` exists. This is
easy; the point is that the theorem is about universality, not about `t` alone.
State precisely what the corollary does and does not claim about `f`.

**Exercise 1.4 (Lean).** A map `t : Y → Y` is _fixed-point-free_ iff it has no
fixed point. Using `c1_bool_has_fpf` and `c1_no_fpf_unit`, explain what the
contrast says about systems whose only outcome is "accept." Then give a
fixed-point-free endomap of a three-element type and prove it fixed-point-free by
`decide`, modeling your proof on `c1_optFlip_fpf`.

**Exercise 1.5.** Restate and prove Cantor's theorem in its usual form, that
there is no surjection `A → Set A`, by taking `Y = Bool` and identifying `Set A`
with `A → Bool`. Point to the exact line of your argument that corresponds to
`bool_not_fpf`, and to the exact subset that corresponds to the diagonal behavior
`a ↦ not (f a a)`.

**Exercise 1.6.** (Gödel, informally.) Suppose a theory `T` proves or refutes
every sentence, and can represent its own provability as a map on sentences. Show
that a self-referential sentence asserting its own unprovability is a
fixed-point-free instance, and identify `Y` and `t`. Which hypothesis of
Corollary 1.10 corresponds to `T` being able to talk about its own proofs, and
which corresponds to `T` deciding every sentence?

**Exercise 1.7.** (Tarski.) Repeat Exercise 1.6 for truth in place of
provability. State the liar sentence as a fixed point of negation, identify `Y`
and `t`, and explain in two sentences why Tarski's conclusion is about
definability while Gödel's is about provability, even though the diagonal step is
identical.

**Exercise 1.8.** (Turing.) Cast the halting argument as an instance of Corollary
1.10. Take the outcomes to record "halts" versus "loops," describe the diagonal
program in words, and name the fixed-point-free `t`. Then explain why the assumed
decider `H`, not the diagonal program, is the object the argument actually
refutes.

**Exercise 1.9.** In `liar_query`, the witness `a₀` depends on the choice of
pre-image. Show that if `f` has two distinct indices naming the diagonal behavior,
both are liars, and that nothing in the argument selects a canonical one. Relate
this to the non-uniqueness of the boundary question in Chapter 4.

**Exercise 1.10 (Lean).** Prove a "one-sided" refinement: if `t : Y → Y` and
`f : A → A → Y` is universal, then there is an index `a₀` with `f a₀ a₀ = t (f a₀ a₀)`,
by calling `c1_lawvere_diagonal`. Then specialize to `Y = Bool`, `t = not`, and
check that you recover `liar_query` up to the shape of the returned equation.

**Exercise 1.11.** Explain, in one paragraph and without symbols, why counting
(Example 1.3) is the wrong intuition for the infinite case, and what the diagonal
provides that counting cannot. Your paragraph should mention that the diagonal
names a specific unnamed behavior, whereas counting only asserts one exists.

**Exercise 1.12.** Give an example of a `Y` and a `t : Y → Y` with _exactly one_
fixed point, and describe what the diagonal produces for a universal
`f : A → A → Y` in that case. Contrast this with the fixed-point-free case, and
connect it to the remark that Kleene's recursion theorem is the same construction
read forwards.

**Exercise 1.13.** (Harder.) Formulate a _partial_ version precisely, building on
the preview above: with outcomes in `Option Y`, define universality as
surjectivity onto partial behaviors `A → Option Y`, state the analogue of Theorem
1.4, and identify which classical instance it becomes when `t` only toggles `none`
against "returns." Explain where the requirement that `t` move `none` enters, and
why a flip fixing `none` would make the argument fail.

**Exercise 1.14 (Lean).** Model a definedness-flip `t : Option Bool → Option Bool`
that swaps `none` with `some false` and fixes `some true`, and decide whether it
is fixed-point-free. If it is not, exhibit its fixed point; if it is, prove it so
by `decide`. Use the answer to explain why Rice's theorem insists the classified
property be _nontrivial_.

**Exercise 1.15.** (Section versus surjection.) Prove on paper that every section
gives point-surjectivity, which is `c1_section_universal`, and explain why the
converse needs a choice principle. Identify the exact step at which choosing one
name per behavior is required, and relate it to the constructive content described
in Remark 1.6.

**Exercise 1.16.** (Reading `Y`.) For each of the following outcome types, decide
whether it admits a fixed-point-free endomap, and hence whether it can host an
impossibility: `Bool`; `Unit`; the two-point type of verdicts "accept/reject";
the type `Option Bool`; a one-point "always accept" verdict space. State the
general principle your answers illustrate.

**Exercise 1.17.** (Starred.) The engine needs `Y` to carry a fixed-point-free endomap.
Chapter 4 replaces this with a continuous map on a connected space whose only
fixed point is a threshold. Speculate on what a system would need to satisfy
_both_ hypotheses at once, a universal self-application and a connected topology,
and what its boundary object would look like. Chapter 8 returns to this for
J-space.

**Exercise 1.18.** (Starred.) Reflect on Remark 1.17's claim that the mathematics of the
AI-safety impossibilities is finished and only the modeling remains. Pick one
informal safety desideratum you care about, phrase it as a universality claim
`hv` for some domain `Q`, and identify the single sentence someone would have to
refute to escape the resulting impossibility. This exercise has no unique answer;
its purpose is to locate where the burden of proof really sits.
