import VersoManual
import TrilemmaBook.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "The Classical Limits" =>

Chapter 1 built one theorem and one corollary. The theorem, {lean}`lawvere`, says
that a universal system has a fixed point for every transformation of its
outcomes. The corollary, {lean}`no_universal`, reads that backwards: if some
transformation `t : Y → Y` has no fixed point, then no system `f : A → A → Y` can
be universal. Everything in the present chapter is an application of the
corollary. We change what `A` names, we change what `Y` measures, we pick a
fixed-point-free `t`, and out falls a theorem that someone proved between 1874
and 1953 by what looked at the time like a different argument each time.

The claim that these are one argument is not a slogan. It is a factoring. Each
classical proof has a self-referential heart and a local wrapper. The heart is
always the diagonal behavior `a ↦ t (f a a)` and the observation that a name for
it collides with itself. The wrapper is the work of arguing that the system in
question really is universal in the sense {lean}`no_universal` requires: that a
set really does surject onto its power set, that a theory really can represent its
own provability, that a programming language really is closed under the
constructions the proof performs. Lawvere isolated the heart. This chapter walks
through the wrappers, one theorem at a time, and shows that once the wrapper is in
place the heart is a single reusable line of Lean.

There is a reason to care about the unification beyond elegance. When results are
proved by what look like unrelated tricks, each new domain seems to need its own
genius, and the safety of a new kind of system looks like an open empirical
question. When they are proved by one move, a new domain needs only the checklist
of the recipe, and the question becomes sharply mathematical: does this system have
a section into its own function space, and does its outcome object carry a
fixed-point-free map. The unification converts a menagerie of clever arguments into
a decision procedure for spotting impossibilities, and that is what lets the later
chapters treat hallucination and prompt injection as instances to be verified
rather than as new mysteries to be cracked.

The order is roughly historical, and it is also an order of increasing subtlety
in the wrapper. Cantor's power-set surjection is the cleanest instance and we
prove it in full. Russell's paradox drops even the power set and works directly
with membership. Gödel's two incompleteness theorems ask the most of the wrapper,
because representing provability inside arithmetic is real work, and we are honest
about which parts live in prose and which parts compile. Tarski, Turing, and Rice
then follow quickly, because by that point the wrapper is familiar and only the
reading changes.

Two conventions carry over from Chapter 1. A system is a curried map
`f : A → A → Y`, and universality is point-surjectivity, `∀ g : A → Y, ∃ a, f a = g`.
Live `lean` code blocks are core Lean 4 and are elaborated when the book is built.
New results proved here are prefixed `c2_` so their names are globally unique.
Where a theorem needs the machinery of Mathlib or a classical axiom, we state it
in prose and name the verified statement in the companion libraries rather than
write fragile code.

# The recipe

Before the instances, it helps to name the procedure they share, because after
the first two everything is variation.

**The recipe.** To obtain a limitative theorem from {lean}`no_universal`:

1. Choose the _index type_ `A`: what the system's names range over. Sets,
   sentences, programs, subsets, and prompts have all played this role.
2. Choose the _outcome type_ `Y`: what a behavior reports. For most classical
   results `Y = Bool`, a yes or no.
3. Exhibit a _fixed-point-free_ `t : Y → Y`, a map with `t y ≠ y` for all `y`.
   For `Y = Bool` this is boolean negation, and Chapter 1's {lean}`bool_not_fpf`
   is the proof that it has no fixed point.
4. Argue the _wrapper_: that the system under study, if it existed with the
   properties claimed, would be universal in the sense
   `∀ g : A → Y, ∃ a, f a = g`.
5. Conclude by {lean}`no_universal` that no such system exists, or by
   {lean}`liar_query` that a specific self-undermining index exists.

Steps 1 through 3 are cheap. Step 4 is where the mathematics lives, and it is the
only step that differs across the classical theorems. Step 5 is one line.

For `Y = Bool` the whole recipe collapses to a single reusable statement. Since
negation is fixed-point free, no boolean system is universal, full stop.

```lean
theorem c2_no_universal_bool {A : Type _} (f : A → A → Bool) :
    ¬ (∀ g : A → Bool, ∃ a, f a = g) :=
  no_universal (fun b => !b) bool_not_fpf f
```

_Proof._ Apply {lean}`no_universal` with `t` the boolean flip `(!·)` and
`ht := bool_not_fpf`. ∎

Read {lean}`c2_no_universal_bool` slowly, because it is the entire chapter in one
line. It says: for _any_ way `f` of assigning to each index `a` a yes-or-no
behavior `f a` over indices, there is some yes-or-no pattern `g : A → Bool` that no
index realizes. The pattern is always the same one, the diagonal flip
`fun a => !(f a a)`, and the theorem does not care whether `A` is finite or a
proper class, whether `f` is computable or a black box, whether the yes and no
mean membership or provability or halting. Cantor, Russell, Gödel, Tarski,
Turing, and the boolean core of Rice are all this statement wearing different
clothes. The rest of the chapter is a fashion show.

**Remark 2.1 (Why `Bool` and not `Prop`).** We insist on `Y = Bool` in the code,
not `Y = Prop`, and the choice is deliberate. On `Bool` the fixed-point-free
witness `bool_not_fpf` is settled by `decide`, checking the two cases, and it
needs no axioms at all. On `Prop` the corresponding statement, that `¬ P ≠ P` for
every proposition `P`, is a form of the law of noncontradiction that is fine
constructively for the negation, but reading a `Prop`-valued system as universal
forces classical principles the moment one wants to case-split on an arbitrary
`P`. We will meet exactly this fork in Russell's paradox below. Keeping the engine
on `Bool` means every compiled proof in this chapter is axiom-free, which we can
check with `#print axioms`, and it is a small model of a discipline the AI-safety
chapters take seriously: a two-valued verdict is a decision, and a decision is
where impossibility bites.

## A finite rehearsal

It is worth running the recipe once on a finite example, where you can see every
piece, before turning it loose on the infinite theorems where the same pieces do
the same work invisibly. Chapter 1's Example 1.3 counted: a set with `n` elements
has `n` behaviors but `2ⁿ` boolean patterns, so universality fails by arithmetic.
The diagonal gives the same conclusion without counting, and the difference
matters, because counting is exactly what stops working when the sets are
infinite.

Take `A` with two elements, call them `0` and `1`, and let `f : A → A → Bool` be
any system. There are four behaviors `A → Bool` in total and only two names, so
some behavior is unnamed, and the recipe tells you which one. Form the diagonal
flip `d = fun a => !(f a a)`. Concretely `d 0 = !(f 0 0)` and `d 1 = !(f 1 1)`.
Now check that `d` is not `f 0`: they differ at `0`, because `d 0 = !(f 0 0)`
disagrees with `f 0 0`. And `d` is not `f 1`: they differ at `1`, because
`d 1 = !(f 1 1)` disagrees with `f 1 1`. So `d` is unnamed, and it was constructed
by a single negation from the diagonal `a ↦ f a a`, with no reference to the size
of `A`.

That last clause is the whole point. The counting proof knew `4 > 2`. The diagonal
proof never counted; it built one specific unnamed behavior by disagreeing with
each `f a` at the one input `a` where disagreement is cheap, its own name. Replace
two by any cardinal, finite or infinite, and the construction is unchanged and the
conclusion is unchanged, while the counting argument has nothing to say once `2ⁿ`
and `n` are both infinite. This is why every theorem in the chapter is a diagonal
and not a count. The systems they concern, sets and their subsets, theories and
their sentences, languages and their programs, are all infinite, and the only
argument that survives is the one that ignores size.

# Cantor's theorem

Cantor proved in 1891 that a set has strictly more subsets than elements, in the
precise sense that no function from a set onto its power set can be a surjection.
This is the theorem that started the subject. It is also the cleanest possible
instance of the recipe, because the power set _is_ the function space `A → Bool`
and a surjection onto it _is_ universality, with nothing to translate.

Identify a subset `S ⊆ A` with its indicator function `A → Bool`, the map sending
`a` to `true` when `a ∈ S` and to `false` otherwise. This identification is a
bijection between the power set of `A` and the type `A → Bool`. Under it, a
function `f : A → (A → Bool)` is the same data as a family of subsets indexed by
`A`, and `f` being surjective onto `A → Bool` is the same as saying every subset
occurs in the family.

**Definition 2.2 (Power-set surjection).** A _power-set surjection_ on `A` is a
function `f : A → (A → Bool)` such that every indicator `g : A → Bool` equals `f a`
for some `a`, that is, `∀ g : A → Bool, ∃ a, f a = g`.

Since `A → (A → Bool)` and `A → A → Bool` are the same type by currying, a
power-set surjection is exactly a universal boolean system. There is no gap to
close. Cantor's theorem is therefore an immediate corollary of the recipe.

**Theorem 2.3 (Cantor, 1891).** _No power-set surjection exists._

```lean
theorem c2_cantor_powerset {A : Type _} (f : A → (A → Bool))
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  cantor f hf
```

_Proof._ A power-set surjection is a universal boolean system, so Chapter 1's
{lean}`cantor` applies directly. Unfolding that proof: universality names the
diagonal subset `d = fun a => !(f a a)`, the set of `a` that the `a`-th subset
excludes. Let `a₀` name it, so `f a₀ = d`. Ask whether `a₀ ∈ f a₀`. Evaluating
the naming equation at `a₀` gives `f a₀ a₀ = !(f a₀ a₀)`, which no boolean
satisfies. ∎

The witness `d` is Cantor's _diagonal set_: it disagrees with the `a`-th listed
subset about the element `a`. It cannot appear anywhere in the listing, because to
appear at position `a₀` it would have to agree with itself about `a₀` and disagree
with itself about `a₀` at the same time. This is the same `a₀` that Chapter 1's
{lean}`liar_query` produces, read now as membership rather than as a truth value.

**Identifying `Y` and `t`.** Here `Y = Bool`, the two answers to "is `a` in this
subset," and `t` is negation, "put `a` in exactly when the diagonal leaves it
out." The fixed-point-free character of negation is the whole obstruction. If some
outcome were fixed by `t`, the diagonal set could sit quietly at that outcome and
the surjection would survive.

**Discussion of the hypothesis.** The single hypothesis is surjectivity, and it is
worth seeing that nothing weaker will do and nothing stronger is needed. Injective
maps `A → (A → Bool)` exist in abundance; the theorem forbids only the covering
property. The map need not be computable, definable, or continuous. It is a raw
function, and the diagonal set is built from it by one negation, so the argument
survives any amount of pathology in `f`. This robustness is exactly why the
diagonal is the wrong tool for quantitative questions, a point Chapter 1 flagged
and Chapters 5 and 6 develop: the argument works so generally precisely because it
ignores metric structure.

**The classical set form.** In the language of pure set theory the theorem reads:
there is no surjection `A → Set A`. The companion library proves this directly, as
`CCH.cantor_no_surjection_set` in `CCHProofs/CCH_03_Cantor.lean`, by the Russell
diagonal `{x | x ∉ f x}` rather than through `Bool`, and it proves the
boolean-indicator form as `CCH.cantor_no_surjection`. The two are the same theorem;
the `Set`-level proof needs the classical fact that membership in a set is
decidable enough to case-split, while the `Bool` form we compile here needs
nothing. We return to why in the discussion of Russell.

**The diagonal set is not a paradox.** Beginners often read the diagonal set `d`
as paradoxical, on the model of Russell's set, and it is worth being clear that it
is not. There is nothing self-contradictory about the set of `a` such that
`a ∉ f a`. It is a perfectly ordinary subset of `A`; you can list its members
whenever you can compute `f`. The only thing the theorem says about it is that it
is not one of the sets `f a`, that it fails to be listed by the particular family
`f`. Cantor's theorem is a statement about the family, not about the diagonal set,
and it is negative in a mild way: some subset was left out. The paradox appears
only in Russell, where the family is forced by comprehension to include every
subset, so that the diagonal set must be both listed and, by construction, unlisted.
The difference between a theorem and a paradox is exactly the difference between a
family that may omit a subset and a family that may not.

**Fixed points and retractions.** Lawvere stated his theorem in the contrapositive
form that Cantor's theorem exemplifies most cleanly, and it is illuminating to
read Cantor that way. Say a type `Y` has the _fixed-point property_ if every
`t : Y → Y` has a fixed point. Lawvere's theorem says that if `A` admits a
point-surjection onto `A → Y`, then `Y` has the fixed-point property. Cantor's
theorem is the contrapositive with `Y = Bool`: since `Bool` fails the fixed-point
property, witnessed by {lean}`bool_not_fpf`, no `A` point-surjects onto `A → Bool`.
Read forward, the same theorem is a tool for _building_ fixed points, and that is
how the lambda calculus uses it, a point Exercise 2.16 develops. Read backward, it
is an impossibility. The engine does not know which way you are reading it; the
sign of the conclusion is entirely in whether your `Y` has a fixed-point-free map.

**Counting was never the point.** The finite rehearsal above already made this
concrete, and Cantor's own history confirms it. The 1874 proof that the reals are
uncountable did not diagonalize; it used nested intervals and the completeness of
the reals, an analytic argument. The 1891 diagonal was the second proof, and its
power was that it generalized instantly from the reals to any set and its power
set, because it never used a special property of the reals, only the ability to
flip a value. The book's later chapters run the two styles in the other order: the
diagonal comes first, in Chapters 1 and 2, and the analytic argument, the
intermediate value theorem, comes second, in Chapters 4 through 6, recovering with
metric content what the diagonal gets for free but without measure.

**The tower of infinities.** Cantor's theorem does not fire once; it iterates. The
power set of `A` is strictly larger than `A`, and the power set of that is larger
still, and the process never closes, so there is no largest set and no set of all
sets, on pain of the paradox Russell found. This is the cumulative hierarchy that
`ZFC` builds level by level, and its infinite cardinalities, the beth numbers, are
each a diagonal step above the last. The theorem also leaves a famous question open
that it cannot itself answer: whether any cardinality sits strictly between a set
and its power set. That is the continuum hypothesis, and Cohen's forcing showed it
is independent of `ZFC`, which is a second-incompleteness-flavored fact one level
up, the axioms cannot decide a question their own diagonal raised. The diagonal
opens the tower; it does not tell you how the rungs are spaced. The recurring
distinction between what the diagonal establishes and what it leaves open is
already present in the oldest instance.

**Cantor and Schröder–Bernstein.** One more contrast sharpens what the theorem
does. The Schröder–Bernstein theorem says that if there are injections both ways
between two sets, they have the same cardinality, and its proof is a back-and-forth
that builds a bijection. Cantor's theorem builds nothing. It exhibits an
obstruction, the unnamed diagonal subset, and stops. The two together pin down
cardinal arithmetic: Schröder–Bernstein makes the order on cardinals antisymmetric,
Cantor makes it strict at every power-set step. It is the second kind of theorem,
the obstruction rather than the construction, that this book is about, and the
diagonal is the universal source of obstructions. When a safety result says "no
system can do this," it is Cantor-shaped, and its proof exhibits the behavior no
system names rather than construct the system that fails.

**Remark 2.4 (Cantor and reflective verdicts).** Chapter 1 packaged the boolean
diagonal as {lean}`no_reflective_verdict`, the statement that no verdict system can
name every pattern of its own verdicts. Cantor's theorem is that statement's
oldest instance: the "verdicts" are membership decisions, and the "patterns" are
subsets. When Chapter 3 argues that a hallucination-free model would be a
reflective verdict on its own outputs, and Chapter 7 argues the same for a
prompt-injection defense, they are asking those systems to be power-set
surjections onto their own behavior. Cantor already answered. The engineering
intuition worth carrying forward is that a model's set of possible behaviors is its
power set, and asking the model to certify every behavior of its own kind is asking
for the surjection Cantor forbids, no matter how large the model.

# Russell's paradox

Russell wrote to Frege in 1902 with a two-line argument that unrestricted
comprehension is inconsistent. Comprehension is the principle that any predicate
carves out a set: for every property `P` there is a set `{x | P x}` whose members
are exactly the `x` with `P x`. Russell applied it to the property "is not a
member of itself." Let `R = {x | x ∉ x}`. Then `R ∈ R` if and only if `R ∉ R`,
and the theory is dead.

The relation to Cantor is close and instructive. Cantor's theorem needs a
codomain, the power set, and a claimed surjection onto it. Russell's paradox drops
the codomain entirely. It works with a single binary relation, membership, and
asks it to be universal in a way that turns out to be the same diagonal collision.
Historically Russell found his paradox by pushing on Cantor's proof: if the
universe of all sets existed, the identity would surject it onto its own power set,
which Cantor forbids, and unwinding that forbidden surjection produces `R`.

To fit the recipe, model an unrestricted membership relation as a boolean system.
Let `A` be a would-be universe of sets, and let `mem : A → A → Bool` report
membership, so `mem a b` is `true` when `b` is a member of `a`. Unrestricted
comprehension says every property of elements is the membership condition of some
set: for every `g : A → Bool` there is a set `a` with `mem a = g`. That is
point-surjectivity of `mem`.

**Definition 2.5 (Naive membership).** A _naive membership relation_ on `A` is a
map `mem : A → A → Bool` satisfying comprehension, `∀ g : A → Bool, ∃ a, mem a = g`:
every boolean condition on `A` is realized as the membership condition of some
element.

**Theorem 2.6 (Russell, 1902).** _If `mem` is a naive membership relation, then
there is a set `r` that is a member of itself exactly when it is not, that is,
`mem r r = !(mem r r)`. No such relation exists._

```lean
theorem c2_russell {A : Type _} (mem : A → A → Bool)
    (hmem : ∀ g : A → Bool, ∃ a, mem a = g) : ∃ r, mem r r = !(mem r r) :=
  liar_query mem hmem
```

_Proof._ This is Chapter 1's {lean}`liar_query` verbatim, with `f` renamed `mem`.
Comprehension applied to the property `fun a => !(mem a a)`, "is not a member of
itself," names a set `r` with `mem r = fun a => !(mem a a)`. Evaluate at `r`:
`mem r r = !(mem r r)`. The Russell set is the diagonal behavior; the theorem is
that it names itself into contradiction. To turn the existence of `r` into an
outright `False`, feed it to {lean}`bool_not_fpf`, or use {lean}`cantor` on `mem`
directly. ∎

**Identifying `Y` and `t`.** Again `Y = Bool` and `t` is negation. The Russell set
`R = {x | x ∉ x}` is nothing but the diagonal behavior `a ↦ t (mem a a)`, the same
object that in Cantor was the diagonal subset and that in Chapter 1 was the liar.
Three names, one construction.

**Discussion of the hypothesis.** The hypothesis is comprehension, and the paradox
is what forced set theory to give it up. The modern repairs restrict which
predicates form sets. Zermelo's separation only lets a predicate carve a subset
out of a set you already have, so `{x ∈ A | x ∉ x}` is legal but is merely a subset
of `A`, not a universe, and the diagonal argument then reproves Cantor rather than
exploding. The type-theoretic repair, which is the one Lean itself uses, stratifies
by universe level so that `mem a a` is not even well-formed: a set cannot be
applied to itself because the levels do not line up. In Lean the naive relation
`mem : A → A → Bool` is perfectly well-typed, which is why {lean}`c2_russell`
compiles, but its hypothesis `hmem` is never satisfiable for a nontrivial `A`, and
that unsatisfiability is the content. The theorem is a proof that the hypothesis is
empty.

**Remark 2.7 (`Bool` versus `Prop`, again).** The propositional Russell paradox,
`R ∈ R ↔ R ∉ R`, lives naturally in `Prop`, where the flip is logical negation.
There the fixed-point-free step is `¬ (P ↔ ¬ P)`, which holds without any axioms.
We nonetheless compile the `Bool` version, because the `Bool` flip composes with
the rest of the diagonal engine using only `congrFun` and `decide`, whereas
threading `Prop`-valued behaviors through {lean}`lawvere` invites classical
case-splits later. This is the same fork flagged in Remark 2.1. The lesson for the
safety chapters: whenever a "safe or unsafe" judgment is genuinely two-valued, the
impossibility is constructive and needs no appeal to excluded middle, and that
matters when the judgment is supposed to be something a machine actually computes.

**The paradox that reshaped a subject.** Russell's two lines did more damage than
any theorem in this chapter, because they arrived while the foundations were being
poured. Frege's "Grundgesetze der Arithmetik" derived arithmetic from logic using
Basic Law V, which is comprehension in the guise of an axiom about the extensions
of concepts, and Russell's paradox is a direct refutation of Basic Law V. Frege
received the letter as the second volume was in press and added an appendix that
begins by admitting the foundation of his life's work had been shaken. The paradox
is not a technicality at the margin of set theory; it is the reason set theory has
axioms at all rather than a single comprehension schema.

**The repairs, and what each gives up.** Three responses survived. Zermelo's
separation, kept in `ZFC`, allows a predicate to carve a subset only out of a set
already given, so `{x ∈ A | x ∉ x}` exists but is merely a subset of `A`; running
the diagonal on it reproves Cantor, that `A` does not contain all its subsets,
rather than exploding. The axiom of foundation then bans `x ∈ x` outright, so the
Russell condition `x ∉ x` holds of everything and defines nothing new. Russell's
own repair, the ramified theory of types, stratifies objects into levels and
declares `x ∈ x` ill-formed, which is the ancestor of the universe hierarchy Lean
enforces on `Type`. Quine's New Foundations keeps a single universe but restricts
comprehension to _stratified_ formulas, those that could be typed, which blocks the
Russell predicate while allowing a universal set to exist. Each repair pays the
same currency: it gives up the unrestricted freedom to turn a predicate into a set,
and it pays exactly enough to make the diagonal behavior `fun a => !(mem a a)`
fail to be a set. The paradox is a lower bound on what any consistent set theory
must forbid.

**A family of paradoxes.** Russell's is one of a cluster that all run the same
diagonal against a would-be universal object. Cantor's paradox is the diagonal
against the set of all sets: if it existed, the identity would surject it onto its
power set, which Theorem 2.3 forbids. The Burali-Forti paradox is the diagonal
against the set of all ordinals, which would be an ordinal greater than every
ordinal including itself. Each is {lean}`c2_russell` with a different reading of
`mem`, and each was, historically, a separate shock. Seeing them as one instance is
the dividend of the Lawvere factoring, and it is the same dividend the safety
chapters collect when hallucination and injection turn out to be one theorem.

# Gödel's first incompleteness theorem

Gödel's 1931 theorem is where the wrapper earns its keep. Cantor and Russell hand
you universality almost for free, because a power set or a comprehension schema is
a surjection by fiat. Arithmetic does not. To run the diagonal against a formal
theory of arithmetic, one must first show that the theory can talk about its own
syntax, and that is a substantial piece of number theory. Once it is done, the
incompleteness theorem is again the diagonal, applied to provability instead of to
membership.

We separate the argument into the part that is genuinely the diagonal, which we
compile, and the arithmetization, which we describe and cite. This is the honest
division of labor. The self-reference is finite and mechanical and belongs in the
kernel. The arithmetization is a long verification that Lean's Mathlib and the
model-theory literature carry out, and reproducing it in a live block would be
fragile and beside the point.

## Representability as point-surjectivity

Fix a formal theory `T` in the language of arithmetic, consistent and strong
enough to represent primitive recursive functions; the standard choice is
Robinson's `Q` or Peano arithmetic `PA`. Gödel numbering assigns to each formula a
natural number, its code, written `⌜φ⌝`. Let `A` be the set of codes of formulas
with one free variable. Each such formula `φ(x)` defines, by substitution, a map
from numbers to sentences and hence, once we fix an interpretation of truth or
provability, a boolean-valued behavior on `A`.

**Definition 2.8 (Representability).** A predicate `g` on codes is _representable_
in `T` when there is a formula `φ` such that, for every code `n`, `T` proves
`φ(n)` when `g n` holds and `T` proves `¬ φ(n)` when `g n` fails. The central
arithmetical fact, due to Gödel, is that every _recursive_ predicate on codes is
representable in `Q`.

Representability is the wrapper's version of surjectivity. Read `f a b` as "the
formula coded by `a`, applied to the code `b`, is provable in `T`." Then a
predicate `g : A → Bool` being representable says there is a formula, some code
`a`, whose provability behavior `f a` matches `g`. Over the recursive predicates,
representability is exactly the point-surjectivity hypothesis
`∀ g, ∃ a, f a = g` of {lean}`lawvere`, restricted to the recursive `g`. That
restriction is the one honest difference from Cantor: the surjection is onto the
representable behaviors, not onto all of `A → Bool`. It is enough, because the
diagonal behavior we build is itself recursive.

## Arithmetizing syntax

The wrapper's real labor is showing that arithmetic can talk about arithmetic, and
it is worth sketching why this is possible at all, because the possibility is not
obvious and the safety analogues turn on the same trick. The language of arithmetic
speaks of numbers, not of formulas or proofs. Gödel's device is to encode each
syntactic object as a number, so that a statement about formulas becomes, after
translation, a statement about numbers, which arithmetic can then make.

Assign to each symbol a number, to each formula the number obtained by
prime-factorization coding of its symbol sequence, `2^(s₀) · 3^(s₁) · 5^(s₂) · …`,
and to each proof, a sequence of formulas, a code of its sequence of codes. Under
this coding, "is a well-formed formula," "is an axiom," "follows from earlier lines
by a rule," and finally "is a proof of the formula with code `n`" all become
arithmetical predicates on the codes. The one delicate step is coding finite
sequences of unbounded length inside a language whose variables range over single
numbers, and Gödel solved it with his beta function, which uses the Chinese
remainder theorem to pack an arbitrary finite sequence into a pair of numbers. With
sequences codable, primitive recursion is expressible, and every primitive
recursive predicate, including "`p` codes a proof of the formula coded by `n`,"
becomes representable in `Q`.

The provability predicate `Prov(n)` is then "there exists `p` such that `p` codes a
proof of `n`," an existential quantifier over the primitive recursive proof-checking
predicate. This one unbounded quantifier is why `Prov` is `Σ₁`, recursively
enumerable but not in general recursive, and that asymmetry is the seam the whole
incompleteness argument runs along. A theory can correctly confirm its actual
proofs, the positive facts, but it cannot in general refute the false ones, because
refuting "there is a proof" needs a universal quantifier the predicate does not
carry. Hold onto this asymmetry; it is exactly what distinguishes Gödel's `Prov`
from Tarski's `True` in the section after next, and it is the logical form of the
gap between a system confirming its safe behaviors and certifying the absence of
unsafe ones.

## The diagonal lemma

The heart of Gödel's proof is a fixed-point construction on sentences. It says
that for any property of sentences the theory can express, there is a sentence
asserting that it itself has that property. This is Lawvere's theorem in the
syntactic category, and it is the one piece we can state cleanly in core Lean as an
abstract fact about universal systems.

**Lemma 2.9 (Diagonal lemma, abstract form).** _Let `f : A → A → Y` be a universal
system and `t : Y → Y` any transformation of outcomes. Then some index `a`
satisfies `f a a = t (f a a)`: the diagonal behavior at `a` is a fixed point of
`t` applied through the system._

```lean
theorem c2_diagonal_lemma {A Y : Type _} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g) (t : Y → Y) :
    ∃ a, f a a = t (f a a) :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Universality names the diagonal behavior `fun a => t (f a a)` by some
`a₀`, so `f a₀ = fun a => t (f a a)`. Evaluate at `a₀`, which is what `congrFun`
does, to get `f a₀ a₀ = t (f a₀ a₀)`. ∎

This is the same three lines as {lean}`lawvere`, reorganized to expose the index
`a₀` rather than the fixed value. In the arithmetical reading, `A` is codes of
one-variable formulas, `f a b` is provability of the diagonalization, and `t` is
the boolean operation the target property performs on a truth value. Lemma 2.9
then says: for the property built from `t`, there is a self-referential sentence
`G`, coded by `a₀`, for which `T` proves `G ↔ t`-of-its-own-status. The genuine
Gödel diagonal lemma, which produces an honest arithmetic sentence rather than an
abstract index, is the arithmetization of exactly this step, and it is a theorem
of `Q`. It is developed in the model-theory literature and formalized in Mathlib's
first-order logic library; we state it and cite it rather than reproduce it,
because the arithmetization is orthogonal to the self-reference the lemma
captures.

## The provability predicate and the Gödel sentence

Let `Prov(x)` be the arithmetized provability predicate: `Prov(⌜φ⌝)` says, inside
`T`, that `φ` has a proof in `T`. This predicate is representable because
provability is recursively enumerable, and building it is the longest part of the
proof. Apply the diagonal lemma with the property "not provable." It yields a
sentence `G` such that

`T ⊢ G ↔ ¬ Prov(⌜G⌝)`,

a sentence that says, correctly, "I am not provable in `T`."

**Theorem 2.10 (Gödel's first incompleteness theorem, 1931).** _Let `T` be a
consistent, recursively axiomatized theory that represents the recursive
predicates. Then there is a sentence `G` such that `T` proves neither `G` nor
`¬ G`. If `T` is also sound, `G` is true._

_Proof (structure)._ Suppose `T ⊢ G`. Then there is a proof, so `T ⊢ Prov(⌜G⌝)`
by the fact that `Prov` correctly reports actual proofs. But `T ⊢ G ↔ ¬ Prov(⌜G⌝)`,
so `T ⊢ ¬ Prov(⌜G⌝)`, and `T` proves both `Prov(⌜G⌝)` and its negation,
contradicting consistency. Suppose instead `T ⊢ ¬ G`. Then
`T ⊢ Prov(⌜G⌝)` by the fixed-point equivalence. Under the stronger assumption of
omega-consistency, or under the Rosser trick which removes that assumption,
`Prov(⌜G⌝)` together with the absence of an actual proof again yields a
contradiction. So `T` decides neither `G` nor `¬ G`. If `T` is sound then `G`,
being unprovable, is exactly what it says it is, and is true. ∎

The self-referential collision at the center is Lemma 2.9. If a consistent `T`
_could_ decide every sentence, its provability behavior would be a total,
correct, boolean system over its own sentences, and applying the diagonal with
`t` = negation would produce a sentence equal to its own negation, which is
impossible. We can state that collapse as a compiled fact, reading `f a a` as the
settled truth value the complete-and-sound theory assigns to the self-referential
sentence coded by `a`.

```lean
theorem c2_godel_semantic {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  match c2_diagonal_lemma f hf (fun b => !b) with
  | ⟨a₀, ha₀⟩ => bool_not_fpf (f a₀ a₀) ha₀.symm
```

_Proof._ Lemma 2.9 with `t` the flip gives `a₀` with `f a₀ a₀ = !(f a₀ a₀)`, and
{lean}`bool_not_fpf` refutes it. ∎

**What {lean}`c2_godel_semantic` does and does not say.** It says that a boolean
system that is _universal_ over its own indices is contradictory. In the
arithmetical reading, universality is the conjunction of representability with
completeness: representability gives the surjection onto recursive behaviors, and
completeness is the extra promise that the theory assigns a definite provable truth
value to every self-referential sentence, so that the diagonal behavior lands back
in the represented family. The compiled theorem is therefore the _semantic_ core:
no consistent theory is both representationally rich and complete. What it does not
capture, and what the prose proof of Theorem 2.10 supplies, is the syntactic
bookkeeping that turns "not complete" into an explicit undecided sentence `G` you
can write down, and the care about omega-consistency versus the Rosser
construction. That bookkeeping is real and is why the full theorem is not a
one-liner. The one-liner is the reason the bookkeeping was worth doing.

**Discussion of the hypotheses.** Three hypotheses carry the theorem, and each
maps onto the recipe. Consistency is what makes the fixed-point collision fatal
rather than merely odd; an inconsistent theory proves everything and has no trouble
proving `G`, so the flip has, in effect, a fixed point because every value is
provable. Recursive axiomatizability is what makes `Prov` representable, and hence
what makes the diagonal behavior land in the surjection's range; drop it and a
theory can be complete, as the full first-order theory of the standard model is,
at the price of not being recursively listable. Representational strength is
point-surjectivity itself. Weaken any one and the wrapper fails, and with it the
theorem. This is the same sensitivity we saw in Cantor, where surjectivity was
load-bearing, made arithmetical.

**Omega-consistency and the Rosser refinement.** Gödel's original argument needed
slightly more than plain consistency to rule out `T ⊢ ¬ G`. He assumed
omega-consistency, which forbids the theory from proving `∃ x, φ(x)` while also
proving `¬ φ(0)`, `¬ φ(1)`, and so on for every numeral, a pathology a consistent
but unsound theory can exhibit. Rosser removed the extra assumption in 1936 by a
clever change of sentence. Instead of "I am not provable," Rosser's sentence says
"for every proof of me, there is a shorter proof of my negation." This is still a
fixed point of a syntactic operation, so it is still Lemma 2.9 in arithmetized
form, but the operation now compares proof lengths, and the comparison makes plain
consistency enough to block both `T ⊢ R` and `T ⊢ ¬ R`. The upgrade costs nothing
in the abstract engine; it is entirely a refinement of the wrapper, choosing a
diagonal behavior whose fixed point is fatal under a weaker hypothesis. That the
same impossibility admits a sharper wrapper is a pattern the safety chapters
repeat, where a first trilemma under strong assumptions is later reproved under
weaker, more realistic ones.

**The epistemic sting.** Part of what makes Gödel's theorem feel paradoxical, when
it is not, is a confusion of levels that the recipe dissolves. The sentence `G` is
unprovable in `T`, and, if `T` is sound, true. So we, reasoning in the metatheory,
know `G` is true, while `T` cannot prove it. There is no contradiction: our
knowledge uses the soundness of `T`, a fact about `T` that lives outside `T` and
that `T` cannot establish about itself, by the second theorem below. The diagonal
does not produce a sentence that is true and false, or provable and unprovable. It
produces a sentence whose truth outruns one particular system's reach, and it
locates that sentence precisely. Every "the AI knows it is lying but says it anyway"
intuition in the safety literature is a version of this level confusion, and
untangling it always comes down to naming which system is doing the knowing.

**Concrete unprovable truths.** The Gödel sentence is often dismissed as
artificial, a sentence built only to be unprovable, and for decades that dismissal
had some force. It no longer does. There are now natural mathematical statements,
about ordinary combinatorial objects, that are true but unprovable in `PA`.
Goodstein's theorem, about sequences of numbers that appear to grow without bound
but in fact always reach zero, is true in the standard model and independent of
`PA`, provable only by transfinite induction up to `ε₀`. The Paris–Harrington
theorem, a strengthened finite Ramsey statement, is another. These are not liar
sentences; they are the kind of statement a combinatorialist might pose without any
thought of logic, and `PA` cannot prove them. The lesson for the safety reading is
that the incompleteness boundary is not confined to self-referential curiosities.
It cuts through the natural questions too, which means a system's inability to
certify a property of itself is not a corner case one can engineer around by
avoiding self-reference. The unprovable can look completely ordinary.

**Remark 2.11 (The safety reading).** Gödel's theorem is the template for every
result in the second half of these notes that has the shape "a system powerful
enough to model itself cannot also certify itself." A model asked to output a
calibrated confidence in its own future outputs, a verifier asked to verify
verifiers including itself, an overseer asked to audit systems as capable as it
is: each is a `Prov`-like predicate turned on its own domain, and each meets the
diagonal. Chapter 3 makes the hallucination version precise, and Chapter 7 the
oversight version. The recurring engineering temptation is to believe that more
capability closes the gap. Gödel says more capability, in the form of stronger
representation, only sharpens the diagonal.

# Gödel's second incompleteness theorem

The first theorem produces an undecided sentence. The second identifies a
particular one: the theory's own consistency. It is the deeper result for the
philosophy of mathematics and the more delicate to prove, because it depends not
just on having a provability predicate but on that predicate behaving well.

Formalize consistency as the sentence `Con(T) := ¬ Prov(⌜0 = 1⌝)`, which says that
`T` does not prove an outright falsehood. The second theorem says a consistent `T`
that can talk about its own proofs cannot prove `Con(T)`.

**Theorem 2.12 (Gödel's second incompleteness theorem, 1931).** _Let `T` be a
consistent, recursively axiomatized theory extending a modest base of arithmetic,
whose provability predicate satisfies the Hilbert–Bernays–Löb derivability
conditions. Then `T` does not prove `Con(T)`._

The derivability conditions are the promises that make `Prov` behave like a real
notion of proof inside `T`:

1. If `T ⊢ φ` then `T ⊢ Prov(⌜φ⌝)`. Actual proofs are internally recognized.
2. `T ⊢ Prov(⌜φ → ψ⌝) → (Prov(⌜φ⌝) → Prov(⌜ψ⌝))`. Internal proof respects modus
   ponens.
3. `T ⊢ Prov(⌜φ⌝) → Prov(⌜Prov(⌜φ⌝)⌝)`. The theory can internally verify its own
   recognitions.

_Proof (structure)._ From the fixed-point equivalence `T ⊢ G ↔ ¬ Prov(⌜G⌝)` and
the derivability conditions, one shows `T ⊢ Con(T) → G`: internal consistency would
let the theory carry out, about itself, the first theorem's argument that `G` is
unprovable, which is what `G` asserts. But the first theorem says `T ⊬ G`. If `T`
proved `Con(T)`, it would prove `G`, a contradiction. So `T ⊬ Con(T)`. ∎

## The second theorem, machine-checked

The sketch above is the textbook one, and it is the part of Gödel's second
theorem that can be checked here. What cannot be checked here is the
arithmetization: that a particular theory such as `PA` really does admit a
provability predicate satisfying the three conditions, and really does admit the
fixed point. That is a large formalization in its own right, and this
development does not carry it out. What follows is therefore the theorem
relative to those inputs, which is exactly how the derivability-conditions
presentation states it.

Package a proof system as a structure. The sentences are an arbitrary type, `imp`
and `bot` are the object-language connectives, `box` is the provability predicate
`Prov`, and `Thm` is the judgement `T ⊢ ·`. Beyond the three derivability
conditions we assume only modus ponens and the two axiom schemes `K` and `S` of
the implicational fragment, which are the standard Hilbert-system apparatus and
which say nothing about provability.

```lean
structure c2_PC where
  S : Type
  Thm : S → Prop
  imp : S → S → S
  box : S → S
  bot : S
  mp : ∀ {a b}, Thm (imp a b) → Thm a → Thm b
  ax_K : ∀ a b, Thm (imp a (imp b a))
  ax_S : ∀ a b c,
    Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  D1 : ∀ {a}, Thm a → Thm (box a)
  D2 : ∀ a b, Thm (imp (box (imp a b)) (imp (box a) (box b)))
  D3 : ∀ a, Thm (imp (box a) (box (box a)))
```

Two derived rules of the implicational fragment, obtained from `K`, `S`, and
modus ponens alone. They are the only propositional reasoning the argument needs.

```lean
theorem c2_s_comb (P : c2_PC) {a b c : P.S}
    (h₁ : P.Thm (P.imp a (P.imp b c))) (h₂ : P.Thm (P.imp a b)) :
    P.Thm (P.imp a c) :=
  P.mp (P.mp (P.ax_S a b c) h₁) h₂

theorem c2_syll (P : c2_PC) {a b c : P.S}
    (h₁ : P.Thm (P.imp a b)) (h₂ : P.Thm (P.imp b c)) :
    P.Thm (P.imp a c) :=
  c2_s_comb P (P.mp (P.ax_K (P.imp b c) a) h₂) h₁
```

Now Löb's theorem. The hypotheses `fix₁` and `fix₂` are the two directions of the
diagonal lemma's fixed point `g ↔ (Prov(g) → A)`, supplied rather than
constructed, since constructing it is the arithmetization we are not doing.

**Theorem 2.12a (Löb, 1955).** _If `T ⊢ Prov(A) → A`, then `T ⊢ A`._

```lean
theorem c2_loeb (P : c2_PC) {A g : P.S}
    (fix₁ : P.Thm (P.imp g (P.imp (P.box g) A)))
    (fix₂ : P.Thm (P.imp (P.imp (P.box g) A) g))
    (h : P.Thm (P.imp (P.box A) A)) :
    P.Thm A :=
  let s3 := P.mp (P.D2 g (P.imp (P.box g) A)) (P.D1 fix₁)
  let s5 := c2_syll P s3 (P.D2 (P.box g) A)
  let s7 := c2_s_comb P s5 (P.D3 g)
  let s8 := c2_syll P s7 h
  P.mp s8 (P.D1 (P.mp fix₂ s8))
```

_Proof._ Necessitate the fixed point and push the box inward with `D2`, giving
`Prov(g) → Prov(Prov(g) → A)`. A second application of `D2` turns that into
`Prov(g) → (Prov(Prov(g)) → Prov(A))`, and `D3` contracts the two boxes to yield
`Prov(g) → Prov(A)`. Composing with the hypothesis gives `Prov(g) → A`, which is
the right-hand side of the fixed point, so `g` itself is a theorem; necessitating
`g` and applying modus ponens delivers `A`. ∎

Consistency is the sentence saying that falsity is not provable, and Gödel's
second theorem is Löb's theorem at `A := ⊥`.

```lean
def c2_Con (P : c2_PC) : P.S := P.imp (P.box P.bot) P.bot

theorem c2_godel_second (P : c2_PC) {g : P.S}
    (fix₁ : P.Thm (P.imp g (P.imp (P.box g) P.bot)))
    (fix₂ : P.Thm (P.imp (P.imp (P.box g) P.bot) g))
    (hcon : P.Thm (c2_Con P)) :
    P.Thm P.bot :=
  c2_loeb P fix₁ fix₂ hcon
```

_Proof._ `Con` unfolds to `Prov(⊥) → ⊥`, which is the hypothesis of Löb's theorem
with `A := ⊥`. So a theory proving its own consistency proves `⊥`. ∎

Read {lean}`c2_godel_second` contrapositively and it is the statement of Theorem
2.12: a theory that does not prove `⊥`, that is, a consistent one, does not prove
`Con(T)`.

One check is worth doing before trusting any of this, because a theorem whose
hypotheses cannot be met is true for empty reasons. The axiom set is satisfiable:

```lean
def c2_pc_trivial : c2_PC where
  S := Unit
  Thm := fun _ => True
  imp := fun _ _ => ()
  box := fun _ => ()
  bot := ()
  mp := fun _ _ => trivial
  ax_K := fun _ _ => trivial
  ax_S := fun _ _ _ => trivial
  D1 := fun _ => trivial
  D2 := fun _ _ => trivial
  D3 := fun _ => trivial
```

This witness is deliberately degenerate: it proves everything, including `⊥`, so
it is an inconsistent theory. It establishes only that {lean}`c2_PC` is
inhabited, so the theorems above are not vacuous. It does not establish that a
consistent theory meets the conditions, and the reader should not read it as
doing so. That claim is the arithmetization, and it remains the one thing in this
chapter taken from the literature rather than checked here.

There is a cleaner route through Löb's theorem, which is the fixed-point argument
made self-standing. Löb's theorem (1955) says `T ⊢ Prov(⌜φ⌝) → φ` implies
`T ⊢ φ`: a theory can only internally trust the provability of what it already
proves. Löb's theorem is itself a diagonal argument, the fixed point of the map
`ψ ↦ (Prov(⌜ψ⌝) → φ)`, and the second incompleteness theorem is the case `φ = 0=1`,
because `Con(T)` is exactly `Prov(⌜0=1⌝) → 0=1` waiting for Löb to refuse it. So the
second theorem, like the first, is one more fixed point, taken now in the modal
algebra of the provability predicate. The modal logic that axiomatizes this
algebra, `GL` for Gödel–Löb, has Löb's theorem as its defining axiom, and its
arithmetical completeness (Solovay, 1976) is the precise statement that provability
reasoning _is_ this fixed-point logic and nothing more.

**Why this one stays in prose.** Every step above is a theorem, and the whole is
formalized in the literature, but the derivability conditions are statements about
a specific arithmetized `Prov`, and verifying them is the arithmetization we
deferred in the first theorem, now with the added burden of the third condition,
which is the internal formalization of the first. There is no faithful two-line
core-Lean rendering, because the content is precisely the syntactic behavior of a
particular predicate, not the abstract diagonal. What the abstract diagonal does
capture, Löb's fixed point, we have already compiled once as Lemma 2.9: the map
whose fixed point Löb takes is a `t : Y → Y` in disguise, and the existence of the
fixed point is {lean}`c2_diagonal_lemma`. The arithmetical soundness of that fixed
point is the cited part.

**Remark 2.13 (Self-certification is the second theorem).** The second theorem is
the sharpest classical statement of a limit that recurs throughout AI safety: a
system cannot vouch for its own soundness from within. "This model will not deceive
you" is a `Con`-like sentence about the model, and a model strong enough to state
it and satisfying the internal-coherence analogues of the derivability conditions
cannot prove it without already being unsound. Chapter 7 returns to this when it
argues that a deployed system's own assurances about its alignment carry no
evidential weight beyond what an external, more powerful check provides, and that
the external check then faces its own second theorem one level up.

**Provability as a modal logic.** The cleanest modern packaging of both
incompleteness theorems is the modal logic `GL`, where a box operator reads as "is
provable in `T`." The derivability conditions become the modal axioms: condition 1
is the necessitation rule, condition 2 is the distribution axiom `K`, and condition
3 is the axiom `4`, that the box iterates. Löb's theorem becomes the single axiom
`GL`, which says box-of-(box-`p`-implies-`p`) implies box-`p`. The Kripke frames
that validate `GL` are exactly the transitive, converse-well-founded ones, frames
with no infinite ascending chains, and converse well-foundedness is the modal
shadow of consistency: a chain of ever-stronger provability claims must terminate.
Solovay's completeness theorem of 1976 makes this exact. His first theorem says
`GL` proves precisely the modal principles that hold for `T`'s provability
predicate under every arithmetical interpretation, so provability reasoning is
`GL` and nothing more. His second characterizes the principles that are always
true, as opposed to always provable, and the two differ by exactly the reflection
principle the second incompleteness theorem denies. The upshot worth carrying: the
logic of a system reasoning about its own proofs is completely understood, it is
finite and decidable, and it has Löb's fixed point built in as an axiom. Self-
reference at this level is not mysterious; it is a small modal logic.

**Consistency strength.** The second theorem also organizes the landscape of
theories into a linear hierarchy by consistency strength. Because `T` cannot prove
its own consistency, a theory that does prove `Con(T)` is strictly stronger, and
this relation, "proves the consistency of," well-orders the natural theories from
weak arithmetic up through set theory with large cardinals. Each step up is a
concrete instance of the second theorem: the stronger theory sees a consistency
fact the weaker one is blind to, and is itself blind to its own. Ordinal analysis
measures these steps with ordinals, assigning to `PA` the ordinal `ε₀`, the height
of the induction it can prove well-founded. The picture to keep is a ladder no rung
of which can see its own footing, which is the exact shape Chapter 7 gives to a
tower of overseers, each able to certify those below and none able to certify
itself.

# Tarski's undefinability of truth

Tarski proved in 1936 that a sufficiently expressive language cannot define its own
truth predicate. Where Gödel constrained provability, which is recursively
enumerable and internally expressible, Tarski constrained truth, which is not even
that. The result is in one sense stronger and in another simpler: stronger because
undefinability is a flat impossibility with no undecided-sentence subtlety, simpler
because there is no need for derivability conditions, only for the diagonal.

A truth predicate for a language `L` is a formula `True(x)` such that for every
sentence `φ`,

`True(⌜φ⌝) ↔ φ`,

which is Tarski's material adequacy condition, his schema T. It says the predicate
gets every sentence right. Tarski's theorem is that no formula of `L` itself can do
this for all sentences of `L`.

**Definition 2.14 (Definable truth predicate).** A language interpreting arithmetic
has a _definable truth predicate_ when some formula `True(x)` satisfies schema T for
every sentence of the language.

Model the situation as a boolean system. Let `A` be codes of sentences, and let a
candidate truth predicate be a way of assigning, to each code, a boolean verdict,
uniformly across all the boolean patterns the language can express. Material
adequacy plus definability makes the verdict system universal over its own
sentences: every boolean condition the language can state, including the negation
of the predicate composed with the diagonal, is itself the verdict pattern of some
sentence. That is point-surjectivity, and it is exactly the hypothesis of Chapter
1's {lean}`no_reflective_verdict`.

**Theorem 2.15 (Tarski, 1936).** _No language that can represent its own syntax and
interpret arithmetic has a definable truth predicate._

```lean
theorem c2_tarski {A : Type _} (True? : A → A → Bool)
    (hT : ∀ g : A → Bool, ∃ a, True? a = g) : False :=
  no_reflective_verdict True? hT
```

_Proof._ A definable, materially adequate truth predicate makes `True?` a
reflective verdict, universal over the boolean patterns on sentences. Chapter 1's
{lean}`no_reflective_verdict` says none exists. Unfolding, the diagonal builds the
liar sentence `L` with `True?(⌜L⌝) ↔ ¬ True?(⌜L⌝)`, and material adequacy turns
that into `L ↔ ¬ L`. ∎

**Identifying `Y` and `t`.** `Y = Bool`, the truth value, and `t` is negation. The
witness is the liar, "this sentence is false," which is {lean}`liar_query` read as
a sentence rather than as a set or a program. The liar is not a curiosity at the
edge of the theory. It is the exact obstruction, the diagonal behavior that a truth
predicate would have to name and cannot.

**Tarski versus Gödel.** The two theorems are close and the difference is precise.
Gödel's `Prov` _is_ definable, because provability is recursively enumerable, and
the price of that definability is incompleteness: the predicate exists but the
theory cannot decide the sentence it produces. Tarski's `True` would have to be
definable to run the same diagonal, and the conclusion is that it simply is not
definable at all, because if it were, the liar would be an outright contradiction
rather than a merely undecided sentence. Provability is a shadow of truth that the
system can cast; truth itself the system cannot hold. The gap between them, the
sentences that are true but not provable, is the room the first incompleteness
theorem lives in. One clean way to see the whole picture: if truth were definable
it would be a complete, sound provability predicate, and {lean}`c2_godel_semantic`
already showed that is contradictory.

## The hierarchy of metalanguages

Tarski's theorem is a ban on defining truth _for a language within that same
language_, and Tarski paired the ban with a positive construction that respects it.
Truth for a language `L` is definable, just not in `L`; it is definable in a richer
metalanguage `L'` that has the resources to quantify over the sentences of `L` and
assert the schema T for each. Truth for `L'` then needs a still richer `L''`, and
so on up an unbounded hierarchy of languages, each defining truth for the one
below and none defining its own. This is the same ladder as the consistency-strength
hierarchy, and it is not a coincidence: both are the second-theorem shape, a tower
in which each level certifies the level beneath and no level certifies itself.

There are ways to buy a single language its own truth predicate, and each pays a
price the recipe predicts. Kripke's 1975 theory of truth allows the truth predicate
to be _partial_, undefined on the ungrounded sentences like the liar, and builds it
as the least fixed point of a monotone operator that adds sentences to the extension
and anti-extension as they become settled. The liar never settles, so `True` is
simply undefined there, and the material adequacy schema holds only for grounded
sentences. This dodges Tarski's theorem by refusing to be total, which is exactly
the move that separates the halting problem from Rice's theorem: allow the deciding
object to withhold judgment and the flat impossibility relaxes into a statement
about where judgment must be withheld. The revision theory of Gupta and Belnap
instead lets the predicate's extension be revised transfinitely, with the liar
oscillating forever rather than settling, and reads truth as the stable pattern of
that revision. Both are honest responses to Tarski, and both trade totality or
bivalence for definability. A truth predicate cannot be total, exact, bivalent, and
self-applicable at once, and you may keep any three.

**Remark 2.16 (Truth probes and Chapter 8).** Tarski's theorem is the reason the
AI-safety literature on "truthfulness" has to be careful about what it can promise.
A truth predicate that is total, exact, and expressible in the same system whose
outputs it judges is exactly the object Tarski forbids. Chapter 8 studies probes
that read a model's internal state to estimate whether the model "believes" its
own output, and the standing objection to such probes is Tarskian: a probe
definable within the model, applied to the model's own truth, meets the liar. The
resolution there is not to defeat the theorem but to change the domain, moving from
outputs to activations and from a two-valued verdict to a continuous score on a
connected space, where a different engine, the intermediate value theorem, takes
over. That the boundary object survives the change of engine is the point of the
final chapter.

# Turing and the halting problem

Turing's 1936 theorem predates the modern statement of Rice's and is its special
case, but historically and pedagogically it comes first. It says no program can
decide, for arbitrary programs and inputs, whether they halt. Read through the
recipe, the halting decider is a candidate boolean predicate `D` on programs, and
the diagonal builds a program that halts exactly when `D` predicts it will not.

Let `A` be the type of programs, and let programs also serve as inputs, since a
program is a string and a string can be fed to a program. Suppose the programming
language is universal in the sense that every boolean behavior over programs is
itself computed by some program, which is the closure of the language under the
constructions the argument needs. A halting decider is any `D : A → Bool`, total by
assumption, claiming to report whether the diagonal computation `f a a` halts.

**Definition 2.17 (Halting decider).** A _halting decider_ for a universal system
`f : A → A → Bool` is a total map `D : A → Bool` intended to satisfy `D a = f a a`
for all `a`, where `f a a` records the halting behavior of program `a` on its own
code.

**Theorem 2.18 (Turing, 1936).** _For every universal system `f : A → A → Bool` and
every candidate decider `D : A → Bool`, there is a program `a` on which the decider
is wrong: `f a a ≠ D a`. No total halting decider is correct._

```lean
theorem c2_turing_halting {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) (D : A → Bool) :
    ∃ a, f a a ≠ D a :=
  match hf (fun a => !(D a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, fun h => bool_not_fpf (D a₀) ((congrFun ha₀ a₀).symm.trans h)⟩
```

_Proof._ Universality names the contrarian behavior `fun a => !(D a)`, "do the
opposite of what `D` predicts," by some program `a₀`, so `f a₀ = fun a => !(D a)`.
Evaluate at `a₀`: `f a₀ a₀ = !(D a₀)`. If the decider were right there,
`f a₀ a₀ = D a₀`, we would get `!(D a₀) = D a₀`, refuted by {lean}`bool_not_fpf`.
So `a₀` is a program the decider misjudges. ∎

The contrarian program `a₀` is the classical construction: build a machine that
runs `D` on its own code and then loops if `D` says halt, halts if `D` says loop.
It cannot behave consistently with `D`'s prediction, so `D` is wrong about it. This
is the same `a₀` as everywhere else in the chapter, now reading `Y = Bool` as
"halts or runs forever" and `t` as the flip "do the opposite."

**The partiality subtlety.** The clean statement above hides the one place halting
differs from Cantor. A real halting decider must be _total_, returning an answer on
every program, while the programs it judges are _partial_, sometimes running
forever. The contrarian program is built to be partial in exactly the way that
breaks a total decider: where `D` says "halts," it loops, which a total `D` cannot
itself do while remaining total and correct. If deciders were allowed to be partial,
returning no answer sometimes, the theorem would not follow in this form, and the
correct statement becomes Rice's, about the impossibility of _total_ decision of a
nontrivial _semantic_ property. We take that step next. Chapter 1's Exercise 1.8
flagged this as the shape of Rice's theorem, and it is.

**The universal machine is the wrapper.** The hypothesis that the language is
universal, `∀ g, ∃ a, f a = g`, is not free; it is the existence of a universal
Turing machine, a single program that simulates any program given its code. Turing
built one, and that construction is the wrapper for this theorem exactly as
Gödel numbering was the wrapper for incompleteness. Without a universal machine
there is no closure under diagonalization, and the halting problem for a
non-universal model of computation can be perfectly decidable; the halting problem
for finite automata, for instance, is trivial. Undecidability is a property of
systems rich enough to host their own interpreter, which is the computational form
of "expressive enough to describe its own behavior" from Chapter 1. The safety
reading writes itself: a model general enough to simulate arbitrary reasoning,
including reasoning about itself, has bought the very universality that makes its
behavior undecidable.

**Where halting sits.** The halting problem is not merely undecidable; it is the
canonical undecidable problem, complete for the recursively enumerable sets under
many-one reduction. Every other undecidability in this chapter reduces to it or
sits above it in the arithmetical hierarchy, the classification of problems by the
number of quantifier alternations needed to define them. Halting is `Σ₁`, one
existential quantifier over a decidable matrix, "there exists a halting
computation," the same `Σ₁` shape as Gödel's `Prov`, and this is no accident: `Prov`
is halting for a proof search. Totality, "this program halts on every input," is
`Π₂`, strictly harder, and the hierarchy continues upward without collapsing. The
diagonal produces the first rung, and reductions climb the rest. Quantitatively,
even the first rung is wild: the busy-beaver function, the longest a halting
`n`-state machine runs, grows faster than any computable function, so
uncomputability is not a thin boundary phenomenon but a dominant one. The diagonal
tells you the boundary exists; it does not tell you it is this violent. That gap
between qualitative and quantitative is the book's recurring theme.

**Remark 2.19 (Runtime verification).** Turing's theorem is the ancestor of every
impossibility in program analysis, and its safety reading is direct: no static
analyzer decides, for all programs, a behavioral question as simple as termination.
For AI systems the behavioral questions are far harder than halting, whether a
model will ever produce disallowed content, whether an agent will ever take an
unsafe action, and the halting problem is the floor. If termination is undecidable,
"never does anything unsafe over an unbounded interaction" is not going to be
decidable by a general procedure either. The safety chapters do not lean on Turing
directly, because they want quantitative statements the diagonal cannot give, but
Turing is the qualitative backstop that says the quantitative work is necessary.

# Rice's theorem

Rice's theorem (1953) is the culmination of the computability instances. It says
that _every_ nontrivial semantic property of programs is undecidable, not just
halting. A property is _semantic_ when it depends only on the function a program
computes, not on the program's text, and _nontrivial_ when some programs have it
and some do not. Rice's theorem sweeps the entire class in one argument: if you can
name a behavioral property that some but not all programs have, no total procedure
decides it.

The reduction to the diagonal has two layers. The boolean core is again the
contrarian construction, identical to Turing's, and we compile it. The full
statement, quantified over all nontrivial properties and over the partial recursive
functions, needs the machinery of an acceptable programming system and is proved in
the companion library; we compile the core and cite the rest.

## The boolean core

**Definition 2.20 (Semantic decider).** For a universal system `f : A → A → Bool`, a
_semantic decider_ is a total map `D : A → Bool` claiming to compute the diagonal
behavior `f a a` from the index `a` alone. Rice's theorem denies that any such `D`
is correct everywhere.

**Theorem 2.21 (Rice, diagonal core).** _For every universal `f : A → A → Bool` and
every `D : A → Bool`, some index `a` has `f a a ≠ D a`._

```lean
theorem c2_rice_diagonal {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) (D : A → Bool) :
    ∃ a, f a a ≠ D a :=
  c2_turing_halting f hf D
```

_Proof._ This is {lean}`c2_turing_halting` under a change of reading. The
contrarian behavior `fun a => !(D a)` is named by some `a₀`, and the decider is
wrong there. ∎

That the proof of Rice's core is literally the proof of Turing's theorem is the
whole thesis of the chapter, made unusually blunt. Turing decides one property,
halting; Rice decides any property; the diagonal does not notice the difference,
because it only ever sees a boolean `D` and flips it. The content that distinguishes
Rice from Turing is entirely in the wrapper: showing that an arbitrary nontrivial
semantic property gives rise to a `D` the diagonal can attack.

## Nontrivial properties and partial functions

The classical Rice's theorem is stated for properties `P` of the partial function a
program computes. Let `P` be a set of partial recursive functions that is neither
empty nor everything, a nontrivial property. Rice's theorem says the set of
programs whose function lies in `P` is undecidable.

**Theorem 2.22 (Rice, full form).** _Let `P` be a nontrivial semantic property of
partial recursive functions. Then the set `{e | φ_e ∈ P}` of program indices with
that property is not recursive._

_Proof (structure)._ Nontriviality gives a program `a` with the property and a
program `b` without it, or vice versa; without loss the everywhere-undefined
program lacks `P`. Given a claimed decider for `P`, reduce the halting problem to it:
build, from any program and input, a program that behaves like `a` if the input
halts and like the empty program otherwise, so that it has `P` exactly when the
input halts. A decider for `P` would then decide halting, which Theorem 2.18
forbids. The reduction is the wrapper; the impossibility it reduces to is the
diagonal. ∎

This full form needs an acceptable numbering of the partial recursive functions,
with the `s-m-n` theorem to perform the construction uniformly, and a
case-analysis on which side of `P` the empty function falls on. It uses classical
logic and the recursion-theoretic apparatus of Mathlib. The companion development
formalizes the diagonal core and the AI-safety corollaries in
`Foundation/F_02_RiceTheorem.lean`: `Foundation.rice_diagonal` is Theorem 2.21 in
mismatch form, `Foundation.rice_general` is the property version for a nontrivial
`P : Bool → Bool`, and `Foundation.no_automated_self_test` is the reading we care
about, that no automated tester predicts a universal system's behavior on its own
description. We reproduce the core here and cite those for the full statement, in
keeping with the discipline of the book: the self-reference compiles, the
recursion theory is cited.

**Identifying `Y` and `t`.** As always for the computability instances, `Y = Bool`
and `t` is negation. What is new in Rice is the universal quantifier over
properties, and the recipe absorbs it: each nontrivial property yields, through the
reduction, a boolean `D`, and the single fixed-point-free `t` defeats them all at
once. One `t`, every property.

**Discussion of the hypothesis.** Nontriviality is the load-bearing word, and it is
the analogue of surjectivity being nondegenerate. A trivial property, one that all
programs have or none do, is decided by a constant function, and there is no
contradiction because the constant decider is never wrong. The diagonal needs two
distinct outcomes to flip between, which is why `t` must be fixed-point free and why
`Y` must have at least two elements. A property with only one truth value across all
programs gives a `t` with a fixed point, and the engine stalls, correctly, because
the theorem is false for trivial properties. This is the computability shadow of
Chapter 1's Exercise 1.4, that `Unit` admits no fixed-point-free endomap.

## Rice–Shapiro and the shape of the undecidable

Rice's theorem says every nontrivial semantic property is undecidable, and it is
natural to ask how badly. The Rice–Shapiro theorem answers for the properties that
are merely recursively enumerable rather than recursive. It says a semantic
property `P` has an r.e. index set only if `P` is determined by finite information:
a function has the property exactly when some finite subfunction of it already
does, and every extension of such a finite piece keeps the property. Properties
that violate this, "the function is total," "the function computes a constant,"
have index sets that are not even r.e., and they sit at `Π₂` or higher in the
hierarchy. So Rice sorts semantic properties into a spectrum. The trivial ones are
decidable. The finitely-determined ones are r.e. but undecidable. The rest are
worse, unrecognizable even in the limit. The bare diagonal only distinguishes
trivial from nontrivial; the finer sorting needs the reductions and the hierarchy,
which is once more the pattern that the diagonal gives the first, coarse boundary
and further structure needs further tools.

This finer picture is the one the safety chapters actually need, because it says
where the line between checkable and uncheckable falls. A behavioral property that
depends only on finitely much observed behavior can at least be recognized when it
appears, even if its absence can never be confirmed, which is the logical form of
"you can catch a model doing something bad but cannot certify it never will." A
property that depends on the whole infinite behavior cannot even be recognized.
Rice–Shapiro is the classical statement that monitoring is possible and
certification is not, and Chapter 7 gives it teeth by adding the cost of the finite
observation and the rate at which confidence can accrue.

**Remark 2.23 (No automated semantic testing).** Rice's theorem is the direct
ancestor of the book's core negative results about evaluating models. A "semantic
property of a model" is a property of the function the model computes, whether it is
honest, whether it is aligned, whether it is safe, and Rice says no general
automated test decides such a property for universal systems. `no_automated_self_test`
in the companion library is exactly this, and Chapter 3 upgrades it from
"undecidable" to a quantitative trilemma by adding structure the bare property
lacks. The pattern to remember: Rice closes the door on deciding behavioral
properties by inspection, and the analytic chapters reopen it a crack by asking not
for a decision but for a calibrated estimate on a connected space, where being
approximately right is possible even though being exactly right is not.

The practical shadow of Rice falls across the whole enterprise of model evaluation.
A benchmark is an attempt to decide a semantic property of a model by running it on
finitely many inputs, and Rice is the reason a benchmark can never certify the
property in general, only sample it. This is not a defect of current benchmarks that
a better one would fix; it is the theorem. What a benchmark can honestly claim is
finite and statistical, "on this distribution, at this rate, the property held," and
the gap between that and "the property holds" is precisely the gap Rice guarantees
is unbridgeable by any finite test. The constructive response, and the one the
safety chapters develop, is to stop asking for certification and start asking for
bounds: not "is this model safe," which Rice forbids deciding, but "with what
probability, over what distribution, at what adversarial cost, does it fail," which
measure and geometry can answer. The impossibility is real, and it is also a
signpost pointing at the questions that do have answers.

# The categorical unification

The claim that these are one theorem has a precise home, and it is worth stating,
because it is what makes "the same argument" a mathematical fact rather than a
family resemblance. Lawvere's 1969 setting is a cartesian closed category, an
abstract universe of "spaces" and "maps" in which one can form products `A × B` and
exponentials `Y^A`, the object of maps from `A` to `Y`. The category of sets is the
example to keep in mind, with `Y^A` the function set `A → Y`, but the theorem holds
in every cartesian closed category, and that generality is the unification.

In this setting a system is a map `f : A → Y^A`, an `A`-indexed family of maps
`A → Y`. Point-surjectivity, which is what we have used, weakens in the categorical
version to _point-surjectivity_ in the internal sense, but the cleanest hypothesis
is a _section_: a map `s : Y^A → A` with `f ∘ s = id`, so that every map `A → Y` is
named on the nose. Lawvere's theorem is then that any `t : Y → Y` has a fixed point,
where a fixed point is a global element `y : 1 → Y` with `t ∘ y = y`. The proof is
the same diagonal, drawn now as a commuting diagram: precompose `f` with the
diagonal `A → A × A`, transpose, apply `t`, and use the section to find the
self-referential point. Chapter 1's Exercise 1.2 asked you to prove exactly the
section form in Lean, and it is three lines there because the set-theoretic
exponential makes transposition invisible.

Why does the abstract version make the unification literal? Because each classical
theorem is Lawvere's theorem in a _particular_ cartesian closed category, not merely
an argument shaped like it. Cantor is the category of sets with `Y = 2`. The
recursive version behind Turing and Rice is a category of assemblies or a realizability
topos, where maps are tracked by programs and `Y^A` is the object of computable
behaviors, so that the section is a universal machine. The provability version behind
Gödel lives in a category built from a theory's own Lindenbaum algebra, where maps
are provable-equivalence classes of formulas. In each category the objects and maps
are different mathematics, and in each the single diagram commutes and yields the
single conclusion. The wrappers of this chapter are, in this light, the
constructions of the categories, and the engine is the one diagram that every
cartesian closed category satisfies.

We do not compile the categorical version, because doing it honestly needs a library
of category theory and the payoff is conceptual rather than computational. The
set-level {lean}`lawvere` is the shadow the categorical theorem casts on the category
of sets, and it is the shadow every result in this book actually uses. The value of
knowing the source of the shadow is that it tells you when a new impossibility is
going to be an instance: whenever the system in question is a map into an internal
function space with a section and an outcome object carrying a fixed-point-free map,
you already have the theorem, and only the reading remains.

# Interlude: the wrapper is the mathematics

A reader who has come this far might draw the wrong lesson, that these theorems are
easy because the engine is three lines. The opposite is closer to the truth. The
engine is three lines precisely because a century of work moved all the difficulty
into the wrappers, and the wrappers are hard. Coding syntax into arithmetic,
building a universal machine, constructing an acceptable numbering with the `s-m-n`
property, establishing the derivability conditions: each is a substantial theorem,
and each is what a graduate course on these subjects actually spends its time
proving. The diagonal is the punchline, and punchlines are short.

This division has a practical consequence for the rest of the book, and it is why
the chapter dwelt on the wrappers rather than the engine. To prove a new
impossibility in the safety domain, you never re-prove the diagonal. You do the work
of the wrapper: you argue that a model with such-and-such capabilities really is
universal over the relevant behaviors, that a defense really does have to answer
every injection including the ones about itself, that a probe really is asked to be
a total exact predicate on the states whose truth it reports. When that argument
succeeds, the impossibility is immediate, and when it fails, the failure is exactly
the escape hatch, the property a real system has that a universal one does not. The
skill the book is trying to teach is not the diagonal, which you now have. It is
recognizing a wrapper, and knowing which of its hypotheses a deployed system can
actually give up.

There is a second, quieter lesson in the division. Because the engine is
axiom-free and compiles, and the wrappers are cited, the book is honest about its
own confidence in a way informal mathematics rarely is. The parts we are certain of,
the self-reference, are checked by the kernel. The parts that depend on a large
library, the arithmetization and recursion theory, are named so you can find the
verified statement and, if you doubt it, check it yourself. When Chapter 3 asserts
a safety trilemma, it inherits this discipline: the diagonal core compiles, and the
modeling assumptions that make a model a reflective verdict are stated as
assumptions, not smuggled in. That is the most a formalization can offer, and it is
more than the informal versions of these results have ever offered.

# What varies, and what does not

Seven theorems, one engine. Laid side by side, the classical limits differ only in
the first four columns of the recipe and agree entirely in the fifth.

| Theorem | `A` (indices) | `Y` | `t` | Wrapper (universality is...) |
|---|---|---|---|---|
| Cantor | a set | `Bool` | `!` | a power-set surjection |
| Russell | a universe of sets | `Bool` | `!` | unrestricted comprehension |
| Gödel I | codes of formulas | `Bool` | `!` | representability plus completeness |
| Gödel II | codes of formulas | `Bool` | Löb's map | derivability conditions |
| Tarski | codes of sentences | `Bool` | `!` | a definable truth predicate |
| Turing | programs | `Bool` | `!` | a universal language |
| Rice | programs | `Bool` | `!` | reduction from a nontrivial property |

The outcome type is `Bool` in every row, and the flip is negation in every row but
one, where Löb's map is a negation in modal disguise. The index type and the
wrapper are where the mathematics of each theorem actually sits, and they are what a
working mathematician learns when learning these results: how a set indexes its
subsets, how arithmetic codes its syntax, how a language enumerates its programs.
The diagonal is not what you learn. It is what you already knew from the first one.

The compiled fifth column is one of {lean}`no_universal`, {lean}`cantor`,
{lean}`liar_query`, {lean}`no_reflective_verdict`, or the local combinations
{lean}`c2_diagonal_lemma` and {lean}`c2_rice_diagonal`, and every one of them is
Chapter 1's Theorem 1.4 under a fixed point of negation. When Chapter 3 introduces
the hallucination and prompt-injection impossibilities, it adds an eighth and ninth
row to this table and no new machinery to the engine. The reader who has followed
the wrappers here will recognize the safety results as instances the moment their
`A`, `Y`, and `t` are named, which is the point of doing the classical cases first
and in this much detail.

There is one honest caveat, and it is the bridge to the second half of the book.
Every theorem in the table is a flat impossibility. It says a certain system does
not exist, and it says nothing about how close you can come, how many
counterexamples there are, or what it costs to find one. The diagonal is a
yes-or-no instrument because `Y` is `Bool` and `t` has no fixed point at all. When
the safety questions demand quantities, how often a model hallucinates, how large
the adversary's basin of successful attacks is, how confident a probe can be, the
diagonal falls silent, and Chapters 4 through 6 pick up a continuous `Y`, a
connected `A`, and the intermediate value theorem, which delivers the same boundary
object with the metric content the diagonal threw away. The classical limits are
where the story is cleanest. They are not where it ends.

One further observation ties the chapter to the ones ahead. In every classical
instance the wrapper had to argue that a real object, a set, a theory, a language,
a machine, is universal, and universality was granted almost by the definition of
the object: a power set is all subsets, a programming language is closed under its
own interpreter. The safety instances are different in a way that is entirely to the
good. There, universality is not definitional; it is an idealization, and the whole
content of a safety theorem is the argument that a system with certain desirable
properties, being faithful, being calibrated, covering its domain, would have to be
universal, and so cannot exist. The classical wrappers establish universality to
derive a contradiction. The safety wrappers derive universality from a wish list to
show the wish list is inconsistent. The engine does not notice the difference. It
flips a boolean and returns the liar either way. What changes is that in the safety
setting the liar is not a curiosity but a design constraint, and the right response
is not to mourn the impossibility but to read off which item on the wish list a
working system must give up. That reading is Chapter 3.

# Historical and bibliographic notes

Cantor's diagonal argument appeared in 1891, though the 1874 proof of the
uncountability of the reals already contains the idea. Russell communicated his
paradox to Frege in 1902, and Frege's appendix acknowledging it is one of the more
gracious moments in the history of mathematics. Gödel's two incompleteness theorems
are the 1931 paper "Über formal unentscheidbare Sätze"; the diagonal lemma is often
attributed jointly to Gödel and Carnap. Tarski's undefinability theorem is from his
1936 work on the concept of truth in formalized languages. Turing's halting result
is in the 1936 "On Computable Numbers," and Rice's theorem is his 1953 paper on
classes of recursively enumerable sets. Löb's theorem is 1955, and Solovay's
arithmetical completeness of the modal logic `GL` is 1976.

The unification through category theory is Lawvere's "Diagonal arguments and
cartesian closed categories" (1969). The most accessible modern account that works
out Cantor, Russell, Gödel, Tarski, and Turing as instances of a single fixed-point
theorem is Yanofsky's "A universal approach to self-referential paradoxes,
incompleteness and fixed points" (2003), whose organization this chapter follows.
For the recursion theory behind Rice's full form, Rogers's "Theory of Recursive
Functions and Effective Computability" remains standard, and Boolos's "The Logic of
Provability" is the reference for the modal treatment of the second incompleteness
theorem. The machine-checked development these notes track is the companion Lean
library, whose Cantor and Rice formalizations are cited above by file and theorem
name.

# Exercises

The exercises are graded. Routine ones ask you to run the recipe on a new instance
or to fill in a step. Ones marked (harder) ask you to prove something new in Lean or
to handle a subtlety in a hypothesis. Ones marked (open-ended) have no single
answer and point toward later chapters.

**Exercise 2.1.** Prove {lean}`c2_no_universal_bool` by hand without invoking
{lean}`no_universal`, unfolding it to a direct `match` on the universality
hypothesis applied to `fun a => !(f a a)`. Check that your proof and the one in the
text produce the same diagonal witness.

**Exercise 2.2.** State and prove in core Lean that `Unit`, the one-element type,
admits no universal system with fixed-point-free flip: show there is no
`t : Unit → Unit` with `t u ≠ u`. Explain why this is the degenerate case at the
bottom of every row of the summary table.

**Exercise 2.3.** Cantor's theorem is usually stated for `Set A`, not `A → Bool`.
Using the identification of a subset with its indicator, write the statement "no
surjection `A → Set A`" and explain, in one paragraph, why it is the same as
{lean}`c2_cantor_powerset`. Where does the classical `Set`-form proof, cited as
`CCH.cantor_no_surjection_set`, use decidability that the `Bool` form avoids?

**Exercise 2.4.** In {lean}`c2_russell`, the hypothesis `hmem` is never satisfiable
for a type `A` with at least two elements. Prove this: derive `False` from `hmem`
using {lean}`cantor`, and conclude that {lean}`c2_russell` is a theorem whose
hypothesis is empty. Relate this to the modern repairs of comprehension.

**Exercise 2.5.** Write out the propositional Russell paradox `¬ (P ↔ ¬ P)` in Lean
for `P : Prop` and prove it without classical axioms. Then explain, referring to
Remark 2.7, why the chapter compiles the `Bool` version instead in the diagonal
engine.

**Exercise 2.6.** (Gödel, by hand.) Using {lean}`c2_diagonal_lemma` with
`t := fun b => !b`, reprove {lean}`c2_godel_semantic` without the `match`, by
`obtain`-ing the witness in tactic mode. Confirm with `#print axioms` that your
proof depends on no axioms.

**Exercise 2.7.** Identify, for each derivability condition in Theorem 2.12, which
property of an ordinary notion of proof it internalizes. Then explain in one
paragraph why the third condition, and not the first two, is what makes the second
incompleteness theorem harder than the first.

**Exercise 2.8.** State Löb's theorem as a fixed-point statement and identify the
map `t` whose fixed point it takes. Verify that the second incompleteness theorem is
the special case `φ = 0 = 1`, and explain why `Con(T)` is the antecedent that Löb
refuses.

**Exercise 2.9.** Give the liar sentence explicitly as the diagonal behavior in
Tarski's theorem, and trace how {lean}`liar_query` produces it. Then show that if a
definable truth predicate existed, {lean}`c2_godel_semantic` would apply to it, so
that Tarski's theorem also follows from the completeness-plus-soundness collapse.

**Exercise 2.10.** Explain the precise difference between Gödel's `Prov` and
Tarski's `True`: one is definable and the theory is incomplete, the other is not
definable at all. Which property of provability, absent for truth, is responsible?
Frame your answer in terms of recursive enumerability.

**Exercise 2.11.** (Harder.) Prove in core Lean a two-input version of Turing's
theorem: for `f : A → A → Bool` universal and a candidate decider `D : A → A → Bool`
meant to satisfy `D a b = f a b`, there exist `a, b` with `f a b ≠ D a b`. Show that
the diagonal case `a = b` recovers {lean}`c2_turing_halting`.

**Exercise 2.12.** Explain the totality subtlety in Turing's theorem in your own
words: why the contrarian program must be partial, and why the argument would fail
if deciders were allowed to return no answer. Connect this to the transition from
Turing to Rice.

**Exercise 2.13.** For a nontrivial `P : Bool → Bool` with `P false ≠ P true`, show
that `P` is a bijection on `Bool`, hence either the identity or negation. Use this to
sketch how `Foundation.rice_general` reduces to {lean}`c2_rice_diagonal`, and
identify where nontriviality is used.

**Exercise 2.14.** (Harder.) The full Rice's theorem, Theorem 2.22, splits on which
side of `P` the everywhere-undefined program falls. Write out both cases of the
reduction from halting, and explain why the split is necessary and where classical
logic enters.

**Exercise 2.15.** Fill in the summary table for two theorems not treated in the
text: the Grelling–Nelson paradox of heterological adjectives, and the fixed-point
combinator `Y` of the untyped lambda calculus. For each, name `A`, `Y`, `t`, and the
wrapper, and say whether the fixed point is a contradiction or a construction.

**Exercise 2.16.** (Open-ended.) Every row of the summary table has `t` fixed-point
free, so the fixed point Lawvere produces is a contradiction. The lambda-calculus
`Y` combinator uses the same diagonal but wants the fixed point. Speculate on what
distinguishes the destructive uses from the constructive one, and relate it to the
difference between `Bool` with negation and a domain where every map has a fixed
point.

**Exercise 2.17.** (Open-ended.) Pick one AI-safety property, honesty, calibration,
or corrigibility, and attempt to force it into the recipe. Name a candidate `A`,
`Y`, and `t`, and identify precisely which universality hypothesis the property would
have to satisfy for {lean}`no_universal` to apply. Then say what a working system
gives up to avoid satisfying it. Chapter 3 does this for hallucination; compare your
attempt to its treatment.

**Exercise 2.18.** (Open-ended.) The chapter argues that the diagonal is silent on
quantities. For Rice's theorem, formulate a quantitative question the theorem does
not answer, for instance the density of programs on which a fixed heuristic decider
is correct, and speculate on what additional structure, a metric, a measure, a
topology on programs, would be needed to make it precise. This is the question
Chapters 5 and 6 take up for attack basins.

**Exercise 2.19.** State the section form of Lawvere's theorem in a cartesian
closed category, as in the categorical-unification section, and identify, for
Cantor and for Turing, what object plays the role of the outcome `Y`, what map
plays `t`, and what construction provides the section `s`. For Turing, explain why
the universal machine is exactly the section.

**Exercise 2.20.** (Harder.) The summary table lists Löb's map as the flip for
Gödel II, calling it "negation in modal disguise." Make this precise: write the map
`ψ ↦ (Prov(⌜ψ⌝) → φ)` whose fixed point Löb's theorem takes, and show that with
`φ = 0 = 1` its fixed point is the sentence whose unprovability is the second
incompleteness theorem. Explain in what sense this map fails to have a fixed point
in the way negation does, and why the conclusion is nonetheless an impossibility.

**Exercise 2.21.** (Open-ended.) Rice–Shapiro sorts semantic properties into
decidable, r.e., and worse. Place three properties of a language model on this
spectrum, phrased as properties of the function it computes, and say for each
whether the classical theorem predicts you can decide it, recognize it, or neither.
Then say what changes when the property is weakened from exact to approximate, which
is the move Chapter 3 makes.
