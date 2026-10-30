import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Classical Limits" =>

Everything here applies {lean}`no_universal`: change what `A` names, change what
`Y` measures, pick a fixed-point-free `t`, and out falls a theorem proved
between 1874 and 1953 by what looked then like a different argument each time.

The claim is a factoring. Each classical proof has a self-referential heart and
a local wrapper. The heart is always `a ↦ t (f a a)` and the collision of its
name with itself. The wrapper argues the system really is universal: that a set
surjects onto its power set, that a theory represents its own provability, that
a language is closed under the proof's constructions. Lawvere isolated the
heart; this chapter walks the wrappers.

The unification matters beyond elegance. Proved by unrelated tricks, each domain
needs its own genius. Proved by one move, a new domain needs only the checklist,
and the question becomes mathematical: does this system have a section into its
own function space, and does its outcome object carry a fixed-point-free map?
That is what lets later chapters treat hallucination and injection as instances
to verify.

New results are prefixed `c2_`. Where a theorem needs Mathlib or a classical
axiom, it is stated in prose with the verified statement named.

# The recipe

*The recipe.* To obtain a limitative theorem from {lean}`no_universal`:

1. Choose the _index type_ `A`: what the names range over. 2. Choose the
_outcome type_ `Y`: what a behavior reports. For most classical
   results `Y = Bool`.
3. Exhibit a _fixed-point-free_ `t : Y → Y`. For `Bool` this is negation, with
   {lean}`bool_not_fpf` the proof.
4. Argue the _wrapper_: that the system, if it existed as claimed, would satisfy
   `∀ g : A → Y, ∃ a, f a = g`.
5. Conclude by {lean}`no_universal`, or by {lean}`liar_query` for a specific
   self-undermining index.

Steps 1 to 3 are cheap. Step 4 is where the mathematics lives and the only step
that differs. Step 5 is one line. For `Y = Bool` the recipe collapses to one
statement.

```lean
theorem c2_no_universal_bool {A : Type _}
    (f : A → A → Bool) :
    ¬ (∀ g : A → Bool, ∃ a, f a = g) :=
  no_universal (fun b => !b) bool_not_fpf f
```

_Proof._ {lean}`no_universal` with the flip and `bool_not_fpf`. ∎

For _any_ assignment of yes-or-no behaviors to indices, some pattern is
unrealized, and it is always `fun a => !(f a a)`. The theorem does not care
whether `A` is finite or a proper class, whether `f` is computable, or whether
yes and no mean membership, provability, or halting.

*Remark 2.1 (Why `Bool` and not `Prop`).* On `Bool` the fixed-point-free witness is
settled by `decide` and needs no axioms; on `Prop`, reading a system as
universal forces classical principles the moment one case-splits on an arbitrary
`P`. Keeping the engine on `Bool` makes every compiled proof here axiom-free,
and it models a discipline the safety chapters take seriously: a two-valued
verdict is a decision, and a decision is where impossibility bites.

_A finite rehearsal._ Take `A = {0,1}`. There are four behaviors and two names,
so one is unnamed, and `d = fun a => !(f a a)` differs from `f 0` at `0` and
from `f 1` at `1`. The counting proof knew `4 > 2`; the diagonal never counted,
building one unnamed behavior by disagreeing with each `f a` at the input where
disagreement is cheap, its own name.

# Cantor's theorem

Identify `S ⊆ A` with its indicator, a bijection between the power set and `A → Bool`,
so a family of subsets indexed by `A` is `f : A → (A → Bool)` and surjectivity
says every subset occurs.

*Definition 2.2 (Power-set surjection).* A _power-set surjection_ on `A` is
`f : A → (A → Bool)` with `∀ g : A → Bool, ∃ a, f a = g`.

By currying this is exactly a universal boolean system. There is no gap to
close.

*Theorem 2.3 (Cantor, 1891).* _No power-set surjection exists._

```lean
theorem c2_cantor_powerset {A : Type _} (f : A → (A → Bool))
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  cantor f hf
```

_Proof._ Chapter 1's {lean}`cantor` applies directly. Unfolding: universality names
the diagonal subset `d = fun a => !(f a a)`, the set of `a` the `a`-th subset
excludes. Let `f a₀ = d` and evaluate at `a₀` to get `f a₀ a₀ = !(f a₀ a₀)`. ∎

Here `Y = Bool` and `t` is negation. If some outcome were fixed by `t`, the
diagonal set could sit there and the surjection would survive.

Only surjectivity is used. Injective maps `A → (A → Bool)` are abundant; the
theorem forbids only covering. The map need not be computable, definable, or
continuous, so the argument survives any pathology in `f` — which is exactly why
the diagonal is the wrong tool for quantitative questions.

In pure set theory the statement is that no surjection `A → Set A` exists,
proved as `CCH.cantor_no_surjection_set` in `CCHProofs/CCH_03_Cantor.lean` by
the Russell diagonal, with the indicator form `CCH.cantor_no_surjection`. The
`Set`-level proof needs membership decidable enough to case-split; the `Bool`
form needs nothing.

The diagonal set is not a paradox. There is nothing self-contradictory about `{a : a ∉ f a}`;
it is an ordinary subset, listable whenever `f` is computable, and the theorem
says only that it is not one of the `f a`. The paradox appears in Russell, where
comprehension forces the family to include every subset, so the diagonal set
must be both listed and unlisted.

Say `Y` has the _fixed-point property_ if every `t : Y → Y` has a fixed point.
Lawvere: if `A` point-surjects onto `A → Y`, then `Y` has it, and Cantor is the
contrapositive at `Y = Bool`. Read forward the same theorem builds fixed points,
which is how the lambda calculus uses it. The sign of the conclusion is entirely
in whether `Y` has a fixed-point-free map.

Cantor's 1874 uncountability proof used nested intervals and completeness, an
analytic argument; the 1891 diagonal was the second proof, and its power was
generalizing instantly to any set, using only the ability to flip a value. This
thesis runs the two styles in the other order.

The theorem iterates: no largest set, no set of all sets, and a cumulative
hierarchy whose beth numbers are a diagonal step apart. It leaves open whether a
cardinality sits strictly between a set and its power set, and Cohen's forcing
showed the continuum hypothesis is independent of `ZFC` — a
second-incompleteness-flavored fact one level up. The diagonal opens the tower
and does not space the rungs.

Schröder–Bernstein builds a bijection from two injections; Cantor builds
nothing, exhibiting an obstruction and stopping. This thesis is about the second
kind, and when a safety result says "no system can do this," it is
Cantor-shaped.

*Remark 2.4 (Cantor and reflective verdicts).* A model's set of possible behaviors is its
power set, so asking a model to certify every behavior of its own kind is asking
for the surjection Cantor forbids, however large the model.

# Russell's paradox

Comprehension says every property carves out a set. Applied to "is not a member
of itself," `R = {x | x ∉ x}` gives `R ∈ R` iff `R ∉ R`. Cantor needs a codomain
and a claimed surjection; Russell drops the codomain and works with one binary
relation. Historically Russell found it by pushing on Cantor's proof: a universe
of all sets would be surjected onto its power set by the identity.

*Definition 2.5 (Naive membership).* A _naive membership relation_ on `A` is
`mem : A → A → Bool` satisfying comprehension, `∀ g : A → Bool, ∃ a, mem a = g`.

*Theorem 2.6 (Russell, 1902).* _If `mem` is a naive membership relation then some
`r` satisfies `mem r r = !(mem r r)`. No such relation exists._

```lean
theorem c2_russell {A : Type _} (mem : A → A → Bool)
    (hmem : ∀ g : A → Bool, ∃ a, mem a = g) :
    ∃ r, mem r r = !(mem r r) :=
  liar_query mem hmem
```

_Proof._ {lean}`liar_query` verbatim with `f` renamed. Comprehension on
`fun a => !(mem a a)` names a set `r`; evaluating at `r` gives the collision.
Feed it to {lean}`bool_not_fpf` for outright `False`. ∎

Again `Bool` and negation, and the Russell set is the diagonal behavior — the
same object that in Cantor was the diagonal subset and in Chapter 1 the liar.

The hypothesis is comprehension, and the paradox is what forced set theory to
give it up. Zermelo's separation carves subsets only from a set already given,
so the diagonal reproves Cantor rather than exploding. The type-theoretic
repair, the one Lean uses, stratifies by universe level so `mem a a` is
ill-formed. In Lean the naive relation is well-typed, which is why
{lean}`c2_russell` compiles, but `hmem` is never satisfiable for nontrivial `A`:
the theorem proves its hypothesis empty.

*Remark 2.7 (`Bool` versus `Prop`, again).* The propositional paradox needs no axioms for
`¬ (P ↔ ¬ P)`. The `Bool` version is compiled because its flip composes with the
engine using only `congrFun` and `decide`, whereas `Prop`-valued behaviors
invite classical case-splits downstream. When a safe-or-unsafe judgment is
genuinely two-valued, the impossibility is constructive, which matters when a
machine computes the judgment.

Frege's _Grundgesetze_ derived arithmetic from logic using Basic Law V,
comprehension in disguise, and Russell's two lines refute it. The paradox is why
set theory has axioms rather than a single comprehension schema. Three repairs
survived: Zermelo's separation with foundation banning `x ∈ x`; Russell's
ramified types, ancestor of Lean's universe hierarchy; and Quine's New
Foundations, restricting comprehension to stratified formulas.

Cantor's paradox is the diagonal against the set of all sets, Burali-Forti
against the set of all ordinals. Each is {lean}`c2_russell` with a different
reading of `mem`, and each was historically a separate shock.

# Gödel's first incompleteness theorem

Cantor and Russell hand you universality almost free, because a power set or a
comprehension schema is a surjection by fiat. Arithmetic does not. Running the
diagonal against a formal theory needs first that the theory talk about its own
syntax, and that is substantial number theory.

We separate the diagonal, which compiles, from the arithmetization, which we
describe and cite. The self-reference is finite and mechanical and belongs in
the kernel. The arithmetization is a long verification the literature carries
out.

## Representability as point-surjectivity

Fix a consistent `T` in the language of arithmetic, strong enough to represent
primitive recursive functions, and let `⌜φ⌝` be Gödel codes.

*Definition 2.8 (Representability).* A predicate `g` on codes is _representable_ in
`T` when some formula `φ` has `T ⊢ φ(n)` whenever `g n` holds and `T ⊢ ¬ φ(n)`
whenever it fails. Gödel's central arithmetical fact is that every recursive
predicate is representable in `Q`.

Representability is the wrapper's surjectivity. Read `f a b` as "the formula
coded by `a`, applied to `b`, is provable." Then representability says some code
`a` has `f a = g`, which is point-surjectivity restricted to recursive `g`. That
restriction is the one honest difference from Cantor, and it suffices, because
the diagonal behavior we build is itself recursive.

## Arithmetizing syntax

The language speaks of numbers, not formulas. Gödel encodes each syntactic
object as a number, so statements about formulas become statements about
numbers. Assign a number to each symbol, code a formula by prime factorization
of its symbol sequence, and code a proof by the sequence of its lines.

The delicate step is coding finite sequences of unbounded length in a language
whose variables range over single numbers, solved by Gödel's beta function via
the Chinese remainder theorem. With sequences codable, primitive recursion is
expressible, and "`p` codes a proof of `n`" is representable in `Q`. Then
`Prov(n)` is "there exists `p` coding a proof of `n`," one unbounded existential
over a primitive recursive matrix.

*Lemma 2.9 (Diagonal lemma, abstract form).* _For universal `f : A → A → Y` and any
`t : Y → Y`, some `a` has `f a a = t (f a a)`._

```lean
theorem c2_diagonal_lemma {A Y : Type _} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g) (t : Y → Y) :
    ∃ a, f a a = t (f a a) :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

_Proof._ Universality names `fun a => t (f a a)` by some `a₀`; evaluate at `a₀`. ∎

This is {lean}`lawvere` reorganized to expose the index rather than the fixed
value. In the arithmetical reading `A` is codes of one-variable formulas, `f a b`
is provability of the diagonalization, and `t` is the operation the target
property performs. The genuine Gödel diagonal lemma, producing an honest
arithmetic sentence, is the arithmetization of this step; it is a theorem of
`Q`, developed in the model-theory literature and formalized in Mathlib's
first-order logic library.

## The Gödel sentence

Apply the diagonal lemma to "not provable" to get `G` with `T ⊢ G ↔ ¬ Prov(⌜G⌝)`:
a sentence saying, correctly, "I am not provable in `T`."

*Theorem 2.10 (Gödel I, 1931).* _Let `T` be consistent, recursively axiomatized,
and representationally strong. Then `T` proves neither `G` nor `¬ G`. If `T` is
sound, `G` is true._

_Proof (structure)._ If `T ⊢ G` then `T ⊢ Prov(⌜G⌝)`, and the fixed point gives
`T ⊢ ¬ Prov(⌜G⌝)`, contradicting consistency. If `T ⊢ ¬ G` then `T ⊢ Prov(⌜G⌝)`;
under omega-consistency, or by the Rosser trick, the absence of an actual proof
again yields a contradiction. If `T` is sound then `G`, being unprovable, is
what it says it is. ∎

The collision at the centre is Lemma 2.9. A consistent `T` that could decide
every sentence would have a total correct boolean system over its own sentences,
and the diagonal with `t` negation produces a sentence equal to its own
negation.

```lean
theorem c2_godel_semantic {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  match c2_diagonal_lemma f hf (fun b => !b) with
  | ⟨a₀, ha₀⟩ => bool_not_fpf (f a₀ a₀) ha₀.symm
```

_Proof._ Lemma 2.9 with the flip, refuted by {lean}`bool_not_fpf`. ∎

*What it does and does not say.* It says a boolean system universal over its own
indices is contradictory. Arithmetically, universality is representability plus
completeness: representability gives the surjection onto recursive behaviors,
and completeness promises a definite provable truth value for every
self-referential sentence, so the diagonal behavior lands back in the
represented family. The compiled theorem is the semantic core: no consistent
theory is both representationally rich and complete.

*The hypotheses.* Consistency makes the collision fatal rather than odd; an
inconsistent theory proves everything, so the flip effectively has a fixed
point. Recursive axiomatizability makes `Prov` representable, so the diagonal
behavior lands in range; drop it and a theory can be complete, as the full
theory of the standard model is, at the price of not being listable.
Representational strength is point-surjectivity itself.

*Rosser's refinement.* Gödel needed omega-consistency to rule out `T ⊢ ¬ G`.
Rosser removed it in 1936 with a sentence saying "for every proof of me there is
a shorter proof of my negation." Still a fixed point, so still Lemma 2.9
arithmetized, but the operation now compares proof lengths, making plain
consistency enough. The upgrade costs nothing in the engine; it refines the
wrapper by choosing a diagonal behavior fatal under a weaker hypothesis.

*The epistemic sting.* `G` is unprovable in `T` and, if `T` is sound, true. So
the metatheory knows `G` while `T` cannot prove it. There is no contradiction:
our knowledge uses soundness of `T`, a fact living outside `T` that `T` cannot
establish about itself.

*Concrete unprovable truths.* The dismissal that `G` is artificial no longer
holds. Goodstein's theorem, about sequences that appear to grow without bound
but always reach zero, is true and independent of `PA`, provable only by
transfinite induction to `ε₀`. Paris–Harrington is another.

*Remark 2.11 (The safety reading).* Gödel is the template for every later result of
the form "a system powerful enough to model itself cannot certify itself." A
model outputting calibrated confidence in its own future outputs, a verifier
verifying verifiers including itself, an overseer auditing systems as capable as
it is: each is a `Prov`-like predicate turned on its own domain. The engineering
temptation is to believe more capability closes the gap. Gödel says stronger
representation only sharpens the diagonal.

# Gödel's second incompleteness theorem

The first theorem produces an undecided sentence; the second identifies one, the
theory's own consistency `Con(T) := ¬ Prov(⌜0 = 1⌝)`.

*Theorem 2.12 (Gödel II, 1931).* _A consistent, recursively axiomatized `T` whose
provability predicate satisfies the Hilbert–Bernays–Löb derivability conditions
does not prove `Con(T)`._

The conditions make `Prov` behave like real proof inside `T`:

1. If `T ⊢ φ` then `T ⊢ Prov(⌜φ⌝)`. Proofs are internally recognized. 2. `T ⊢ Prov(⌜φ → ψ⌝) → (Prov(⌜φ⌝) → Prov(⌜ψ⌝))`.
Internal modus ponens. 3. `T ⊢ Prov(⌜φ⌝) → Prov(⌜Prov(⌜φ⌝)⌝)`. Internal
recognition of recognition.

_Proof (structure)._ The conditions give `T ⊢ Con(T) → G`: internal consistency
lets the theory carry out, about itself, the argument that `G` is unprovable,
which is what `G` asserts. But `T ⊬ G`. So `T ⊬ Con(T)`. ∎

## The second theorem, machine-checked

What can be checked here is the derivability-conditions argument. What cannot is
the arithmetization: that a theory such as `PA` really admits a provability
predicate satisfying the conditions and the fixed point. That is a large
formalization this development does not carry out. What follows is the theorem
relative to those inputs, which is how the derivability presentation states it.

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
  D2 : ∀ a b, Thm
      (imp (box (imp a b)) (imp (box a) (box b)))
  D3 : ∀ a, Thm (imp (box a) (box (box a)))
```

Two derived rules from `K`, `S`, and modus ponens, the only propositional
reasoning needed.

```lean
theorem c2_s_comb (P : c2_PC) {a b c : P.S}
    (h₁ : P.Thm (P.imp a (P.imp b c)))
    (h₂ : P.Thm (P.imp a b)) :
    P.Thm (P.imp a c) :=
  P.mp (P.mp (P.ax_S a b c) h₁) h₂

theorem c2_syll (P : c2_PC) {a b c : P.S}
    (h₁ : P.Thm (P.imp a b)) (h₂ : P.Thm (P.imp b c)) :
    P.Thm (P.imp a c) :=
  c2_s_comb P (P.mp (P.ax_K (P.imp b c) a) h₂) h₁
```

The hypotheses `fix₁` and `fix₂` are the two directions of the fixed point `g ↔ (Prov(g) → A)`,
supplied rather than constructed.

*Theorem 2.12a (Löb, 1955).* _If `T ⊢ Prov(A) → A` then `T ⊢ A`._

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
`Prov(g) → Prov(Prov(g) → A)`. A second `D2` gives `Prov(g) → (Prov(Prov(g)) → Prov(A))`,
and `D3` contracts the boxes to `Prov(g) → Prov(A)`. Composing with the
hypothesis gives `Prov(g) → A`, the right-hand side of the fixed point, so `g`
is a theorem; necessitating `g` and applying modus ponens delivers `A`. ∎

```lean
def c2_Con (P : c2_PC) : P.S := P.imp (P.box P.bot) P.bot

theorem c2_godel_second (P : c2_PC) {g : P.S}
    (fix₁ : P.Thm (P.imp g (P.imp (P.box g) P.bot)))
    (fix₂ : P.Thm (P.imp (P.imp (P.box g) P.bot) g))
    (hcon : P.Thm (c2_Con P)) :
    P.Thm P.bot :=
  c2_loeb P fix₁ fix₂ hcon
```

_Proof._ `Con` unfolds to `Prov(⊥) → ⊥`, the hypothesis of Löb at `A := ⊥`. ∎

Read contrapositively, this is Theorem 2.12. One check is worth doing, since a
theorem whose hypotheses cannot be met is true for empty reasons: the axiom set
is satisfiable.

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
inhabited, so the theorems are not vacuous. It does _not_ establish that a
consistent theory meets the conditions. That claim is the arithmetization, and
it remains the one thing here taken from the literature rather than checked.

Löb's theorem is itself a diagonal, the fixed point of `ψ ↦ (Prov(⌜ψ⌝) → φ)`,
and the second incompleteness theorem is the case `φ = 0=1`, because `Con(T)` is
exactly `Prov(⌜0=1⌝) → 0=1` waiting for Löb to refuse it.

*Why the arithmetization stays in prose.* The derivability conditions are
statements about a specific arithmetized `Prov`, and verifying them is the
deferred arithmetization plus the third condition, which internalizes the first.
There is no faithful short core-Lean rendering, because the content is the
syntactic behavior of a particular predicate, not the abstract diagonal. The
abstract diagonal is already compiled as Lemma 2.9.

*Remark 2.13 (Self-certification is the second theorem).* This is the sharpest
classical statement of a limit recurring throughout AI safety: a system cannot
vouch for its own soundness from within. "This model will not deceive you" is a
`Con`-like sentence, and a model strong enough to state it and satisfying the
internal-coherence analogues cannot prove it without already being unsound.
Chapter 7 argues that a deployed system's own assurances carry no evidential
weight beyond an external check, and that the external check faces its own
second theorem one level up.

*Provability as a modal logic.* Both theorems package cleanly in `GL`, where the
box reads "provable in `T`." Condition 1 is necessitation, condition 2 is axiom
`K`, condition 3 is axiom `4`. Löb's theorem is the axiom `GL`. Its frames are
exactly the transitive, converse-well-founded ones, and converse
well-foundedness is the modal shadow of consistency: a chain of ever-stronger
provability claims must terminate.

*Consistency strength.* Because `T` cannot prove its own consistency, a theory
proving `Con(T)` is strictly stronger, and "proves the consistency of"
well-orders the natural theories from weak arithmetic up through large
cardinals. Ordinal analysis measures the steps, assigning `PA` the ordinal `ε₀`.
The picture to keep is a ladder no rung of which can see its own footing, the
exact shape Chapter 7 gives to a tower of overseers.

# Tarski's undefinability of truth

A truth predicate satisfies `True(⌜φ⌝) ↔ φ` for every sentence, Tarski's schema
T.

*Definition 2.14 (Definable truth predicate).* A language interpreting arithmetic
has a _definable truth predicate_ when some formula `True(x)` satisfies schema T
for every sentence of the language.

Material adequacy plus definability makes the verdict system universal over its
own sentences: every boolean condition the language can state, including the
negation of the predicate composed with the diagonal, is some sentence's verdict
pattern.

*Theorem 2.15 (Tarski, 1936).* _No language that can represent its own syntax and
interpret arithmetic has a definable truth predicate._

```lean
theorem c2_tarski {A : Type _} (True? : A → A → Bool)
    (hT : ∀ g : A → Bool, ∃ a, True? a = g) : False :=
  no_reflective_verdict True? hT
```

_Proof._ Such a predicate is a reflective verdict, and
{lean}`no_reflective_verdict` says none exists. Unfolding, the diagonal builds
the liar `L` with `True?(⌜L⌝) ↔ ¬ True?(⌜L⌝)`, and adequacy turns that into `L ↔ ¬ L`.
∎

*Identifying `Y` and `t`.* `Bool` and negation. The witness is the liar, which
is {lean}`liar_query` read as a sentence rather than a set or a program. The
liar is not a curiosity at the edge of the theory; it is the exact obstruction.

*Tarski versus Gödel.* Gödel's `Prov` _is_ definable, because provability is
recursively enumerable, and the price is incompleteness: the predicate exists
but the theory cannot decide the sentence it produces. Tarski's `True` would
have to be definable to run the same diagonal, and the conclusion is that it is
not definable at all, because if it were the liar would be an outright
contradiction rather than an undecided sentence. Provability is a shadow of
truth the system can cast; truth itself it cannot hold. The gap between them is
the room the first theorem lives in. Cleanly: if truth were definable it would
be a complete sound provability predicate, which {lean}`c2_godel_semantic`
already refuted.

## The hierarchy of metalanguages

Truth for `L` is definable, just not in `L`: it is definable in a richer `L'`
with the resources to quantify over `L`'s sentences. Truth for `L'` needs `L''`,
and so on up an unbounded hierarchy, each level defining truth for the one below
and none its own. This is the consistency-strength ladder again, and not by
coincidence: both are the second-theorem shape.

There are ways to buy a language its own truth predicate, and each pays a price
the recipe predicts. Kripke's 1975 theory makes the predicate _partial_,
undefined on ungrounded sentences like the liar, built as the least fixed point
of a monotone operator; the liar never settles, and adequacy holds only for
grounded sentences. This dodges Tarski by refusing totality, exactly the move
separating halting from Rice: let the deciding object withhold judgment and the
flat impossibility relaxes into a statement about where judgment must be
withheld.

*Remark 2.16 (Truth probes and Chapter 8).* A truth predicate that is total, exact,
and expressible in the system whose outputs it judges is exactly what Tarski
forbids. Chapter 8 studies probes reading internal state to estimate whether a
model "believes" its output, and the standing objection is Tarskian. The
resolution is not to defeat the theorem but to change the domain: from outputs
to activations, from a two-valued verdict to a continuous score on a connected
space, where the intermediate value theorem takes over.

# Turing and the halting problem

*Definition 2.17 (Halting decider).* A _halting decider_ for a universal system
`f : A → A → Bool` is a total `D : A → Bool` intended to satisfy `D a = f a a`,
where `f a a` records the halting behavior of program `a` on its own code.

*Theorem 2.18 (Turing, 1936).* _For every universal `f` and every candidate `D`
there is a program `a` with `f a a ≠ D a`._

```lean
theorem c2_turing_halting {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) (D : A → Bool) :
    ∃ a, f a a ≠ D a :=
  match hf (fun a => !(D a)) with
  | ⟨a₀, ha₀⟩ =>
    ⟨a₀, fun h =>
      bool_not_fpf (D a₀) ((congrFun ha₀ a₀).symm.trans h)⟩
```

_Proof._ Universality names the contrarian behavior `fun a => !(D a)` by `a₀`.
Evaluating at `a₀` gives `f a₀ a₀ = !(D a₀)`. If the decider were right there we
would get `!(D a₀) = D a₀`, refuted by {lean}`bool_not_fpf`. ∎

The contrarian program is the classical construction: run `D` on your own code,
then loop if `D` says halt and halt if `D` says loop. Same `a₀` as everywhere
else, now reading `Y` as halts-or-loops and `t` as "do the opposite."

*The partiality subtlety.* A real decider must be _total_, while the programs it
judges are _partial_. The contrarian program is partial in exactly the way that
breaks a total decider. If deciders could be partial the theorem would not
follow in this form, and the correct statement becomes Rice's, about total
decision of a nontrivial semantic property.

*The universal machine is the wrapper.* The hypothesis `∀ g, ∃ a, f a = g` is
the existence of a universal Turing machine, and Turing built one. Without it
there is no closure under diagonalization, and halting for a non-universal model
can be decidable; for finite automata it is trivial. Undecidability is a
property of systems rich enough to host their own interpreter.

*Where halting sits.* Halting is the canonical undecidable problem, complete for
the r.e. sets under many-one reduction. It is `Σ₁`, one existential over a
decidable matrix, the same shape as `Prov`, which is no accident: `Prov` is
halting for a proof search.

*Remark 2.19 (Runtime verification).* No static analyzer decides termination for all
programs. For AI systems the behavioral questions are far harder, whether a
model will ever produce disallowed content or an agent ever take an unsafe
action, and halting is the floor. The safety chapters do not lean on Turing
directly, because they want quantitative statements, but Turing is the
qualitative backstop saying the quantitative work is necessary.

# Rice's theorem

A property is _semantic_ when it depends only on the function a program
computes, and _nontrivial_ when some programs have it and some do not. Rice
sweeps the class in one argument.

*Definition 2.20 (Semantic decider).* For universal `f`, a _semantic decider_ is a
total `D : A → Bool` claiming to compute `f a a` from `a` alone.

*Theorem 2.21 (Rice, diagonal core).* _For every universal `f` and every `D`, some
`a` has `f a a ≠ D a`._

```lean
theorem c2_rice_diagonal {A : Type _} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) (D : A → Bool) :
    ∃ a, f a a ≠ D a :=
  c2_turing_halting f hf D
```

_Proof._ {lean}`c2_turing_halting` under a change of reading. ∎

That Rice's core proof is literally Turing's is the chapter's thesis made blunt.
Turing decides one property, Rice any property, and the diagonal does not
notice, because it only ever sees a boolean `D` and flips it. What distinguishes
them is entirely the wrapper.

*Theorem 2.22 (Rice, full form).* _Let `P` be a nontrivial semantic property of
partial recursive functions. Then `{e | φ_e ∈ P}` is not recursive._

_Proof (structure)._ Nontriviality gives a program with the property and one
without; without loss the everywhere-undefined program lacks `P`. Given a
claimed decider, reduce halting to it: from any program and input build a
program behaving like the witness if the input halts and like the empty program
otherwise, so it has `P` exactly when the input halts. A decider for `P` would
decide halting. ∎

This needs an acceptable numbering with the `s-m-n` theorem and a case analysis
on which side of `P` the empty function falls, using classical logic and
Mathlib's recursion theory. The companion development formalizes the core and
the safety corollaries in `Foundation/F_02_RiceTheorem.lean`:
`Foundation.rice_diagonal` is Theorem 2.21 in mismatch form,
`Foundation.rice_general` is the property version for nontrivial `P : Bool → Bool`,
and `Foundation.no_automated_self_test` is the reading we want.

*Identifying `Y` and `t`.* `Bool` and negation. What is new is the quantifier
over properties, and the recipe absorbs it: each nontrivial property yields a
boolean `D` through the reduction, and one fixed-point-free `t` defeats them
all.

*The hypothesis.* Nontriviality is load-bearing, the analogue of surjectivity
being nondegenerate. A trivial property is decided by a constant function and
there is no contradiction, because the constant decider is never wrong. The
diagonal needs two outcomes to flip between.

## Rice–Shapiro and the shape of the undecidable

Rice–Shapiro says a semantic property has an r.e. index set only if it is
determined by finite information: a function has it exactly when some finite
subfunction does, and every extension keeps it. Properties violating this, "is
total," "computes a constant," are not even r.e.

That finer picture is what the safety chapters need, because it locates the line
between checkable and uncheckable. A property depending only on finitely much
observed behavior can be recognized when it appears though its absence never
confirmed, which is the logical form of "you can catch a model doing something
bad but cannot certify it never will." A property depending on the whole
infinite behavior cannot even be recognized. Rice–Shapiro is the classical
statement that monitoring is possible and certification is not.

*Remark 2.23 (No automated semantic testing).* A property of the function a model
computes, whether it is honest or aligned or safe, is semantic, and Rice says no
general automated test decides it for universal systems.
`no_automated_self_test` is exactly this. A benchmark is an attempt to decide a
semantic property by running finitely many inputs, and Rice is why a benchmark
can only sample, never certify.

# The categorical unification

In a cartesian closed category a system is a map `f : A → Y^A`, and the cleanest
hypothesis is a _section_ `s : Y^A → A` with `f ∘ s = id`. Lawvere's theorem is
that any `t : Y → Y` then has a fixed point `y : 1 → Y` with `t ∘ y = y`. The
proof is the same diagonal drawn as a commuting diagram: precompose with `A → A × A`,
transpose, apply `t`, and use the section to find the self-referential point.

Each classical theorem is Lawvere's theorem in a _particular_ cartesian closed
category, not merely an argument shaped like it. Cantor is sets with `Y = 2`.
Turing and Rice live in a category of assemblies or a realizability topos, where
maps are tracked by programs and the section is a universal machine.

We do not compile the categorical version, since doing it honestly needs a
category theory library and the payoff is conceptual. The value of knowing the
source is that it tells you when a new impossibility will be an instance:
whenever the system is a map into an internal function space with a section, and
the outcome object carries a fixed-point-free map, only the reading remains.

# Interlude: the wrapper is the mathematics

The engine is three lines precisely because a century of work moved all the
difficulty into the wrappers, and the wrappers are hard. Coding syntax into
arithmetic, building a universal machine, constructing an acceptable numbering
with `s-m-n`, establishing the derivability conditions: each is a substantial
theorem, and each is what a graduate course actually spends its time proving.
The diagonal is the punchline, and punchlines are short.

The consequence for the rest of this thesis is that to prove a new impossibility
you never re-prove the diagonal. You argue that a model with such-and-such
capabilities is universal over the relevant behaviors, that a defense must
answer every injection including those about itself, that a probe is asked to be
a total exact predicate on the states whose truth it reports. When that argument
succeeds the impossibility is immediate; when it fails, the failure is exactly
the escape hatch.

There is a quieter lesson. Because the engine is axiom-free and compiles while
the wrappers are cited, this development is honest about its own confidence in a
way informal mathematics rarely is. The parts we are certain of are checked by
the kernel; the parts depending on a large library are named so you can find the
verified statement.

# What varies, and what does not

| Theorem | `A` (indices) | `Y` | `t` | Wrapper (universality is...) |
|---|---|---|---|---|
| Cantor | a set | `Bool` | `!` | a power-set surjection |
| Russell | a universe of sets | `Bool` | `!` | unrestricted comprehension |
| Gödel I | codes of formulas | `Bool` | `!` | representability plus completeness |
| Gödel II | codes of formulas | `Bool` | Löb's map | derivability conditions |
| Tarski | codes of sentences | `Bool` | `!` | a definable truth predicate |
| Turing | programs | `Bool` | `!` | a universal language |
| Rice | programs | `Bool` | `!` | reduction from a nontrivial property |

The outcome type is `Bool` in every row and the flip is negation in every row
but one, where Löb's map is negation in modal disguise. The index type and the
wrapper are where the mathematics sits, and they are what one actually learns
from these results. The diagonal is not what you learn; it is what you already
knew from the first one.

The compiled fifth column is always one of {lean}`no_universal`, {lean}`cantor`,
{lean}`liar_query`, {lean}`no_reflective_verdict`, {lean}`c2_diagonal_lemma`, or
{lean}`c2_rice_diagonal`, and each is Theorem 1.4 under a fixed point of
negation. Chapter 3 adds an eighth and ninth row and no new machinery.

One honest caveat bridges to the second half. Every theorem in the table is a
flat impossibility, silent on how close you can come, how many counterexamples
exist, or what finding one costs. The diagonal is a yes-or-no instrument because
`Y` is `Bool` and `t` has no fixed point at all.

A last observation. In every classical instance universality was granted almost
by definition of the object: a power set is all subsets, a language is closed
under its own interpreter. In the safety instances universality is an
idealization, and the content is the argument that a system with desirable
properties, being faithful, calibrated, and covering, would have to be universal
and so cannot exist.

# Historical notes

Cantor's diagonal is 1891, though the 1874 uncountability proof contains the
idea. Russell wrote to Frege in 1902. Gödel's theorems are the 1931 paper; the
diagonal lemma is often attributed jointly to Gödel and Carnap. Tarski's
undefinability is 1936, Turing's halting result 1936, Rice's theorem 1953, Löb's
1955, and Solovay's arithmetical completeness of `GL` 1976.

The unification is Lawvere (1969); the accessible modern account working out the
instances is Yanofsky (2003), whose organization this chapter follows. Rogers's
_Theory of Recursive Functions and Effective Computability_ remains standard for
the recursion theory behind Rice, and Boolos's _The Logic of Provability_ for
the modal treatment of the second theorem.
