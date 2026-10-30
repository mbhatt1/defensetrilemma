import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "Preliminaries" =>

This chapter fixes vocabulary: how to read the Lean, the set-and-function
language of the diagonal engine, the topology the analytic engine needs, and how
the development is built and audited.

Two pictures recur. Combinatorial: a system naming its own behaviors cannot be
everywhere consistent, because the behavior disagreeing with each name at that
name is itself a behavior. Geometric: a continuous quantity negative somewhere
and positive elsewhere vanishes in between. The first is the diagonal, the
second the intermediate value theorem, and every impossibility here is one of
the two in costume.

A reader fluent in Lean should skim to the roadmap, noting `congrFun` and
`match` on an existential.

# How to read the Lean 4

The code blocks are the proofs, elaborated as this document builds and checked
by the kernel. Definitions here are prefixed `c0_` so they cannot clash with the
development.

## Types and terms

Lean is built on types. Every term has a type, written `e : T`, checked before
the term means anything. `Nat` is the naturals, `Bool` the two-element type,
`Prop` the type of propositions.

*Definition 0.1 (Type and term).* A _type_ classifies terms. A _term_ `e` _has
type_ `T`, written `e : T`, when the language's rules assign `T` to `e`.
Type-checking verifies such assignments mechanically.

Types have types, and universes form a hierarchy `Type : Type 1 : …` to avoid
the paradox of Chapter 1. `Type _` means "some level, inferred," and `Sort` is
the umbrella: `Prop = Sort 0`, `Type = Sort 1`.

*Example 0.2.* `2 : Nat`, `true : Bool`, and `1 + 1 = 2 : Prop`. The first live
block asserts the last, proved by `rfl`.

```lean
example : 1 + 1 = 2 := rfl
```

An `example` is an anonymous check. Named results use `def` for data and
`theorem` for proofs; core Lean has no `lemma`.

## Functions and application

`f : A → B` applied to `a : A` is written `f a`, by juxtaposition. Application
binds tighter than almost everything, so `f a + 1` is `(f a) + 1`.

*Definition 0.3 (Function type).* For types `A` and `B`, `A → B` is the type of
functions from `A` to `B`. Application of `f : A → B` to `a : A` is `f a : B`.

A lambda `fun x => e` has type `A → B` when `e : B` given `x : A`; naming the
argument left of the colon is the same thing.

```lean
def c0_double (n : Nat) : Nat := n + n
def c0_double' : Nat → Nat := fun n => n + n
```

Application computes, and `rfl` accepts it.

```lean
example : c0_double 3 = 6 := rfl
```

Composition and identity are worth naming, because the diagonal is a claim about
a composite.

```lean
def c0_id {A : Type} (a : A) : A := a
def c0_comp {A B C : Type} (g : B → C)
    (f : A → B) : A → C := fun a => g (f a)
example : c0_comp c0_double c0_double 3 = 12 := rfl
```

Curly braces mark _implicit_ arguments, inferred by Lean and never written at a
call site.

## Currying and the shape A → A → Y

The arrow associates right and application left, so `A → A → Y` is `A → (A → Y)`
and `f a b` is `(f a) b`. The conventions make currying invisible. The central
object of this thesis has this shape.

*Definition 0.4 (Currying).* A two-argument function into `Y` is represented
curried as `f : A → A → Y`. Then `f a : A → Y` supplies the first argument only,
and `f a b : Y` supplies both.

Read `f a` as the _behavior indexed by_ `a`, and `f a b` as that behavior at
`b`.

```lean
def c0_add : Nat → Nat → Nat := fun a b => a + b
example : c0_add 2 3 = 5 := rfl
```

*Example 0.5.* Let `f n m` report whether behavior `n` fires at slot `m`. Then
`f n` is the whole behavior and `f n n` is the behavior at its own name. That is
the _diagonal_, and Chapter 1 shows it is where self-referential systems break.
Both arguments range over the same set, so a name is also a legal input.

## ∀ and ∃

A proof of `P : Prop` is a term of type `P`, which is why Lean proofs look like
programs. Propositions are _proof-irrelevant_: any two proofs of one proposition
are definitionally equal, so a theorem's content is its statement plus its axiom
dependencies, never the term the elaborator built. `∀ x : A, P x` is a dependent
function type, proved with a lambda.

*Definition 0.6 (Universal quantifier).* `∀ x : A, P x` is the type of proofs
that `P a` holds for every `a : A`. A term of it maps each `a` to a proof of `P a`.

```lean
theorem c0_forall_le : ∀ n : Nat, n ≤ n :=
  fun n => Nat.le_refl n
```

Universal instantiation is application: `h a` proves `P a`. The existential is
dual, a pair `⟨a, h⟩` built with the anonymous constructor.

*Definition 0.7 (Existential quantifier).* `∃ x : A, P x` is the type of proofs
that some `a : A` satisfies `P`. A term is a pair `⟨a, h⟩` with `a : A` the
witness and `h : P a`.

```lean
theorem c0_exists_zero : ∃ n : Nat, n = 0 := ⟨0, rfl⟩
```

To use one, take it apart with `match`. Building packs a pair; using unpacks
one. The Lawvere proof does one of each. Implication is the function arrow.

```lean
theorem c0_imp {p q : Prop} (h : p → q) (hp : p) : q := h hp
```

Almost every theorem takes its ambient types implicitly, which is why statements
about all sets look like statements about one.

## Negation, disjunction, the empty proposition

`¬ P` is definitionally `P → False`, and `False` has no proof.

*Definition 0.8 (Negation and the empty proposition).* `False` is the
proposition with no constructors. For `P : Prop`, `¬ P` is `P → False`. From
`False` anything follows, by `False.elim`.

```lean
theorem c0_not_false : ¬ False := fun h => h
theorem c0_ex_falso {p : Prop} (h : False) : p :=
  False.elim h
```

Inequality is negated equality: to use `h : a ≠ b`, hand it a proof of `a = b`
and collect `False`. Every contrapositive result below does this.

*Definition 0.9 (Disjunction).* `P ∨ Q` is proved by `Or.inl` on a proof of `P`
or `Or.inr` on a proof of `Q`, and used by case analysis.

```lean
example : (1 = 1) ∨ (2 = 3) := Or.inl rfl

theorem c0_or_comm {p q : Prop} (h : p ∨ q) : q ∨ p :=
  match h with
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

Conjunction `P ∧ Q` is dual: built from two proofs, used by projection.

## Structures

*Definition 0.10 (Structure).* A structure is a type whose terms are tuples of
named fields. Declaring it yields a constructor and one projection per field.

```lean
structure c0_Point where
  x : Nat
  y : Nat

def c0_origin : c0_Point := { x := 0, y := 0 }
def c0_origin' : c0_Point := ⟨0, 0⟩
example : c0_origin.x = 0 := rfl
```

One bracket notation builds structures, `∃` proofs, and `∧` proofs, because all
three are structures.

```lean
theorem c0_and_comm {p q : Prop} (h : p ∧ q) : q ∧ p :=
  match h with
  | ⟨hp, hq⟩ => ⟨hq, hp⟩
```

## Inductive types

*Definition 0.11 (Inductive type).* An inductive type is specified by a finite
list of constructors, each a function into the type. Its terms are exactly those
built by finitely many constructor applications, which is what makes `match`
exhaustive.

```lean
inductive c0_Nat where
  | zero : c0_Nat
  | succ : c0_Nat → c0_Nat
```

A structure is the one-constructor case; `And` is a structure landing in `Prop`.

```lean
structure c0_And (p q : Prop) : Prop where
  intro ::
  left : p
  right : q
```

The existential's constructor is dependent: it packages an element and a proof
about that element.

```lean
inductive c0_Exists {A : Type} (P : A → Prop) : Prop where
  | intro : (a : A) → P a → c0_Exists P
```

So `⟨a, h⟩` is `intro` applied to a witness and a proof, and `match` is the
recursor exposing them. Nothing in the diagonal proof is special notation.

## Term mode and tactics

The core arguments are term mode, because a five-line theorem gets a five-line
proof with every symbol visible. Tactics appear only for small decidable facts.

*Remark 0.12.* Both modes produce the same object: a tactic block elaborates to a term
and the kernel checks the term. A tactic producing a wrong term yields an error,
not a false theorem.

## Pattern matching

`match` branches on the shape of an inductive term, binding the pieces, on data
and proofs alike.

```lean
def c0_pred : Nat → Nat
  | 0 => 0
  | n + 1 => n
```

The standard move is `match hf (…) with | ⟨a₀, ha₀⟩ => …`, pulling a witness out
of an existential produced by surjectivity.

## Dot notation

`h.symm` means `Eq.symm h`, with the namespace found from `h`'s type. Spelling
convenience, no logical content.

```lean
theorem c0_symm {A : Type} {a b : A} (h : a = b) : b = a :=
  h.symm
theorem c0_trans {A : Type} {a b c : A} (h1 : a = b)
    (h2 : b = c) : a = c :=
  h1.trans h2
```

## rfl and definitional equality

`rfl` proves an equality whose sides agree by computation. It runs any finite
computation but proves no quantified statement: `∀ n, n + 0 = n` is `rfl`
because addition recurses on its second argument, and `∀ n, 0 + n = n` is not.

## congrFun

*Definition 0.13 (`congrFun`).* For `f g : A → B`, `h : f = g` and `a : A`, the
term `congrFun h a` has type `f a = g a`. It eliminates an equation between
functions by evaluating at a chosen argument.

```lean
theorem c0_congr {A B : Type} (f g : A → B) (h : f = g)
    (a : A) : f a = g a :=
  congrFun h a
```

This is the hinge of Lawvere's theorem: surjectivity gives an equation between
functions, and `congrFun` evaluates both sides at the diagonal point. The
converse, function extensionality, costs an axiom, and the core proofs do not
need it.

## decide

*Definition 0.14 (Decidability and `decide`).* `P` is _decidable_ when an
algorithm returns a proof of `P` or of its negation. The tactic `decide` proves
a decidable `P` by running that algorithm.

```lean
example : 2 < 5 := by decide
theorem c0_bool_not : ∀ b : Bool, (!b) ≠ b := by decide
```

The second is the workhorse: no boolean equals its own negation. This single
fact drives Cantor, and through Cantor every diagonal result here, by a two-case
check needing no axioms.

*Remark 0.15.* `decide` needs a finite or algorithmically checkable domain.
`∀ b : Bool, …` is decidable; `∀ n : Nat, …` is not, and no tactic changes that.

## What kernel checking means

Lean has two layers. The _elaborator_ turns surface syntax into an explicit
proof term and is large and untrusted; the _kernel_ checks the term has its
claimed type and is a few thousand lines and trusted.

*Definition 0.16 (Kernel checking).* The kernel _checks_ a proof when the trusted
type-checker verifies that the elaborated term has exactly the stated type,
using the fixed rules of the logic and the axioms the term invokes.

A buggy tactic yields a term that either fails to type-check or type-checks, in
which case the theorem holds however it was found. The trusted base is the
kernel plus the axioms.

## The axiom audit

*Definition 0.17 (Axiom audit).* `#print axioms name` prints the axioms a proof
depends on, collected transitively through every lemma used. An empty list means
the result holds in the base logic alone.

The Boolean diagonal results report no axioms; anything routed through the reals
inherits `propext`, `Classical.choice`, and `Quot.sound`. This is the precise
sense in which Chapter 4 calls the diagonal proof cleaner.

*Remark 0.18.* The axiom list is part of a theorem's meaning. Two proofs of one
statement, one axiom-free and one using choice, are different pieces of
knowledge, and this development tracks which is which.

## The engine in five lines

```lean
theorem c0_lawvere {A Y : Type} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g)
    (t : Y → Y) : ∃ y, t y = y :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨f a₀ a₀, (congrFun ha₀ a₀).symm⟩
```

Four moves. Instantiate `hf` at the twisted diagonal. Unpack the `∃` with
`match`, binding `a₀` and the function equation. Offer `f a₀ a₀` as the fixed
point. Evaluate at `a₀` with `congrFun` and flip with `.symm`. Every core proof
below is a variation.

## Cantor, live

Specialize: `Y = Bool` and `t` the negation, fixed-point-free by `c0_bool_not`.

```lean
theorem c0_cantor {A : Type} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  match c0_lawvere f hf (fun b => !b) with
  | ⟨y, hy⟩ => c0_bool_not y hy
```

Suppose `f` names every boolean pattern over its indices. The engine returns a
fixed point of negation, which `c0_bool_not` refutes. Identifying a subset with
its indicator, universality is exactly a point-surjection of `A` onto its power
set. The engine also names the index where the system breaks.

```lean
theorem c0_liar {A : Type} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) :
    ∃ a, f a a = !(f a a) :=
  match hf (fun a => !(f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

Name the twisted diagonal by `a₀` and evaluate there. That is the liar in
Boolean clothing, and in Chapter 3 it becomes the query on which a truthful
model must hallucinate, the prompt no wrapper neutralizes, and the state a truth
probe cannot classify.

# Sets and functions

*Definition 0.19 (Function, evaluation).* `f : A → Y` assigns each `a : A` a
value `f a : Y`. Functions are equal when they agree pointwise; that pointwise
agreement suffices is function extensionality.

*Definition 0.20 (Composition and identity).* For `f : A → B` and `g : B → C`,
`g ∘ f : A → C` is `fun a => g (f a)`, and `id` is `fun a => a`. Composition is
associative with `id` as two-sided unit.

*Definition 0.21 (Injective, surjective, bijective).* `f : A → B` is _injective_
when `f a = f a'` forces `a = a'`, _surjective_ when every `b` is some `f a`,
and _bijective_ when both.

```lean
def c0_Injective {A B : Type} (f : A → B) : Prop :=
  ∀ a a', f a = f a' → a = a'
def c0_Surjective {A B : Type} (f : A → B) : Prop :=
  ∀ b, ∃ a, f a = b
```

*Example 0.22.* Successor on `Nat` is injective, not surjective. `c0_pred` is
surjective, not injective. On finite sets the two coincide, which is pigeonhole;
its failure on infinite sets is what lets the diagonal say what counting cannot.

## Systems and universality

Chapter 1 calls a term of type `A → A → Y` a _system_ and reads it as a naming
scheme: `a` is a name, `f a` is the behavior it denotes. Both arguments range
over `A`, and that coincidence is the entire source of self-reference.

*Definition 0.23 (System).* A _system_ is a function `f : A → A → Y`. Its
_diagonal_ is `a ↦ f a a`.

*Definition 0.24 (Universal, point-surjective).* `f : A → A → Y` is _universal_,
or _point-surjective_, when every `g : A → Y` equals `f a` for some `a`.

This is "the system can talk about itself," made precise. Where this thesis
argues a real system satisfies it, that argument is the substance and the
theorem is a formality. Point-surjectivity is weaker than surjectivity of `A → (A → Y)`:
it asks only that each behavior be hit, which is all the diagonal needs.

*Example 0.25.* No finite system is universal once `|Y| ≥ 2`. With `|A| = n`
there are `n` behaviors `f a` but `|Y|ⁿ` functions `A → Y`. Counting already
forbids it. The diagonal matters because it forbids universality for a reason
surviving into the infinite case, where counting is silent.

*Definition 0.26 (Indicator).* The _indicator_ of `S ⊆ A` is the function
`A → Bool` true exactly on `S`. Subsets of `A` and functions `A → Bool`
correspond bijectively.

```lean
def c0_iszero : Nat → Bool := fun n => n == 0
example : c0_iszero 0 = true := rfl
example : c0_iszero 3 = false := rfl
```

The liar is then the subset containing a name exactly when its behavior excludes
it.

*Definition 0.27 (Section).* A _section_ of `f : A → A → Y` is
`s : (A → Y) → A` with `f (s g) = g` for every `g`. It picks a name for each
behavior.

*Definition 0.28 (Retraction).* A _retraction_ of `s : A → B` is `r : B → A` with
`r (s a) = a`. Its existence makes `s` injective.

```lean
def c0_Retraction {A B : Type} (r : B → A)
    (s : A → B) : Prop := ∀ a, r (s a) = a
```

Every section yields point-surjectivity. The converse needs choice. Lawvere's
theorem holds in section form without choice, which is why the categorical
statement is about sections; at the set level the surjection form suffices.

*Definition 0.29 (Fixed point, fixed-point-free).* A _fixed point_ of `t : Y → Y`
is a `y` with `t y = y`. `t` is _fixed-point-free_ when it has none.

Each impossibility is manufactured by choosing `Y` and a fixed-point-free `t`.
On `Bool` the flip has none; on the real interval the complement has exactly
one, at `1/2`, and that lone fixed point is the content of the analytic theorem:
the forbidden place is the threshold.

*Remark 0.30.* The parallel is exact. The Boolean flip has no fixed point, so on
a naming domain something must be its own negation, which is impossible. The
real complement has one, so on a connected domain something must sit exactly at
the threshold, which calibration forbids. The fixed-point structure of the
outcome map is the dial that switches engines.

# The minimum topology

The analytic half reaches the same boundary object by continuity and
connectedness. The facts below are Mathlib's.

We work over `ℝ`, which is _order-complete_, so closed intervals are connected.
Order-completeness is the analytic counterpart of naming richness: it makes the
sign-change point exist rather than fall through a gap. Over `ℚ` the setup
fails, which is why the theorem is about `ℝ`.

*Definition 0.31 (Open set, topological space).* A _topology_ on `X` is a family
of subsets containing `∅` and `X` and closed under arbitrary unions and finite
intersections. A set is _closed_ when its complement is open. In a metric space
the opens are unions of balls, so both pictures agree.

*Definition 0.32 (Continuity).* `h : X → ℝ` is _continuous_ when preimages of
opens are open; on metric spaces this is the ε-δ condition at every point.

Continuity is the analytic stand-in for the diagonal's structural hypothesis: it
forbids teleporting across the boundary instead of crossing it.

*Definition 0.33 (Connected space).* `X` is _connected_ when it is not the union
of two disjoint nonempty opens; equivalently its only clopen subsets are `∅` and
`X`.

*Example 0.34.* Every interval of `ℝ` is connected. A two-point discrete space is
not: each point is clopen. That distinction is exactly the one between the
engines.

*Remark 0.35.* On subsets of `ℝ`, connected, path-connected, and interval
coincide. The thesis states connectedness because the question spaces of the
safety readings are not intervals but abstract spaces assumed connected, and one
proof then covers every reading.

*Theorem 0.36 (Intermediate value theorem).* _Let `X` be connected and
`h : X → ℝ` continuous. If `h` takes a value below `c` somewhere and above `c`
somewhere, then `h x₀ = c` for some `x₀`._

Nothing here is ours. Every use goes through Mathlib's two-function form
`IsPreconnected.intermediate_value₂`, with the interval case
`isPreconnected_Icc`. Chapter 4 derives the statement above from those two, as
Theorem 4.7.

*Remark 0.37 (Why it is true).* Suppose `h(a) < 0 < h(b)`. Let `S` be the set of
`x ∈ [a, b]` with `h(x) < 0`. It is nonempty and bounded, so it has a supremum
`x₀`. Continuity rules out `h(x₀) < 0`, since points to the right would still be
negative and `x₀` would not bound `S`.

*Remark 0.38.* The two theorems are mirror images. Naming produces an index whose
behavior contradicts itself; connectedness produces a point where a continuous
quantity is pinned to a forbidden value. In both, global richness on the domain
forces a specific bad point. `Foundation.F_04` makes the correspondence formal
rather than analogical.

*Definition 0.39 (Lipschitz map).* `h : X → ℝ` is _`L`-Lipschitz_ when
`dist (h x) (h x') ≤ L · dist x x'`. The constant converts an output gap into a
guaranteed input gap.

The bare theorem gives existence only. Lipschitz control upgrades a crossing
into a band of computed width, and it is why the analytic engine computes what
the diagonal cannot. Chapter 5 is a sustained application.

*Definition 0.40 (Boundary object).* The _boundary object_ is the domain element
a proof forces into existence: for the diagonal an index `a₀` with `f a₀ a₀ = t (f a₀ a₀)`;
for the intermediate value theorem a point `x₀` where the continuous quantity
equals its threshold. In the safety readings it is the query on which a truthful
model must hallucinate, the input no filter can classify, and the state no truth
probe can place.

It is not an artifact of technique. It is one object seen two ways, and it
cannot be designed away, because it is forced by the expressiveness or
connectedness that made the system useful.

# The two engines

_Engine one, the diagonal._ No fixed-point-free `t` admits a universal system.
Feed it `Y` and a fixed-point-free `t`; receive an impossibility. Axiom-free in
Boolean form and entirely non-quantitative.

*Remark 0.41.* Its strength is its limit: it cannot give the width of a failure region
or a scaling rate, because its only hypothesis is a naming property with no
geometry. The separation is clean, with the qualitative claim proved once
unconditionally and the quantitative claim separately where geometry exists.

_Engine two, the intermediate value theorem._ Feed it a connected question
space, a continuous model, and a continuous correctness measure taking both
signs; receive a boundary point. It needs the reals and classical logic, so its
audit is heavier, and in exchange with Lipschitz control it yields band widths,
separations, and rates.

The engines locate the same boundary object and part on everything quantitative.
Chapter 4 is the hinge, and `Foundation.F_04` records the correspondence. Read
with one question in hand: which engine is running, and what may it therefore
conclude? A claim of impossibility suggests the diagonal; a claim carrying a
number is the analytic engine.

_The categorical origin._ Lawvere proved the theorem for cartesian closed
categories, covering sets, computable functions, and the internal logic of a
topos at once, with a section as the hypothesis and composition replacing
application. So Cantor, Gödel, Tarski, Turing, and the trilemmata of Chapter 3
are literal specializations rather than analogies. This thesis stays at the set
level.

*Remark 0.42.* Once the engines are isolated, each result is a paragraph plus a
few lines of code, and the apparent variety of impossibility theorems collapses
to two arguments and a catalogue of instances. A proof that feels long is the
part arguing that a real system satisfies the hypotheses, which is the honest
work.

# How this is verified and built

The project pins `leanprover/lean4:v4.28.0` with Verso pinned to match, so the
live blocks are elaborated by the same Lean that checks the companion libraries.
`lake build` elaborates every chapter module, which is the same as checking
every live proof.

*Remark 0.43.* Building is verifying. A reader who distrusts a proof can clone the
project, run `lake build`, and watch the kernel accept the printed lines. The
first build compiles dependencies and is slow; later builds are incremental.

The chapters split in two. The diagonal chapters are self-contained core Lean
with trivial audits. The analytic results need Mathlib and live in the companion
developments, cited by name: `HallucinationProofs` for the truth boundary,
`Foundation` for the correspondence between engines, `CCHProofs` for the
computability instances, and `ManifoldProofs` for the geometric refinements.
