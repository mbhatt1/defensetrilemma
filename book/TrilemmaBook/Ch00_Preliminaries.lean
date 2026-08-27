import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "Preliminaries" =>

This book proves that certain things are impossible. Not hard, not unsolved,
impossible: a truthful and calibrated and covering language model, a prompt
filter that stops every injection, a probe that reads the truth off the inside
of a network. The proofs are short. What takes work is understanding what they
say and trusting that they are correct, and both of those are the subject of
this chapter.

Two habits make the rest of the book readable. The first is reading a Lean 4
proof as mathematics rather than as software. A Lean proof of a theorem is a
finite object that a small program, the kernel, can check for you, and once you
learn to read the handful of constructs this book uses you will find the proofs
shorter and more honest than their prose counterparts. The second habit is
keeping two pictures in mind at once. One picture is combinatorial: a system
that can name its own behaviors cannot be everywhere consistent, because the
behavior that disagrees with each name at that name is itself a behavior. The
other picture is geometric: a continuous quantity that is negative somewhere and
positive somewhere else is zero in between, and the zero is a place the system
cannot avoid. The first picture is the diagonal. The second is the intermediate
value theorem. Every impossibility in this book is one of these two arguments
wearing a costume.

You do not need prior Lean, and you do not need graduate topology. You need
comfort with functions and sets, a first course in logic, and willingness to
read a five-line proof slowly. This chapter supplies the rest. It has five
parts: how to read the Lean in this book, the set-and-function language the
diagonal engine speaks, the small amount of topology the analytic engine needs,
a preview of the two engines and where each chapter sits, and finally how the
book is built and checked so that you can rerun the verification yourself.

A note on how to use this chapter. If you already read Lean, skim the first part
for the specific idioms this book leans on, `congrFun` and `match` on an
existential above all, and spend your time on the two-engines roadmap. If you
know the mathematics but not the proof assistant, read the first part slowly and
run the code yourself. The chapter is long because it is meant to be the last
time you have to look anything up.

# How to read the Lean 4 in this book

The code blocks in this book are not illustrations of proofs that live elsewhere.
They _are_ the proofs. When the book is built, Lean 4 elaborates each block and
its kernel checks the result, so a block that you can see in the text is a block
that compiled. That is the entire value proposition of writing the book this way,
and it is worth the small investment of learning to read the notation. This
section builds that reading vocabulary from the ground up, using only tiny
self-contained examples. Every live definition here is prefixed `c0_` so that it
cannot clash with the real development.

## Types and terms

Lean is built on _types_. Every well-formed expression, every _term_, has a
type, and the type is checked before the term means anything. You write `e : T`
to assert that the term `e` has type `T`. Some types you will see constantly:
`Nat`, the natural numbers `0, 1, 2, …`; `Bool`, the two-element type with values
`true` and `false`; `Prop`, the type of _propositions_, which we return to below.

**Definition 0.1 (Type and term).** A _type_ is a classification of terms. A
_term_ `e` _has type_ `T`, written `e : T`, when the rules of the language
assign `T` to `e`. Type-checking is the mechanical process of verifying such
assignments.

There is a type of types. `Nat`, `Bool`, and `Prop` are themselves terms, and
their type is a _universe_. The first data universe is written `Type`, so
`Nat : Type` and `Bool : Type`. To avoid a paradox of the kind Chapter 1 studies,
the universes form an infinite hierarchy `Type : Type 1 : Type 2 : …`, and Lean
can often infer the level for you. In this book you will sometimes see `Type _`,
which means "some universe level, please work it out." For a first reading you
may pretend there is a single universe called `Type` and lose nothing.

Above both `Type` and `Prop` sits a common notion, `Sort`. Lean writes
`Prop = Sort 0` and `Type = Sort 1`, and universe-polymorphic definitions quantify
over `Sort u`. You will not need to manipulate `Sort` directly, but seeing it in
a hover or an error message should not alarm you: it is the umbrella under which
propositions and data types both live.

**Example 0.2.** The literal `2` is a term of type `Nat`. The expression
`true` is a term of type `Bool`. The proposition `1 + 1 = 2` is a term of type
`Prop`. Here is the first live block; it asserts that `1 + 1` and `2` are the
same natural number, and its proof is `rfl`, which we explain shortly.

```lean
example : 1 + 1 = 2 := rfl
```

An `example` is an anonymous theorem or definition: Lean checks it and throws
away the name. We use `example` when we want to show that something compiles
without adding a name to the namespace. A named result uses `def` for data and
`theorem` for proofs; the two keywords behave almost identically, and the choice
records intent, whether the thing you defined is a value you will compute with or
a fact you will cite. Some libraries add a `lemma` keyword as a synonym for
`theorem`, but core Lean, which is all the live blocks here use, does not, so this
book writes `theorem` throughout.

## Functions and application

A function from `A` to `B` has type `A → B`. You apply a function by
juxtaposition: if `f : A → B` and `a : A` then `f a : B`. There are no
parentheses around arguments and no commas between them; application is just a
space, and it binds tighter than almost everything else, so `f a + 1` means
`(f a) + 1`.

**Definition 0.3 (Function type).** For types `A` and `B`, the type `A → B` is
the type of functions taking an argument of type `A` and producing a result of
type `B`. Application of `f : A → B` to `a : A` is written `f a` and has type
`B`.

You build a function with a _lambda_, written `fun x => e`. The term
`fun x => e` has type `A → B` when `e : B` under the assumption `x : A`. You can
also define a named function directly, naming the argument to the left of the
colon.

```lean
def c0_double (n : Nat) : Nat := n + n
def c0_double' : Nat → Nat := fun n => n + n
```

These two definitions are the same function written two ways. The first names
its argument before the colon; the second is a lambda after it. Both have type
`Nat → Nat`. Application computes in the obvious way, and `rfl` accepts the
computation.

```lean
example : c0_double 3 = 6 := rfl
```

Functions compose, and the identity function does nothing, and these two facts
are worth naming even though they are elementary, because the diagonal argument
is a statement about how a certain composite behaves.

```lean
def c0_id {A : Type} (a : A) : A := a
def c0_comp {A B C : Type} (g : B → C) (f : A → B) : A → C := fun a => g (f a)
example : c0_comp c0_double c0_double 3 = 12 := rfl
```

The composite `c0_comp c0_double c0_double` doubles twice, so at `3` it returns
`12`, and `rfl` confirms the computation. The curly braces around `A B C` mark
them _implicit_: Lean infers those types from the other arguments, so you never
write them at a call site. We return to implicit arguments below.

## Currying and the shape A → A → Y

The arrow associates to the right, so `A → A → Y` means `A → (A → Y)`. A term of
that type is a function that takes one `A` and returns a function `A → Y`.
Feeding it a second `A` then produces a `Y`. This is _currying_: a function of
two arguments presented as a function returning a function. The book's central
object has exactly this shape, so it pays to be fluent with it.

**Definition 0.4 (Currying).** A function of two arguments, taking `a : A` and
`b : A` to a value in `Y`, is represented in curried form as a term
`f : A → A → Y`. Then `f a : A → Y` is the result of supplying only the first
argument, and `f a b : Y` supplies both.

Read `f a` as a whole: it is a function, the _behavior indexed by_ `a`. Read
`f a b` as that behavior evaluated at `b`. The two readings are the same term
grouped differently, since `f a b` parses as `(f a) b`. Application associates to
the left, exactly opposite to the arrow, and the two conventions fit together so
that currying is invisible: you write `f a b` and never think about the
intermediate function `f a` unless you want to.

```lean
def c0_add : Nat → Nat → Nat := fun a b => a + b
example : c0_add 2 3 = 5 := rfl
```

**Example 0.5.** Take `A = Nat` and `Y = Bool` and let `f n m` say whether `n`
divides evenly into a fixed schedule at slot `m`. Then `f n` is the whole
schedule of behavior `n`, a function `Nat → Bool`, and `f n n` is what behavior
`n` does at its own index. That last value, the behavior applied to its own
name, is the _diagonal_, and Chapter 1 shows it is where self-referential
systems break. The coincidence that makes it possible is that both arguments of
`f` range over the same set, so a name is also a legal input.

## ∀ and ∃

Logic lives inside the type system. A proposition is a term of type `Prop`, and a
_proof_ of a proposition `P` is a term of type `P`. To prove `P` is to construct
a term whose type is `P`. This is the propositions-as-types principle, and it is
why proofs in Lean look like programs: they are.

There is one asymmetry between `Prop` and `Type` that the trust story quietly
relies on. Propositions are _proof-irrelevant_: any two proofs of the same
proposition are treated as definitionally equal, because for a proposition we care
that it holds, not which term witnesses it. Data types are not like this; `0` and
`1` are genuinely different terms of `Nat`. Proof irrelevance is why a theorem's
content is its statement and its axiom dependencies, never the particular proof
term the elaborator happened to build, and it is why two different-looking proofs
of the same lemma are interchangeable wherever that lemma is cited.

The universal quantifier `∀ x : A, P x` is a _dependent function type_. A proof
of it is a function that, given any `a : A`, returns a proof of `P a`. So you
prove a `∀` the same way you write a function: with a lambda.

**Definition 0.6 (Universal quantifier).** `∀ x : A, P x` is the type of proofs
that `P a` holds for every `a : A`. A term of this type is a function sending
each `a : A` to a proof of `P a`.

```lean
theorem c0_forall_le : ∀ n : Nat, n ≤ n := fun n => Nat.le_refl n
```

Given `h : ∀ x : A, P x` and a particular `a : A`, the application `h a` is a
proof of `P a`. Universal instantiation is function application. This one fact
removes most of the mystery from the proofs ahead: when a proof "applies the
hypothesis to `a₀`," it is literally writing `h a₀`.

The existential quantifier `∃ x : A, P x` is the dual. A proof is a _pair_: a
witness `a : A` together with a proof of `P a`. You build the pair with angle
brackets, `⟨a, h⟩`, the _anonymous constructor_.

**Definition 0.7 (Existential quantifier).** `∃ x : A, P x` is the type of
proofs that some `a : A` satisfies `P`. A term of this type is a pair `⟨a, h⟩`
where `a : A` is the witness and `h : P a` is a proof for that witness.

```lean
theorem c0_exists_zero : ∃ n : Nat, n = 0 := ⟨0, rfl⟩
```

To _use_ an existential you take it apart, which is what `match` does. If
`h : ∃ x, P x`, then `match h with | ⟨a, ha⟩ => …` binds `a` to some witness and
`ha` to the accompanying proof, and you continue in that context. Building an
existential is packing a pair; using one is unpacking it. The Lawvere proof in
Chapter 1 does exactly one of each, and once you see that, the proof is no
longer mysterious.

Implication is a special case of the function arrow. A proof of `P → Q` is a
function turning a proof of `P` into a proof of `Q`, so you apply it the same
way you apply any function.

```lean
theorem c0_imp {p q : Prop} (h : p → q) (hp : p) : q := h hp
```

Here `{p q : Prop}` are _implicit arguments_: Lean infers them from context, and
you do not pass them explicitly. Explicit arguments use round parentheses,
implicit ones use curly braces. When you read a theorem statement, treat the
curly-brace binders as "for any types or values of this shape, inferred
silently." Almost every theorem in this book takes its ambient types `A`, `Y`,
`Q` implicitly, which is why the statements look like they are about specific
sets when they are in fact about all of them.

## Negation, disjunction, and the empty proposition

Two further logical connectives complete the vocabulary the proofs use. The
first is negation. In Lean `¬ P` is definitionally `P → False`, where `False` is
the proposition with no proof at all. To prove `¬ P` you assume a proof of `P`
and derive a proof of `False`, which is to say you show the assumption was
impossible.

**Definition 0.8 (Negation and the empty proposition).** `False` is the
proposition with no constructors, hence no proof. For a proposition `P`, the
negation `¬ P` is defined as `P → False`. From a proof of `False` one may
conclude anything, by the eliminator `False.elim`.

```lean
theorem c0_not_false : ¬ False := fun h => h
theorem c0_ex_falso {p : Prop} (h : False) : p := False.elim h
```

The first says `¬ False` holds, since `¬ False` is `False → False` and the
identity function inhabits it. The second is the principle of explosion: from a
contradiction, everything follows. Inequality is negation of equality: `a ≠ b` is
notation for `¬ (a = b)`, that is `a = b → False`. So to use a hypothesis
`h : a ≠ b` you feed it a proof of `a = b` and receive `False`. Watch for this in
the contrapositive results, where the whole proof is "produce the equality the
hypothesis forbids, hand it over, and collect the contradiction."

The second connective is disjunction. `P ∨ Q` has two constructors, `Or.inl` for
a proof of the left side and `Or.inr` for a proof of the right, and you use a
disjunction by matching on which side holds.

**Definition 0.9 (Disjunction).** `P ∨ Q` is proved by `Or.inl` applied to a
proof of `P`, or by `Or.inr` applied to a proof of `Q`. It is used by case
analysis: a proof of `P ∨ Q` splits into the case where `P` holds and the case
where `Q` holds.

```lean
example : (1 = 1) ∨ (2 = 3) := Or.inl rfl

theorem c0_or_comm {p q : Prop} (h : p ∨ q) : q ∨ p :=
  match h with
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

The first line proves a disjunction by supplying its true left half. The second
swaps the two sides: match on which disjunct holds, then rebuild the disjunction
with the sides exchanged. Conjunction `P ∧ Q`, which we meet again with
structures, is the dual, built from two proofs and used by projecting out each.

## Structures

A _structure_ bundles several fields into one type. It is the tool for packaging
a mathematical object together with the data and hypotheses that define it. You
declare the fields, and Lean gives you a constructor and one projection per
field.

**Definition 0.10 (Structure).** A structure is a type whose terms are tuples of
named fields. Declaring it produces a constructor that takes the fields and
returns a term, and projections that recover each field from a term.

```lean
structure c0_Point where
  x : Nat
  y : Nat

def c0_origin : c0_Point := { x := 0, y := 0 }
def c0_origin' : c0_Point := ⟨0, 0⟩
example : c0_origin.x = 0 := rfl
```

The two definitions of the origin are equal; the first names its fields, the
second uses the anonymous constructor `⟨0, 0⟩`, filling fields in order. The
projection `c0_origin.x` recovers the first field. The same anonymous-constructor
notation `⟨…⟩` that builds a structure also builds an `∃` proof and an `And`
proof, because all three are, under the hood, structures with fields. That is why
one bracket notation covers packing a witness with its proof, packing two proofs
of a conjunction, and packing two coordinates.

```lean
theorem c0_and_comm {p q : Prop} (h : p ∧ q) : q ∧ p :=
  match h with
  | ⟨hp, hq⟩ => ⟨hq, hp⟩
```

The conjunction `p ∧ q` is a structure with two fields, a proof of `p` and a
proof of `q`. To prove `q ∧ p` we take the input apart with `match`, naming the
two proofs `hp` and `hq`, then repack them in the other order. Read the proof out
loud and it is exactly the mathematics: "a proof of `p` and `q` gives a proof of
`p` and a proof of `q`, so it gives a proof of `q` and `p`."

## Inductive types, up close

Structures, `Nat`, `Bool`, `And`, `Or`, and `Exists` are all instances of one
mechanism: the _inductive type_. An inductive type is declared by listing its
constructors, the primitive ways to build a term, and Lean then generates a
recursor that says these are the _only_ ways, which is what lets `match` be
exhaustive. Understanding this one mechanism demystifies all the notation above
at once.

**Definition 0.11 (Inductive type).** An inductive type is a type specified by a
finite list of constructors. Each constructor is a function into the type being
defined. The type contains exactly the terms built by finitely many applications
of its constructors, and pattern matching branches on which constructor produced
a given term.

```lean
inductive c0_Nat where
  | zero : c0_Nat
  | succ : c0_Nat → c0_Nat
```

This is the natural numbers in miniature: a term is `zero`, or `succ` of a
smaller term, and nothing else, which is why `match` on `Nat` needs only the two
cases `0` and `n + 1`. A structure is the special case of an inductive type with
a single constructor, and a proposition like `And` is a structure landing in
`Prop`.

```lean
structure c0_And (p q : Prop) : Prop where
  intro ::
  left : p
  right : q
```

The existential is an inductive type whose one constructor is genuinely
dependent: it packages an element and a proof about _that specific_ element.

```lean
inductive c0_Exists {A : Type} (P : A → Prop) : Prop where
  | intro : (a : A) → P a → c0_Exists P
```

Reading these declarations, you can see why `⟨a, h⟩` builds an `Exists`: it is
the `intro` constructor applied to a witness and a proof, and the anonymous
bracket just spares you writing the constructor name. The same reading explains
why `match` recovers the pieces: the recursor lets you assume a term came from
`intro` and expose its two arguments. Nothing about the diagonal proof is special
notation; it is constructors in and pattern matches out.

## Term-mode proofs, and a word on tactics

A _term-mode_ proof writes the proof term directly, as we have been doing:
`fun n => rfl`, `⟨0, rfl⟩`, the `match` above. Lean also has a _tactic_ mode,
entered with `by`, where you build the proof by issuing instructions that
manipulate a goal. This book prefers term mode for the core arguments, because a
term-mode proof of a five-line theorem is itself about five lines and every
symbol is visible. Tactics appear only for small decidable facts, where a single
tactic settles the goal and writing the term by hand would obscure rather than
reveal.

**Remark 0.12.** Term mode and tactic mode produce the same kind of object. A
tactic block is elaborated into a proof term, and it is that term the kernel
checks. There is no second, weaker standard of proof for tactic mode. When you
see `by decide` you are seeing an instruction that _generates_ a proof term; the
term, not the instruction, is what is trusted. A tactic that produced a wrong
term would simply fail to type-check, and you would get an error rather than a
false theorem.

## match and pattern matching

`match` inspects a term of an inductive type and branches on its shape, binding
the pieces. It works on data and on proofs alike, since both are terms of
inductive types. On `Nat` the shapes are `0` and `n + 1` (successor); on a pair
the single shape is `⟨a, b⟩`; on `Bool` the shapes are `true` and `false`.

```lean
def c0_pred : Nat → Nat
  | 0 => 0
  | n + 1 => n
```

This defines the predecessor by cases on the shape of the input, with no separate
`match` keyword because a definition can pattern-match directly on its arguments.
The first line handles zero, the second handles a successor and names the
predecessor `n`. Pattern matching is also how the proofs in this book use their
hypotheses: `match hf (…) with | ⟨a₀, ha₀⟩ => …` is the standard move for pulling
a witness `a₀` and its property `ha₀` out of an existential produced by a
surjectivity assumption.

## Dot notation and namespaces

Lean groups definitions into _namespaces_, and a definition `Foo.bar` can be
called on a term `x : Foo` as `x.bar`. This _dot notation_ is why you see
`h.symm` and `h.trans` and `Or.inl`: `h.symm` means `Eq.symm h`, applying the
symmetry-of-equality lemma to `h`, and Lean finds `Eq.symm` because `h`'s type is
an equality. It is a spelling convenience with no logical content, but it makes
proofs read like method chains and it is everywhere in the book.

```lean
theorem c0_symm {A : Type} {a b : A} (h : a = b) : b = a := h.symm
theorem c0_trans {A : Type} {a b c : A} (h1 : a = b) (h2 : b = c) : a = c :=
  h1.trans h2
```

The first flips an equation; the second chains two equations end to end. When the
Lawvere proof writes `(congrFun ha₀ a₀).symm`, it is producing an equality with
`congrFun` and then flipping its orientation with `.symm`, two moves you have now
seen in isolation.

## rfl and definitional equality

`rfl` is the proof that a thing equals itself. It succeeds whenever the two sides
are equal _by computation_, or definitionally: Lean reduces both sides as far as
the definitions allow and checks that the results are identical. So `1 + 1 = 2`
is `rfl` because `1 + 1` computes to `2`, and `c0_double 3 = 6` is `rfl` because
the definition of `c0_double` unfolds and the arithmetic runs. When two
expressions are equal but not by pure computation, `rfl` is not enough and you
reason about the equality explicitly, which is where the next construct enters.

Definitional equality is stronger than it first looks and also has a hard limit.
It will run any amount of finite computation, so a claim like
`c0_pred (c0_double 4) = 7` is `rfl`. It will not prove a statement quantified
over all inputs, because that is not a single computation: `∀ n, n + 0 = n` is
`rfl`-provable in core Lean because addition recurses on its second argument, but
`∀ n, 0 + n = n` is not, and the difference is a genuine one about how the
definitions unfold, not a matter of notation.

## congrFun and equality of functions

The single most important library function in this book's core is `congrFun`. It
says that equal functions are equal at every point. Given a proof `h : f = g`
that two functions are equal, and a point `a`, the term `congrFun h a` is a proof
that `f a = g a`.

**Definition 0.13 (`congrFun`).** For `f g : A → B` and `h : f = g` and `a : A`,
the term `congrFun h a` has type `f a = g a`. It is the elimination principle for
an equation between functions: from the functions being equal, conclude their
values agree at any chosen argument.

```lean
theorem c0_congr {A B : Type} (f g : A → B) (h : f = g) (a : A) : f a = g a :=
  congrFun h a
```

This one step is the hinge of Lawvere's theorem. Surjectivity hands you an index
`a₀` whose behavior `f a₀` equals a function you designed. That is an equation
between functions. To extract a contradiction you evaluate both sides at `a₀`,
and `congrFun` is exactly "evaluate both sides at `a₀`." Watch for it in the
three-line proof at the start of Chapter 1; nothing else is going on.

The reverse direction, concluding `f = g` from agreement at every point, is
function extensionality. It is available in Lean but is not free: it uses an
axiom, and the axiom audit below flags it when it is used. The core diagonal
proofs do not need it, which is part of why they audit so cleanly. Keep the
asymmetry in mind: going from `f = g` to pointwise agreement is `congrFun` and
costs nothing, while going the other way costs an axiom.

## decide and decidable propositions

Some propositions can be settled by a finite computation. Whether a specific
natural number is less than another, whether two booleans are equal, whether a
statement holds for all booleans: each reduces to running a decision procedure
and reading off the answer. Lean formalizes this with the `Decidable` type class,
and the tactic `decide` proves a goal by running the procedure and checking that
it returns the affirmative result.

**Definition 0.14 (Decidability and `decide`).** A proposition `P` is
_decidable_ when there is an algorithm returning a proof of `P` or a proof of its
negation. The tactic `decide` proves a decidable `P` by evaluating that algorithm
and confirming the affirmative result.

```lean
example : 2 < 5 := by decide
theorem c0_bool_not : ∀ b : Bool, (!b) ≠ b := by decide
```

The second line is the workhorse for the Boolean flip. It states that no boolean
equals its own negation, and `decide` proves it by checking both cases, `true`
and `false`. This is the fixed-point-free fact that turns Lawvere's theorem into
Cantor's, and through Cantor's into every diagonal impossibility in the book.
Because `decide` on booleans reduces to a finite check with no axioms, results
proved this way carry the cleanest possible trust story.

**Remark 0.15.** `decide` only applies when the proposition ranges over
something finite or otherwise algorithmically checkable. You cannot `decide` a
statement quantified over all natural numbers, because there is no finite check.
The book uses `decide` exactly where the domain is `Bool` or a small finite type,
and reasons by hand everywhere else. The quantifier `∀ b : Bool, …` is decidable
because `Bool` has two elements; the quantifier `∀ n : Nat, …` is not, and no
tactic can change that.

## What "the kernel checks it" means

Lean has two layers. The _elaborator_ is a large, sophisticated program that
turns the surface syntax you write, with its implicit arguments, tactics, and
notation, into a fully explicit proof term. The _kernel_ is a small program, a
few thousand lines, whose only job is to check that a fully explicit term has the
type it claims. The elaborator is convenient but not trusted; the kernel is
trusted but simple. A proof is accepted only when the kernel, reading the final
term, agrees that its type is the theorem statement.

**Definition 0.16 (Kernel checking).** To say the kernel _checks_ a proof is to
say the small trusted type-checker has verified that the elaborated proof term
has exactly the stated type, using only the fixed rules of the logic and any
axioms the term explicitly invokes.

This division is why machine-checked mathematics is trustworthy without trusting
the whole system. A bug in the elaborator, a tactic that does the wrong thing, a
misapplied piece of automation: all of these produce a term that either fails to
type-check, in which case you get an error and no theorem, or type-checks
correctly, in which case the theorem is true regardless of how the term was
found. The elaborator can be as clever and as buggy as it likes; the kernel is
the referee, and the referee is small enough to audit. The trusted base is the
kernel plus the axioms, and nothing else, which is a far smaller thing to trust
than a human reviewer's attention over forty pages of analysis.

## #print axioms and the trust story

Lean's logic includes a few optional axioms, chiefly propositional
extensionality, quotient soundness, and the axiom of choice. Anything proved
without them stands on the bare type theory. Anything that uses them is still a
theorem, but its trust rests on those axioms too, and you should know which. The
command `#print axioms name` reports exactly the axioms a given theorem depends
on, tracing through every lemma it used.

**Definition 0.17 (Axiom audit).** For a proved theorem `name`, the command
`#print axioms name` prints the list of axioms on which the proof depends,
computed by transitively collecting the axioms of every definition and lemma in
the proof term. An empty or trivial list means the result holds in the base logic
alone.

Running `#print axioms` on the Boolean diagonal results reports that they depend
on no axioms beyond the base logic: the proof of `c0_bool_not` and the Cantor
instance built on it are, in the strictest sense the system offers, unconditional.
The analytic results are different. Anything that goes through the real numbers,
continuity, and the intermediate value theorem inherits `propext`,
`Classical.choice`, and `Quot.sound`, because the construction of the reals and
the classical logic used in analysis rest on them. This is not a defect; it is
the honest accounting. When Chapter 4 says the diagonal proof is "cleaner" than
the analytic proof, the axiom audit is the precise sense in which that is true,
and you can reproduce the audit yourself with one command.

**Remark 0.18.** The axiom list is part of the theorem's meaning, not a footnote
to it. Two proofs of the same statement, one axiom-free and one using choice,
are genuinely different pieces of knowledge, and the book keeps track of which is
which. This is a discipline that ordinary mathematical writing cannot easily
maintain, and it is one of the concrete payoffs of doing the work in Lean. When
you finish a chapter, running the audit on its main theorem is the fastest way to
see what the result really cost.

## A worked preview: the diagonal in five lines

You now have every construct the core engine uses. To prove it, here is the
Lawvere fixed-point theorem, reproduced with a `c0_` name so it stands on its own
in this chapter. Read it as a test of the vocabulary just built.

```lean
theorem c0_lawvere {A Y : Type} (f : A → A → Y)
    (hf : ∀ g : A → Y, ∃ a, f a = g) (t : Y → Y) : ∃ y, t y = y :=
  match hf (fun a => t (f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨f a₀ a₀, (congrFun ha₀ a₀).symm⟩
```

Walk through it with the definitions in hand. The hypothesis `hf` is a `∀` over
functions `A → Y`, so `hf (fun a => t (f a a))` is universal instantiation,
function application, at the specific function `a ↦ t (f a a)`. Its type is an
`∃`, so we take it apart with `match`, binding a witness `a₀` and a proof
`ha₀ : f a₀ = (fun a => t (f a a))`, an equation between functions. We must
produce a fixed point of `t`, an `∃ y, t y = y`, so we pack a pair: the witness
is `f a₀ a₀`, and the proof obligation is `t (f a₀ a₀) = f a₀ a₀`. Now
`congrFun ha₀ a₀` evaluates the function equation at `a₀`, giving
`f a₀ a₀ = t (f a₀ a₀)`, and `.symm` flips the equation to the orientation the
goal wants. That is the whole proof: instantiate, unpack, evaluate at the
diagonal point, repack. If you can read those five lines, you can read every core
proof in this book, because they are all variations on this one.

## From the engine to Cantor, live

To see the engine do work rather than sit as an abstraction, specialize it. Take
`Y = Bool` and `t` the negation `(!·)`, whose fixed-point-freeness is
`c0_bool_not`. Feed the two into the engine and universality collapses outright.

```lean
theorem c0_cantor {A : Type} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : False :=
  match c0_lawvere f hf (fun b => !b) with
  | ⟨y, hy⟩ => c0_bool_not y hy
```

Read the proof as an accusation and a rebuttal. Suppose `f` is universal, a
system that names every boolean pattern over its own indices. The engine
`c0_lawvere` then hands us a fixed point `y` of negation, a boolean with
`(!y) = y`, packaged as `⟨y, hy⟩`. The rebuttal is `c0_bool_not y`, which is a
proof that `(!y) ≠ y`, that is a function from `(!y) = y` to `False`. Applying it
to `hy` produces `False`, so the assumption of universality was impossible. This
is Cantor's theorem in the reading of the previous section: identify a subset of
`A` with its indicator `A → Bool`, and universality is exactly a point-surjection
of `A` onto its power set, which cannot exist.

The engine also names the exact index on which the system breaks, not merely that
one exists. That index is the liar, and producing it takes the same four moves
with the negation baked into the diagonal from the start.

```lean
theorem c0_liar {A : Type} (f : A → A → Bool)
    (hf : ∀ g : A → Bool, ∃ a, f a = g) : ∃ a, f a a = !(f a a) :=
  match hf (fun a => !(f a a)) with
  | ⟨a₀, ha₀⟩ => ⟨a₀, congrFun ha₀ a₀⟩
```

Here we do not even invoke `c0_lawvere`; we run its guts directly. Name the
twisted diagonal `a ↦ !(f a a)` by some `a₀`, then evaluate the naming equation
at `a₀` with `congrFun` to get `f a₀ a₀ = !(f a₀ a₀)`. The index `a₀` is a
behavior whose self-application equals its own negation, which is the liar
sentence in Boolean clothing. Hold onto this construction. In Chapter 3 the same
`a₀` becomes, under three readings, the query on which a truthful model must
hallucinate, the prompt no wrapper can neutralize, and the state a truth probe
cannot classify. They are one index seen three ways.

## Running the blocks yourself, and reading errors

A practical note, since the blocks are meant to be run. Drop any block above into
a file whose first line is nothing more than a comment, open it in an editor with
the Lean extension, and the same elaboration the book performs happens as you
type. There are no imports to add for the core-Lean blocks; that is what "core
Lean only" buys you. When a proof is wrong, the error appears at the point where
the kernel's expectation and your term diverge, and it names the expected type and
the type it actually found. Learning to read that mismatch is most of learning
Lean: the expected type is the goal you still owe, and the found type is what your
term delivered. A proof that goes through produces no message at all, which is the
quiet the rest of this book runs on.

# Sets and functions

The diagonal engine is stated in the language of sets and functions, and it uses
a small, fixed vocabulary. This section fixes that vocabulary and the notation.
Nothing here is deep. The point is that a few plain notions, stated carefully,
carry the entire combinatorial half of the book.

## Functions, domains, codomains

A function `f : A → Y` assigns to each element of its _domain_ `A` a single
element of its _codomain_ `Y`. We do not distinguish "function" from "map"; they
mean the same thing. The set of functions from `A` to `Y` is itself an object,
which we write `A → Y`, matching the Lean type. When we speak of "all behaviors
over `A` valued in `Y`," we mean all elements of `A → Y`.

**Definition 0.19 (Function, evaluation).** A function `f : A → Y` is a rule
assigning to each `a : A` a value `f a : Y`, called the evaluation of `f` at `a`.
Two functions `f, g : A → Y` are _equal_ when `f a = g a` for every `a : A`; the
principle that this pointwise agreement suffices for equality is function
extensionality.

## Composition, identity, and the classes of map

Two functions compose when the codomain of one is the domain of the next, and the
identity map is neutral for composition. These give the language for the
structural properties a map can have.

**Definition 0.20 (Composition and identity).** For `f : A → B` and `g : B → C`,
the composite `g ∘ f : A → C` is `fun a => g (f a)`. The identity `id : A → A` is
`fun a => a`. Composition is associative, and identity is a two-sided unit for it.

A map can be one-to-one, or onto, or both, and each property has a place in the
arguments ahead.

**Definition 0.21 (Injective, surjective, bijective).** A function `f : A → B` is
_injective_ when `f a = f a'` forces `a = a'`; _surjective_ when every `b : B` is
`f a` for some `a`; _bijective_ when it is both. In symbols, injective is
`∀ a a', f a = f a' → a = a'` and surjective is `∀ b, ∃ a, f a = b`.

```lean
def c0_Injective {A B : Type} (f : A → B) : Prop := ∀ a a', f a = f a' → a = a'
def c0_Surjective {A B : Type} (f : A → B) : Prop := ∀ b, ∃ a, f a = b
```

**Example 0.22.** The successor `fun n => n + 1` on `Nat` is injective but not
surjective, since nothing maps to `0`. The predecessor `c0_pred` is surjective but
not injective, since `0` and `1` both map to `0`. On a finite set the two
properties coincide, which is the pigeonhole principle, and it is exactly this
coincidence that fails for infinite sets and lets the diagonal say something
counting cannot.

## Currying, again, as a naming scheme

The object at the center of the diagonal arguments is a function of the curried
type `A → A → Y`. Chapter 1 calls such a thing a _system_, and reads it as a
naming scheme: each `a : A` is a _name_ or _index_, and `f a : A → Y` is the
_behavior_ that the name `a` denotes. Both arguments range over the same set `A`,
and that coincidence is the whole source of self-reference. A name can be handed
to a behavior, including the behavior it itself denotes, and the value `f a a` is
the behavior at its own name.

**Definition 0.23 (System and diagonal).** A _system_ is a function
`f : A → A → Y`. Its _diagonal_ is the function `A → Y` given by `a ↦ f a a`,
sending each index to the value of its own behavior at itself.

The diagonal is where the argument acts. Given any transformation `t : Y → Y` of
outcomes, the _diagonal behavior twisted by_ `t` is `a ↦ t (f a a)`. It is a
perfectly good function `A → Y`, so if the system names every function, it names
this one, and the name it assigns is where the contradiction lands.

## Point-surjectivity and universality

The diagonal arguments need surjectivity one level up, about the curried system
rather than a plain map.

**Definition 0.24 (Point-surjectivity, universality).** A system
`f : A → A → Y` is _point-surjective_, or _universal_, when every function
`g : A → Y` is named: for all `g` there exists `a : A` with `f a = g`. In symbols,
`∀ g : A → Y, ∃ a, f a = g`.

Read this as a precise form of "the system can talk about itself." A
proof-checker that accepts the code of any predicate on proofs, a model that can
be prompted to imitate any behavior over prompts, a representation that encodes
any pattern over its own states: each asserts point-surjectivity for the right
`A` and `Y`. The hypothesis is strong, and where the book argues that a real
system satisfies it, that argument is the substance. The theorem itself, given
the hypothesis, is a formality, which is the point of isolating the engine.

Point-surjectivity is genuinely weaker than the honest surjectivity of a map
`A → (A → Y)`, and the difference is where the subtlety of the categorical
version lives. It asks only that each behavior be _hit_, not that the hitting be
done by a single well-behaved map, and that is all the diagonal needs.

**Example 0.25.** No finite system is universal once `Y` has at least two
elements. If `A` has `n` elements there are `n` names, hence at most `n`
behaviors `f a`, but there are `|Y|ⁿ` functions `A → Y`, and `n < |Y|ⁿ` whenever
`|Y| ≥ 2`. Counting already forbids universality in the finite case. The diagonal
matters because it forbids universality for a reason that survives when `A` is
infinite and counting has nothing to say.

## Subsets, indicators, and the power set

A subset `S` of `A` is the same data as its _indicator_ function `A → Bool`,
sending an element to `true` exactly when it lies in `S`. So the set of all
subsets of `A`, the power set, is the function set `A → Bool`. This identification
is why Cantor's theorem, that no set surjects onto its power set, is the special
case `Y = Bool` of the diagonal.

**Definition 0.26 (Indicator).** The _indicator_ of a subset `S ⊆ A` is the
function `A → Bool` returning `true` on `S` and `false` elsewhere. Subsets of `A`
and functions `A → Bool` are in bijection under this correspondence.

```lean
def c0_iszero : Nat → Bool := fun n => n == 0
example : c0_iszero 0 = true := rfl
example : c0_iszero 3 = false := rfl
```

The map `c0_iszero` is the indicator of the subset `{0}` of `Nat`. Under the
correspondence, universality of a system `A → A → Bool` is precisely a
point-surjection of `A` onto its power set, and the liar of Chapter 1 is the
subset that contains a name exactly when its behavior excludes it.

## Sections and retractions

Surjectivity says every `g` has a name. A stronger, constructive statement gives
you the name explicitly, as a function, and its mirror image records when a map
can be undone.

**Definition 0.27 (Section).** A _section_ of a system `f : A → A → Y` is a
function `s : (A → Y) → A` such that `f (s g) = g` for every `g : A → Y`. A
section picks, for each behavior `g`, a name `s g` that denotes it.

**Definition 0.28 (Retraction).** A _retraction_ of a map `s : A → B` is a map
`r : B → A` with `r (s a) = a` for all `a`. If a retraction exists, `s` is
injective, and `A` is a "retract" of `B`.

```lean
def c0_Retraction {A B : Type} (r : B → A) (s : A → B) : Prop := ∀ a, r (s a) = a
```

Every section yields point-surjectivity: given `g`, the element `s g` is a
witness for the existential, since `f (s g) = g`. The converse needs choice, to
select a name for each `g` at once. Lawvere's theorem holds in the section form
without any choice, and that form is the one that transfers verbatim to any
cartesian closed category, which is why the categorical statement is about
sections rather than surjections. For the set-level results the surjection form
is all we need, and Exercise 0.9 asks you to redo the engine with a section and
notice that the proof gets one step shorter.

## Fixed points and fixed-point-free maps

The output side of the engine turns on a single property of a map `t : Y → Y`.

**Definition 0.29 (Fixed point, fixed-point-free).** A _fixed point_ of
`t : Y → Y` is a `y` with `t y = y`. The map `t` is _fixed-point-free_ when it
has none: `t y ≠ y` for all `y`.

Lawvere's theorem says a universal system forces every `t` to have a fixed point.
Contrapositively, a fixed-point-free `t` forbids universality. So each
impossibility in the diagonal half is manufactured by choosing a set of outcomes
`Y` and a fixed-point-free transformation of them. On `Y = Bool` the negation
`(!·)` is fixed-point-free, by `c0_bool_not`, and that single fact drives Cantor,
Rice, Gödel read through the liar, and the AI-safety trilemmata. On the real
interval the complement `y ↦ 1 - y` has one fixed point, at `1/2`, and that lone
fixed point is not a failure of the pattern but the whole content of the analytic
theorem: the forbidden place is the threshold itself.

**Remark 0.30.** The parallel is exact and worth holding onto before Chapter 4
makes it precise. The Boolean flip has no fixed point, so on a domain that can
name its behaviors, something is forced to be its own negation, which is
impossible, and universality dies. The real complement has exactly one fixed
point, so on a connected domain, something is forced to sit exactly at the
threshold, which the calibration hypotheses forbid, and the model dies. Same
shape, two engines, and the fixed-point structure of the outcome map is the dial
that switches between them.

# The minimum topology

The analytic half of the book uses continuity and connectedness to reach the same
boundary object the diagonal reaches by self-reference. This section states the
few topological facts involved, at the level of generality the book actually
needs, which is modest. The live proofs of these facts are in the companion
Mathlib development, not in this chapter, because they need the library; here we
state them carefully in prose and in backticked notation so that Chapter 4 reads
smoothly.

## The real line and intervals

We work over the real numbers `ℝ` with their usual order and distance. The closed
interval from `a` to `b` is `[a, b] = { x : a ≤ x ∧ x ≤ b }`. The two facts about
`ℝ` we lean on are that it is _order-complete_, every bounded nonempty set has a
least upper bound, and that closed intervals are _connected_, which is a
consequence of completeness. Order-completeness is the analytic counterpart of
the naming richness the diagonal needs: it is the property that makes "the place
where the sign changes" actually exist rather than fall through a gap in the line.
Over the rationals the same setup fails, because a sign change can straddle an
irrational the rationals do not contain, and this is precisely why the theorem is
a theorem about `ℝ` and not about any ordered field.

## Metric and topological spaces

A _metric space_ is a set with a distance function satisfying the triangle
inequality; a _topological space_ is the more general setting where "open set" is
taken as primitive and distance may be absent. Everything the book needs can be
read in the metric picture, where continuity is the familiar epsilon-delta
statement, but the companion development states results topologically because
that is how Mathlib is organized and because connectedness is cleanest there.

**Definition 0.31 (Open set, topological space).** A _topology_ on a set `X` is a
collection of subsets, the _open sets_, containing the empty set and `X` and
closed under arbitrary unions and finite intersections. A set is _closed_ when
its complement is open. In a metric space the open sets are the unions of open
balls, so the metric and topological pictures agree.

## Continuity

Intuitively a function is continuous when small changes in the input produce
small changes in the output, with no jumps. The book uses continuity in its
standard topological form, which agrees with the epsilon-delta form on metric
spaces.

**Definition 0.32 (Continuity).** A function `h : X → ℝ` from a topological space
`X` to the reals is _continuous_ when the preimage of every open set is open.
Equivalently, for metric spaces, `h` is continuous at `x` when for every `ε > 0`
there is a `δ > 0` such that `dist x x' < δ` implies `dist (h x) (h x') < ε`, and
continuous when it is continuous at every point.

The models in the analytic chapters are assumed continuous as maps from a
question space to a confidence-and-answer space, and correctness is measured by a
continuous signed truth-distance. Continuity is the analytic stand-in for the
structural assumptions of the diagonal side. It is what forbids the model from
teleporting across the boundary instead of crossing it, and everything the
analytic engine concludes is false without it, as Exercise 0.10 makes concrete.

## Connected spaces

Connectedness is the property that a space is not split into two separated pieces.
It is what makes the intermediate value theorem true, and it is the exact
hypothesis that replaces point-surjectivity in the analytic engine.

**Definition 0.33 (Connected space).** A topological space `X` is _connected_
when it cannot be written as the union of two disjoint nonempty open sets.
Equivalently, the only subsets of `X` that are both open and closed are the empty
set and `X` itself. A subset is connected when it is connected as a space with the
subspace topology.

**Example 0.34.** Any interval of `ℝ`, open, closed, or half-open, bounded or
not, is connected. A two-point set with the discrete topology is not connected:
each point is open, and the space splits into two clopen halves. The distinction
is precisely the one between the analytic and combinatorial engines. A connected
question space supports the intermediate value argument; a discrete space of names
supports the diagonal instead, and the discrete core of the analytic result,
mentioned in Chapter 4, is what happens when you try to run the analytic argument
on a disconnected domain and it degrades to counting.

**Remark 0.35.** For subsets of `ℝ`, connected and _path-connected_ coincide, and
both reduce to being an interval, so on the line there is nothing to distinguish.
The reason the book states connectedness rather than "is an interval" is that the
question spaces of the AI-safety readings are not literally intervals; they are
abstract spaces assumed connected, and the intermediate value theorem holds for
all of them uniformly. Stating the weakest sufficient hypothesis is what lets one
proof cover every reading.

## The intermediate value theorem

The one analytic theorem the book truly depends on is the intermediate value
theorem, in the following form.

**Theorem 0.36 (Intermediate value theorem).** _Let `X` be connected and
`h : X → ℝ` continuous. If `h` takes a value below `c` at some point and a value
above `c` at another, then `h` takes the value `c` at some point: there is an
`x₀ ∈ X` with `h x₀ = c`._

The classical special case is `X = [a, b]`: a continuous real function that is
negative at `a` and positive at `b` has a zero somewhere between. The general
form, over an arbitrary connected space, is what the companion development uses,
through Mathlib's connectedness API, and it is the form that makes the AI-safety
statements clean, because the question space is not literally an interval but is
assumed connected.

**Remark 0.37 (Why it is true).** The one-variable proof is worth recalling,
because it shows where completeness enters. Suppose `h(a) < 0 < h(b)`. Let `S` be
the set of `x ∈ [a, b]` with `h(x) < 0`. It is nonempty and bounded, so by
order-completeness it has a least upper bound `x₀`. Continuity rules out
`h(x₀) < 0`, since then points slightly to the right would still be negative and
`x₀` would not be an upper bound, and it rules out `h(x₀) > 0`, since then points
slightly to the left would already be positive and `x₀` would not be least. The
only survivor is `h(x₀) = 0`. The abstract version replaces "least upper bound of
a bounded set" with "connectedness forbids a clopen split," but the moral is the
same: a global completeness or connectedness property forces the crossing point
to exist. This is the exact structural echo of the diagonal, where a global
naming property forced the liar to exist.

**Remark 0.38.** The intermediate value theorem is the mirror image of the
diagonal. There the naming hypothesis produced an index whose behavior
contradicted itself; here connectedness produces a point where a continuous
quantity is pinned to a value its other hypotheses forbid. In both, a global
richness assumption on the domain, universality or connectedness, forces the
existence of a specific bad point, and the bad point is where the impossibility
lives. Chapter 4 records the two theorems as two spellings of one fact, and the
file `Foundation.F_04` in the companion development makes the correspondence a
formal statement rather than an analogy.

## Signed distance, thresholds, and a word on Lipschitz control

The analytic readings measure correctness by a _signed_ quantity, negative on
one side of the truth boundary and positive on the other, so that the boundary is
its zero set. Pairing this with a confidence score that must exceed a threshold
turns the trilemma into a sign-crossing problem the intermediate value theorem
resolves. The bare theorem gives only existence of the crossing. To get numbers,
how wide the ambiguous band is or how far apart the decisive regions must be, you
add a _Lipschitz_ bound.

**Definition 0.39 (Lipschitz map).** A function `h : X → ℝ` on a metric space is
_`L`-Lipschitz_ when `dist (h x) (h x') ≤ L · dist x x'` for all `x, x'`. The
constant `L` bounds how fast the output can change, so it converts a gap in
output values into a guaranteed gap in inputs.

Lipschitz control is what upgrades a qualitative crossing into a quantitative
band, and it is the whole reason the analytic engine can compute things the
diagonal cannot. Chapter 5, on the geometry of attack basins, is a sustained
application of this upgrade, and none of its quantities are visible without it.

## The boundary object

Both engines output a distinguished point of the domain: the liar index on the
diagonal side, the threshold-crossing question on the analytic side. Throughout
the book this is the _boundary object_. It is not an artifact of either proof
technique. It is the same object seen two ways, and the recurring theme is that
you cannot design it away, because it is forced by the very expressiveness or
connectedness that made the system useful in the first place.

**Definition 0.40 (Boundary object).** The _boundary object_ of an impossibility
result is the domain element the proof forces into existence: for the diagonal, an
index `a₀` with `f a₀ a₀ = t (f a₀ a₀)`; for the intermediate value theorem, a
point `x₀` with the continuous quantity equal to its threshold value. In the
AI-safety readings it is, respectively, the query on which a truthful model must
hallucinate, the input no prompt filter can classify, and the state a truth probe
cannot place on either side.

# The two engines: a roadmap

Everything above serves one architecture. There are two proof engines, they
produce the same boundary object, and each chapter of the book is one engine
applied to one system. This section lays out the architecture and says where each
piece lives, so that you can read the rest of the book knowing which engine is
running and what it can and cannot deliver.

## Engine one: the diagonal

The diagonal engine is Lawvere's fixed-point theorem, `c0_lawvere` above, and its
contrapositive, "no fixed-point-free `t` admits a universal system." You feed it a
reading of the outcome set `Y` and a fixed-point-free map `t`, and it returns an
impossibility. The engine is finite in spirit, needs no axioms in its Boolean
form, and gives a witness with no quantitative content: it tells you a bad point
exists, not how many there are, not how hard one is to find, not what it costs an
adversary to reach one.

**Remark 0.41.** The strength of the diagonal is also its limit. It says nothing
metric. It cannot tell you the width of the region where a defense fails, or how
the failure rate scales, because its only hypothesis is a naming property with no
geometry attached. When you want numbers you must change engines. This is not a
weakness to apologize for; it is a clean separation of concerns, with the
qualitative "it is impossible" proved once, unconditionally, and the quantitative
"here is how badly" proved separately where geometry is available.

## Engine two: the intermediate value theorem

The analytic engine is Theorem 0.36. You feed it a connected question space, a
continuous model, and a continuous correctness measure with values of both signs,
and it returns a point on the boundary. It requires the reals and classical
logic, so its axiom audit is heavier than the diagonal's, and in exchange it gives
what the diagonal cannot: once you add Lipschitz control on the maps, the same
argument yields quantities, the width of the ambiguous band, the minimum
separation of the decisive regions, the rate at which the margin shrinks as
calibration tightens. The geometry of attack basins in Chapter 5 is entirely a
refinement of this engine, and none of it is available to the diagonal.

## Where the engines meet, and where they part

The two engines locate the same boundary object, and Chapter 4 is the hinge that
shows this. The Boolean liar `(!·)`, fixed-point-free, and the real complement
`y ↦ 1 - y`, with its single fixed point at the threshold, are the two faces of
one construction, recorded formally in `Foundation.F_04`. They meet at the
boundary object and part on everything quantitative. Read the book with this
question always in hand: which engine is running here, and what is it therefore
allowed to conclude. If the claim is "impossible," suspect the diagonal. If the
claim carries a number, a width, a rate, a probability, it is the analytic engine
and its Lipschitz refinements at work.

## The categorical origin, briefly

The origin of the diagonal engine is worth stating, because the source
explains why one theorem covers so many cases. Lawvere proved his fixed-point
theorem not about sets but about maps in a _cartesian closed category_, a setting
abstract enough to include sets, computable functions, and the internal logic of
a topos all at once. In that setting the hypothesis is stated with a section: a
map `A → Y^A` admitting a right inverse, which is the categorical form of
Definition 0.27. The proof is the same instantiate-and-diagonalize move, with
composition standing in for function application. Because the argument lives at
that level of generality, its instances are not analogies but literal
specializations: Cantor, Gödel, Tarski, Turing, and the trilemmata of Chapter 3
are one theorem read in different categories. This book stays at the set level,
where the surjection form suffices and the code is short, and points to the
categorical statement only to explain why the pattern is not a coincidence.

## Chapter map

Here is the shape of the book, so the preview is concrete.

Chapter 1 states and proves the diagonal engine, `lawvere` and `no_universal`,
in a few lines of core Lean, and extracts the schema every later result
instantiates. Chapter 2 turns the crank on the classical limitative theorems:
Cantor, Rice, Gödel and Tarski through the liar, Turing's halting problem, each
one choice of `Y` and fixed-point-free `t`. Chapter 3 applies the same engine to
recent AI-safety impossibilities, the hallucination trilemma and the
prompt-injection defense trilemma, arguing that the substance is in showing a
real system's verdict is reflective, after which the contradiction is one line.

Chapter 4 is the pivot from logic to analysis. It re-derives the trilemma from
topology, with the intermediate value theorem in the diagonal's role, and marks
exactly where the two engines agree and diverge. Chapter 5 develops the
quantitative side, the geometry of attack basins, which only the analytic engine
supports. Chapter 6 handles approximate bridges, what survives when the
hypotheses hold only up to error. Chapter 7 draws the practical consequences for
deploying language models. Chapter 8 answers the objection that all of this
concerns outputs only, by turning both engines on a probe that reads the middle
of a computation rather than its output.

**Remark 0.42.** The book is short by design, and the shortness is a claim: once
the two engines are isolated, each result is a paragraph of reading plus a few
lines of code, and the apparent variety of impossibility theorems collapses to
two arguments and a catalogue of instances. If at any point a proof feels long,
you are probably reading the part that argues a real system satisfies the
hypotheses, which is honest work, and not the engine, which is always brief.

# How the book is verified and built

The last preliminary is operational. This book is a Lean 4 project, and you can
build it, check every proof, and run the axiom audits yourself. This section says
how, at the level of detail needed to reproduce the verification.

## The toolchain

The project pins Lean 4 at toolchain `leanprover/lean4:v4.28.0`, recorded in the
`lean-toolchain` file, and uses `elan`, Lean's version manager, to select it
automatically when you enter the directory. The book is authored in Verso, Lean's
documentation system, pinned to `v4.28.0` to match, so that the live code blocks
are elaborated by the same Lean that checks the companion proof libraries. Verso
is what lets a code block in the text _be_ a compiled definition rather than a
quotation of one. The dependency set, recorded in `lake-manifest.json`, is Verso
and its own dependencies; the self-contained chapters need nothing else, and in
particular the core-Lean blocks in this chapter compile without Mathlib.

## Building

The build tool is `lake`, Lean's package manager. From the `book` directory,
`lake build` elaborates every chapter module, which is the same as checking every
live proof in the text: if a code block did not compile, the build would fail
there, naming the file and line. To produce the reading editions,
`lake exe trilemmabook` runs the generator in `TrilemmaBookMain.lean`, which emits
a single-page HTML edition and a TeX edition from the one source. The generator is
configured to render the whole table of contents in the sidebar, because the HTML
is deliberately one page: the book is short enough to read straight through, and a
chapter-per-page split would turn every cross-reference into a navigation round
trip.

**Remark 0.43.** Because the live blocks are checked at build time, there is no
separate step to "verify the book." Building it is verifying it. A reader who
distrusts a proof can clone the project, run `lake build`, and watch the kernel
accept the very lines printed in the text. That is a stronger guarantee than a
human referee can give, restricted to exactly the claims stated in code. The
first build downloads and compiles the dependencies and takes a while; later
builds are incremental and touch only what changed.

## The self-contained core and the companion libraries

The chapters split into two kinds. The diagonal chapters, one through four in
their logical parts, are self-contained core Lean: the proofs you read are the
proofs that compile, with no external library, and their axiom audits are trivial.
The analytic results need Mathlib and live in companion developments, cited by
name where they are used: `HallucinationProofs` for the hallucination trilemma
and its boundary lemma, the defense results for the prompt-injection side,
`Foundation` for the correspondence between the engines, `CCHProofs` for the
computability instances, and `ManifoldProofs` for the geometric refinements. The
book reproduces the argument of each cited result in prose and points to the
verified statement, rather than importing the heavy library into the text, which
keeps the text buildable in seconds while the deep results stay checked in their
own libraries.

## Reading the axiom audit

For any theorem in the self-contained core you can confirm the trust story with
`#print axioms name`. On the Boolean diagonal results the report lists no axioms
beyond the base logic, which is the precise meaning of the claim that Cantor's
theorem and its AI-safety descendants are unconditional. On any result routed
through the reals the report lists `propext`, `Classical.choice`, and `Quot.sound`,
the three standard axioms behind classical analysis in Lean. The presence or
absence of that list is not decoration. It is the difference, made checkable,
between a combinatorial impossibility that holds in the bare type theory and an
analytic one that holds given the classical construction of the continuum. Keep
the audit in mind as you read: when two chapters prove nearby statements by
different engines, the axiom lists are how the book records that they are, in a
strong sense, different theorems.

# Exercises

**Exercise 0.1.** Define in core Lean a function `c0_triple : Nat → Nat` that
triples its argument, in both the named-argument style and the lambda style, and
prove `c0_triple 4 = 12` by `rfl`. Explain in one sentence why `rfl` suffices
here, referring to Definition 0.1 and the notion of definitional equality.

**Exercise 0.2.** State and prove, in term mode, that for propositions `p` and
`q`, `p ∧ q → p`. Then state and prove `p → q → p ∧ q`. Identify which of your
proofs packs a structure and which projects one, using the vocabulary of
Definition 0.10.

**Exercise 0.3.** Using only `congrFun` (Definition 0.13), prove that for
`f g : Nat → Nat` with `h : f = g`, one has `f 0 = g 0` and `f 7 = g 7`. Explain
why you cannot prove `f = g` from `f 0 = g 0` alone, and name the principle that
would be needed to go the other direction from agreement at _every_ point.

**Exercise 0.4.** Write the predecessor function `c0_pred` yourself, then prove
`c0_pred 0 = 0` and `c0_pred 5 = 4` by `rfl`. Now explain, without writing code,
why `∀ n, c0_pred (n + 1) = n` is provable by `rfl` for each concrete `n` but
requires a genuine proof, not `rfl`, when stated for all `n` at once.

**Exercise 0.5.** Prove `∀ b : Bool, b && b = b` by `decide`, and then argue why
the analogous statement `∀ n : Nat, n * 1 = n` cannot be proved by `decide`.
State precisely which hypothesis of Definition 0.14 fails for the second, and
connect your answer to Remark 0.15.

**Exercise 0.6.** Re-derive Example 0.25 in detail. For `|A| = n` and `|Y| = 2`,
exhibit a function `A → Y` that is not of the form `f a`, by flipping the diagonal
`f a a`. Then explain in one paragraph why this counting argument, though correct
here, gives the wrong intuition for infinite `A`, and what the diagonal supplies
that counting cannot. Relate the failure of counting to Example 0.22, the
successor map.

**Exercise 0.7.** Give an example of a fixed-point-free map `t : Bool → Bool` and
prove it fixed-point-free by `decide`. Then show that no map `Unit → Unit` is
fixed-point-free, and say in one sentence what this means, via Definition 0.29
and the engine, for a system whose only possible outcome is "accept."

**Exercise 0.8.** For the real complement `t y = 1 - y`, find its unique fixed
point by solving `t y = y`. Relate the answer to the threshold in the analytic
trilemma, and explain why "the map has exactly one fixed point" is the analytic
counterpart of "the Boolean flip has none," referring to Remark 0.30.

**Exercise 0.9.** Prove the section form of the engine in core Lean: given
`f : A → A → Y`, a section `s : (A → Y) → A` with `hs : ∀ g, f (s g) = g`
(Definition 0.27), and any `t : Y → Y`, produce a fixed point of `t`. Compare
your proof to `c0_lawvere` and identify the single step that becomes shorter when
you have a section instead of a mere surjection.

**Exercise 0.10.** Read Theorem 0.36 and construct a counterexample when the
domain is _not_ connected: give a continuous `h` on the two-point discrete space
of Example 0.34 that is negative at one point and positive at the other yet is
never zero. Conclude in one sentence why connectedness is not an optional
convenience in the analytic engine.

**Exercise 0.11.** Run, or describe running, `#print axioms` (Definition 0.17) on
two theorems from later chapters: a Boolean diagonal result and an analytic
result routed through the reals. Predict the two axiom lists before checking, then
explain what the difference tells you about the two theorems as pieces of
knowledge, referring to Remark 0.18.

**Exercise 0.12.** In `c0_lawvere`, the witness `a₀` depends on the choice of
preimage for the twisted diagonal. Argue that if two distinct indices both name
the twisted diagonal, both are boundary objects (Definition 0.40), and that
nothing in the proof selects a canonical one. Relate this non-uniqueness to the
statement in later chapters that the boundary question is not unique.

**Exercise 0.13.** Using Definition 0.21, prove in core Lean that the composite of
two injective functions is injective. Then explain in prose why injectivity is the
retraction-side property (Definition 0.28) and surjectivity the section-side
property, and where each appears in the diagonal argument.

**Exercise 0.14.** (Synthesis.) In one page and without symbols, explain to a
colleague who knows analysis but not logic why the intermediate value theorem and
Cantor's diagonal are, for the purposes of this book, the same argument. Your
explanation should name the domain hypothesis each engine uses, the outcome-map
property each exploits, and the boundary object each produces, and should say
plainly what the analytic engine can compute that the diagonal cannot.
