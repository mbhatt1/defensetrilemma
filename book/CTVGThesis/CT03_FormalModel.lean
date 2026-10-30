import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Formal Model" =>

This chapter fixes the objects that are actually declared in Lean and
checked by the compiler as this document builds. Each structure below is
followed immediately by the code that defines it; nothing is described here
that is not in that code.

# The augmented state

The state of a closed-loop agentic system, at a point in time, is modeled as
a tuple of a latent computational component, a discrete operating mode, a
memory/context/provenance component, a capability component, an
environment component, and the state of a specification monitor (Chapter 4).

```lean
structure CTVGState (X Q M C E RPhi : Type) where
  latent      : X
  mode        : Q
  memory      : M
  capability  : C
  environment : E
  monitor     : RPhi
```

This is a product type and nothing more: the compiler checks that it forms
a valid structure, which is a weaker guarantee than any theorem about it,
and no theorem about `CTVGState` is proved anywhere in this thesis.

# Belief as an interface

A belief is modeled here as an opaque summary type together with the two
operations a monitor needs: reading off a point estimate, and updating on
an observation.

```lean
structure Belief (S Y : Type) where
  estimate : S
  update   : Y → S
```

This is deliberately not a probability measure. A concrete instance
(particle filter, Gaussian belief, finite-support posterior) would refine
`estimate` and `update`; nothing in this thesis provides such an instance,
and no claim here depends on which refinement a future instance would
choose.

# Intervention and composition

An agent proposes an action; a defender's intervention either lets it
through or replaces it.

```lean
inductive Intervention (A : Type) where
  | allow
  | modify (a' : A)
  | sandbox (a' : A)
  | reducePrivilege (a' : A)
  | askHuman
  | deny
  | fallback

def compose {A : Type} (proposed : A) : Intervention A → A
  | .allow              => proposed
  | .modify a'          => a'
  | .sandbox a'         => a'
  | .reducePrivilege a' => a'
  | .askHuman           => proposed
  | .deny               => proposed
  | .fallback           => proposed
```

`compose` is total and type-checks; that is the entire content of this
section. The three cases that currently fall through to `proposed`
(`askHuman`, `deny`, `fallback`) do so because no distinguished "safe
default" action has been fixed at this level of generality — fixing one
would require committing to a concrete `Action` type, which this chapter
does not do.

# Capability ordering

Capability sets are given a partial order: `c1 ≤ c2` means every action
`c1` allows, `c2` also allows.

```lean
structure CapabilitySet (Action : Type) where
  executable : Action → Bool

def CapabilitySet.le {Action : Type} (c1 c2 : CapabilitySet Action) : Prop :=
  ∀ a, c1.executable a = true → c2.executable a = true

instance {Action : Type} : LE (CapabilitySet Action) := ⟨CapabilitySet.le⟩
```

This ordering is what Chapter 5's theorem is stated against. It is a
`def` and an `instance`, checked for type-correctness by the compiler; the
theorem that gives this ordering its content is proved separately, in
Chapter 5, and is not restated here.
