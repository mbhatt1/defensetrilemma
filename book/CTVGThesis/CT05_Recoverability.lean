import VersoManual
import CTVGThesis.CT03_FormalModel
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Shield, and Capability Monotonicity" =>

This chapter contains the one theorem in this thesis that is a genuine
machine-checked proof rather than a definition, an interface, or a
conjecture.

# The shield interface

A shield checks an agent's proposed action against a hard admissibility
predicate and a separate, second-stage predicate, and substitutes the best
available admissible alternative when the proposal fails either check.

```lean
/-- A shield interface: `hardInvariant` and `valueBound` are left abstract,
so that this structure fixes only the control flow — check, then fall back
to the best admissible alternative — not any concrete safety criterion. -/
structure Shield (Action : Type) where
  hardInvariant : Action → Bool
  valueBound    : Action → Bool
  utility       : Action → Float
  candidates    : List Action

def Shield.admissible {Action : Type} (shield : Shield Action) : List Action :=
  shield.candidates.filter (fun a => shield.hardInvariant a && shield.valueBound a)

def Shield.decide {Action : Type} (shield : Shield Action) (proposed : Action)
    (isProposedAdmissible : Bool) : Action :=
  if isProposedAdmissible then proposed
  else
    let admissible := shield.admissible
    match admissible with
    | []      => proposed  -- no fallback is fixed at this level of generality
    | a :: as =>
      as.foldl (fun best a =>
        if shield.utility a > shield.utility best then a else best) a
```

`Shield.decide`'s empty-admissible-set branch returns the unmodified
proposal, which is very likely the wrong thing to do in a deployed system.
No theorem in this thesis says what the right thing is, and no default is
fixed here beyond what type-checks.

# Capability monotonicity

Reachability in a finite number of steps, under a given capability set, is
defined as an inductive predicate: a state reaches itself in zero steps, and
reaches a further state by one more executable-action step.

```lean
inductive ReachableIn {State Action : Type} (step : State → Action → List State)
    (c : CapabilitySet Action) : State → State → Prop where
  | refl (s : State) : ReachableIn step c s s
  | tail {s0 s' s : State} (a : Action) :
      ReachableIn step c s0 s' →
      c.executable a = true →
      s ∈ step s' a →
      ReachableIn step c s0 s

theorem capability_reachable_subset {State Action : Type}
    (step : State → Action → List State)
    (c1 c2 : CapabilitySet Action) (h : c1.le c2)
    (s0 s : State) :
    ReachableIn step c1 s0 s → ReachableIn step c2 s0 s := by
  intro hr
  induction hr with
  | refl => exact ReachableIn.refl s0
  | tail a hprev hexec hstep ih =>
      exact ReachableIn.tail a ih (h a hexec) hstep
```

`capability_reachable_subset` is checked by the Lean kernel: if `c1 ≤ c2`
in the sense of Chapter 3's capability ordering, every state reachable
under `c1` is reachable under `c2`. Its content is exactly this statement
and no more. It does not say anything about probability, about a defender's
ability to control what is reached, about safety, or about usefulness; it
is a fact about monotone reachability graphs, stated here because the
capability ordering it needs was already in scope, and its relevance to
agentic AI safety is entirely in the reading — shell access, unrestricted
networking, credentials, write access, and delegation are each naturally
modeled as enlarging the executable-action set at every state that has
them — a reading this thesis asserts but does not, and could not, prove.
