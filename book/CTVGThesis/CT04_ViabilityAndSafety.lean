import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Specification Automaton" =>

Not every hazard is a property of a single state. Reading an
attacker-controlled document, extracting a secret, and transmitting it to
an attacker-controlled endpoint violates no single-state predicate; the
violation is a property of the trajectory. This chapter gives the one Lean
object this thesis uses to reduce that kind of trajectory-level question to
an ordinary state-level one.

# The automaton

A safety specification is compiled into a deterministic monitor with a
start state, a step function reading the current state, the action taken,
and the resulting state, and a predicate marking which of its states are
rejecting.

```lean
structure SpecAutomaton (R S A : Type) where
  init    : R
  step    : R → S → A → S → R
  reject  : R → Bool

/-- Running the automaton over a whole trajectory, so that a trajectory
violates the specification exactly when the automaton ends in a rejecting
state. -/
def SpecAutomaton.run {R S A : Type} (spec : SpecAutomaton R S A)
    (states : List S) (actions : List A) : R :=
  match states, actions with
  | s :: s' :: states', a :: actions' =>
      spec.step (SpecAutomaton.run spec (s :: states') actions') s a s'
  | _, _ => spec.init
```

`SpecAutomaton.run` type-checks and its termination is accepted by the
compiler's structural-recursion check on the argument lists; nothing beyond
that is claimed. In particular, this chapter does not prove that any
concrete instantiation of `step` correctly compiles any particular temporal
formula, does not prove `SpecAutomaton.run` correct against any semantics
for trajectories, and does not prove that `reject` classifies trajectories
the way an informal safety specification would want. What is proved is only
that the automaton, as a piece of Lean code, is well-typed and terminates —
which is exactly the reduction Chapter 3's `CTVGState.monitor` field
presupposes is available: the monitor component of the state is intended to
be populated by `SpecAutomaton.run`'s current partial result, so that a
trajectory-level property becomes the ordinary state-level question of
whether that field currently satisfies `reject`.
