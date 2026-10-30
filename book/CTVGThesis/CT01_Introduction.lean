import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Introduction" =>

This thesis started from a much larger proposal: a full dynamic-programming
theory of agentic AI safety, with a robust reachability value, a viability
kernel, a critical surface, a recoverability boundary, an adversarial-energy
metric, a hysteresis prediction, and an eight-point empirical program. That
proposal is not what follows. It is not what follows because none of it was
backed by a machine-checked declaration, and this thesis's governing rule,
inherited from its companion volume *Two Schemas of Impossibility*, is that a
claim without Lean backing does not appear in the document. The companion
thesis enforces this with a build-time citation gate: every numbered claim
must either be proved in an elaborated code block or resolve to a named
declaration in one of its four companion libraries, on pain of the build
failing. This thesis adopts the same rule and applies it to itself, and the
result is a much smaller document than the one first proposed.

# What survives the rule

Four objects survive. Chapter 3 gives the augmented agent state, a belief
interface, the intervention/composition mechanism, and the capability
partial order, each as a Lean `structure`, `inductive`, or `def` that the
compiler checks for well-formedness as this document builds. Chapter 4 gives
the specification automaton that a trajectory-level safety property compiles
into. Chapter 5 gives a shield interface and proves, as a genuine
machine-checked theorem, that a capability ordering which only ever adds
executable actions can only ever enlarge what is reachable — not a deep
result, but a real one, `capability_reachable_subset`, checked by the Lean
kernel rather than asserted in prose. Chapter 6 gives a recoverability
monitor interface, offered explicitly as bookkeeping rather than as backing
for any claim about what recoverability *is*.

# What does not survive

Chapter 7 lists what was cut and why, so that a reader who saw an earlier,
larger version of this project — or who read the informal writeup this
thesis grew out of — can see exactly where the boundary was drawn and can
check that the cut was not selective. The short version: a robust failure
value, a viability kernel, a critical surface, a tail-severity functional, an
adversarial-energy metric, a hysteresis prediction, a runtime-assurance
fallback rule, a reading of causal-incentive analysis, and an eight-item
empirical program were all proposed at one point and all removed, because
none of them was a Lean declaration and this thesis's rule does not make an
exception for an idea being interesting.

# Thesis statement, scaled to what remains

*A small fragment of agentic-AI-safety reasoning — the state an agent
occupies, the actions available to it under a capability ordering, the
automaton a trajectory-level specification compiles into, and the fact that
enlarging capability can only enlarge what is reachable — can be given a
machine-checked formal encoding in Lean 4, and exactly one nontrivial
consequence of that encoding, capability monotonicity of reachability, is
proved rather than asserted.*

This is a narrower claim than the one the larger proposal made, and it is
narrower on purpose. A reader who wants the larger theory — the dynamic
game, the critical surface, the empirical program — should read it as a
research proposal, stated as such, and should not mistake anything in
Chapters 3 through 6 of this document for evidence toward it.

# Structure

Chapter 2 places the surviving formal objects against their literature.
Chapter 3 gives the state, belief, intervention, and capability structures.
Chapter 4 gives the specification automaton. Chapter 5 gives the shield
interface and the capability-monotonicity theorem. Chapter 6 gives the
recoverability-monitor interface. Chapter 7 lists what was cut, and why.
Chapter 8 concludes.
