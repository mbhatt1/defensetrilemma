import VersoManual
open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "What Was Cut, and Why" =>

This thesis was rewritten under a rule adopted from its companion volume:
a claim survives only if it is proved in an elaborated Lean block or
resolves to a named declaration. Applying that rule to the original
proposal removed most of it. This chapter lists what was removed, so the
cut is auditable rather than quiet.

# The robust failure value and the viability kernel

Proposed: a value function `V_T(B)`, computed as the smallest,
over defender policies, of the largest, over adversary policies and
plausible transition models, probability of a trajectory reaching a
failure set before a completion set; a "useful viability kernel" of belief
states from which some defender policy keeps this value and a companion
tail-severity functional below fixed tolerances while still finishing the
task; and a "critical surface" at the kernel's boundary.

Cut, in full. No transition model, no defender-policy type, no
adversary-policy type, and no value function were ever defined in Lean.
The recursion proposed to compute `V_T` was written down by analogy with
classical Bellman recursions and its existence and convergence were never
established, even informally, let alone proved.

# Tail severity and adversarial energy

Proposed: a CVaR-based tail-severity functional, and a "critical energy"
measuring the minimum adversarial effort needed to force a belief state out
of the viability kernel.

Cut, in full, for the same reason: both were defined only in prose, against
objects (the viability kernel, an attacker effort function) that themselves
were never formalized.

# Recoverability as a probability, and the hysteresis prediction

Proposed: a recoverability functional `R_T(B)`, a "core" safe region, a
resulting point-of-no-return boundary, and a prediction that memory-bearing
agents would show measurable hysteresis in failure probability under a
forward/backward sweep of a hazard-intensity parameter, while stateless
agents would not.

Cut. What is kept, in Chapter 6, is only the bookkeeping interface a future
monitor implementing some such quantity would expose — an estimate and an
update function — with no claim about what the estimate should be, how it
would be computed, or whether the hysteresis prediction is true. The
prediction itself, being an empirical claim about systems that were never
built or measured as part of this thesis, does not belong in a document
gated on Lean backing, and is removed rather than retained as a labeled
conjecture.

# The runtime-assurance fallback rule

Proposed: a design rule that, when a shield's admissible-action set is
empty, control should switch to a distinct, independently-certified
fallback controller, by analogy with the Simplex architecture from
safety-critical control.

Cut as a rule. What is kept, in Chapter 5, is the observation that
`Shield.decide`'s empty-admissible-set branch currently returns the
unmodified proposal — a fact about the Lean code, stated as a fact about
the code, not as a design recommendation about what a real system should
do instead.

# Causal-incentive analysis and the Defense Trilemma reading

Proposed: a reading of structural causal influence diagrams as
complementary to reachability analysis, identifying "pressure" where
reachability identifies "consequence"; and a reading of the companion
thesis's Defense Trilemma result as motivating this thesis's (now-removed)
shield architecture.

Cut, in full. Neither reading was a claim this thesis could back with a
declaration — the first cites no diagram formalized anywhere in this
project, and the second is commentary on a different thesis's theorem, not
a claim proved here.

# The eight-item empirical identification program

Proposed: a procedure for discovering an adequate state representation by
an empirical Markov-sufficiency test, a procedure for fitting a transition
model and an ambiguity set from data, a procedure for estimating `V_T` and
testing for a critical surface, and eight falsifiable predictions collected
from the rest of the (now-removed) theory.

Cut, in full. No data was collected, no model was fit, and every prediction
depended on a quantity — `V_T`, `E_crit`, `R_T`, the hysteresis loop area —
that no longer appears in this thesis.

# What this leaves

What survives is Chapters 3 through 6: four Lean structures, one inductive
predicate, and one theorem. That is the whole of this thesis's formal
content, and Chapter 8 says so without padding it back out.
