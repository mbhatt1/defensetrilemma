import VersoManual
open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Conclusion" =>

This thesis, in its current form, formalizes a small piece of vocabulary
for reasoning about agentic AI safety — an augmented state, a belief
interface, an intervention/composition mechanism, a capability partial
order, a specification automaton, a shield interface, and a
recoverability-monitor interface — and proves one theorem against that
vocabulary: `capability_reachable_subset`, that a capability ordering which
only ever adds executable actions can only ever enlarge what is reachable.

That is a modest result relative to the theory originally proposed. It is
stated as such rather than dressed up, because the alternative — keeping
the larger theory's definitions and conjectures in the document, labeled as
conjectures — was tried in an earlier draft and rejected: a claim that
cannot be checked by the Lean kernel does not belong in a thesis gated on
Lean backing, no matter how carefully it is hedged in prose. Chapter 7
records exactly what that rejection removed, so that the removal is
inspectable rather than a matter of trust.

What this thesis takes itself to have shown is narrower than what its
companion volume shows for hallucination and prompt-injection defense: a
type-correct formal skeleton, and one theorem within it. The larger claims
about robust reachability values, viability kernels, critical surfaces,
recoverability, adversarial energy, and hysteresis in memory-bearing agents
remain exactly what they were before this rewrite — informal proposals,
possibly worth formalizing — and this document no longer asserts them.
