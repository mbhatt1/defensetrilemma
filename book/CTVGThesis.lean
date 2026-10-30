/-
Root document for the CTVG thesis. Rewritten to keep only content backed by
an actual Lean declaration: a claim that resolves to nothing in this
project's Lean code does not appear in this document. See Chapter 7 for what
that rule removed from the original proposal.
-/

import VersoManual
import CTVGThesis.CT01_Introduction
import CTVGThesis.CT02_RelatedWork
import CTVGThesis.CT03_FormalModel
import CTVGThesis.CT04_ViabilityAndSafety
import CTVGThesis.CT05_Recoverability
import CTVGThesis.CT06_Architecture
import CTVGThesis.CT07_EmpiricalProgram
import CTVGThesis.CT08_Limitations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Capability Monotonicity in a Formal Skeleton for Agentic AI Safety" =>

%%%
authors := ["Manish Bhatt"]
%%%

A thesis submitted in partial fulfilment of the requirements for the degree of
Doctor of Philosophy.

# Abstract

An earlier draft of this project proposed a full dynamic-programming theory
of agentic AI safety — a robust reachability value, a viability kernel, a
critical surface, a recoverability boundary, an adversarial-energy metric,
a memory-hysteresis prediction, and an eight-item empirical program built
on top of them. This document is not that draft. It is a rewrite under a
rule borrowed from its companion thesis, *Two Schemas of Impossibility*:
a claim appears only if it is proved in an elaborated Lean block or
resolves to a named Lean declaration: it is a thesis about what remains of
a larger proposal once every claim without a Lean declaration behind it is
removed.

What remains is a small formal skeleton — an augmented agent state, a
belief interface, an intervention/composition mechanism, a capability
partial order, a specification automaton, a shield interface, and a
recoverability-monitor interface, each a Lean `structure`, `inductive`, or
`def` checked by the compiler as this document builds — together with one
genuine theorem, `capability_reachable_subset`: a capability ordering that
only ever adds executable actions can only ever enlarge the reachable
state graph. The theorem is a general fact about monotone reachability
graphs; its relevance to agentic AI safety is a reading argued for in the
text, not a further mathematical result.

Chapter 7 lists every claim that was cut to reach this document — the
value function, the viability kernel, the critical surface, the tail-
severity and adversarial-energy functionals, the recoverability
probability and its hysteresis prediction, a runtime-assurance design
rule, a causal-incentive reading, and the empirical identification
program — and says why each was cut: none of them corresponded to a Lean
declaration. This thesis's claim about itself is only that the skeleton
and the one theorem in Chapters 3 through 6 are genuinely backed, and that
everything listed in Chapter 7 is a research proposal, not a result.

# How to read this thesis

This is a short document by design. Chapter 1 states the scope reduction
directly. Chapter 2 places the surviving formal objects, briefly, against
their literatures. Chapters 3 through 6 give the Lean content: the state
and capability structures, the specification automaton, the shield
interface and the capability-monotonicity theorem, and the
recoverability-monitor interface. Chapter 7 is an explicit accounting of
what was removed and why. Chapter 8 concludes.

{include 1 CTVGThesis.CT01_Introduction}

{include 1 CTVGThesis.CT02_RelatedWork}

{include 1 CTVGThesis.CT03_FormalModel}

{include 1 CTVGThesis.CT04_ViabilityAndSafety}

{include 1 CTVGThesis.CT05_Recoverability}

{include 1 CTVGThesis.CT06_Architecture}

{include 1 CTVGThesis.CT07_EmpiricalProgram}

{include 1 CTVGThesis.CT08_Limitations}
