import VersoManual
open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Related Work" =>

The formal objects that survive into Chapters 3 through 6 are small
instances of larger, established constructions. This chapter places each
one, and is explicit that placing an object against a literature is not the
same as claiming this thesis reproduces that literature's theorems: the
Lean content of this thesis is the four structures and the one theorem
listed in Chapter 1, and nothing said here should be read as extending that
content.

# Hybrid state and partial observability

Chapter 3's augmented state, with continuous and discrete components living
side by side, is an instance of the standard object in stochastic hybrid
systems theory, where reachability results are already established for
systems combining both. Chapter 3's belief interface is the standard
sufficient-statistic construction from partially observable planning: the
posterior over the hidden state given the observation history is what a
planner needs to act optimally under partial observability, and belief-space
planning is the classical way to reduce a partially observed problem to a
fully observed one over that posterior. This thesis's `Belief` structure
captures only the interface — a point estimate and an update rule — not the
measure-theoretic content, deliberately: nothing downstream in this thesis
needs more than the interface.

# Specification automata

Compiling a trajectory-level temporal property into a monitor automaton,
which Chapter 4's `SpecAutomaton` does, is the standard construction from
runtime verification and from shielding in safe reinforcement learning: a
temporal-logic specification is compiled into an automaton whose state
tracks progress toward, or violation of, the property, so that a
trajectory-level question becomes an ordinary question about the automaton's
current state. Shielding then overrides a learner's action only when doing
otherwise would violate the specification, which is the idea Chapter 5's
`Shield` structure encodes, again as an interface rather than as a proof
that any concrete shield built on it satisfies the specification.

# Capability and reachability

The claim proved in Chapter 5 — that a capability ordering which only adds
executable actions can only enlarge the reachable set — is an instance of an
entirely general fact about reachability in monotone systems, unrelated to
agents specifically: it holds for any state-transition graph where a
"stronger" edge set is a superset of a "weaker" one. Its relevance to
agentic AI safety is the reading, not the mathematics: shell access,
unrestricted networking, credentials, write access, and delegation are each
naturally modeled as enlarging the executable-action set at every state that
has them, and the theorem then says the resulting reachable set can only
grow. This reading is argued for in Chapter 5; the theorem itself needs
nothing about agents to be true.

# What this chapter does not place

Belief-space robustness under model uncertainty, temporal reachability
values, runtime-assurance switching, information-flow reference monitors,
and causal-incentive analysis all have substantial literatures that an
earlier draft of this thesis related its (since-removed) claims to. Chapter
7 records that those claims were removed and does not restore this
chapter's discussion of their literatures, because a related-work section
for a claim that no longer appears in the thesis would misrepresent what the
thesis contains.
