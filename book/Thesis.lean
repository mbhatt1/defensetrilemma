/-
Root document for the thesis. The theoretical chapters are the verified
chapter modules of the companion development, included here in thesis order;
the framing chapters are new and live under `Thesis/`.
-/

import VersoManual
-- New chapters, written for the thesis.
import Thesis.Th01_Introduction
import Thesis.Th02_RelatedWork
import Thesis.Th15_Empirical
import Thesis.Th16_Limitations
import Thesis.Th17_Conclusion
import Thesis.Th18_Exercises
-- Theoretical chapters, shared with the companion book and checked by Lean
-- as this document is built.
import Thesis.Ch00_Preliminaries
import Thesis.Ch01_Diagonal
import Thesis.Ch02_ClassicalLimits
import Thesis.Ch03_Trilemmata
import Thesis.Ch04_FromLogicToAnalysis
import Thesis.Ch05_AttackGeometry
import Thesis.Ch06_ApproximateBridges
import Thesis.Ch07_AISafety
import Thesis.Ch08_JSpace
import Thesis.Ch09_CoTMonitoring
import Thesis.Ch10_LatentKnowledge
import Thesis.Ch11_Watermarking
import Thesis.Ch12_Appendices

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Two Schemas of Impossibility: Machine-Checked Limits of Trustworthy Machine Learning, and Why They Tighten with Capability" =>

%%%
authors := ["Manish Bhatt"]
%%%

A thesis submitted in partial fulfilment of the requirements for the degree of
Doctor of Philosophy.

# Abstract

A trustworthy language model should not assert falsehoods with confidence,
should not obey instructions hidden in the data it processes, and should be able
to report on its own reasoning. Each of these goals has an impossibility result
attached to it, and the literature treats those results as separate findings
proved by separate methods.

This thesis argues that they are instances of two mathematical schemas. The
first is a diagonal schema: a system that can name its own behaviors is forced
to a self-referential fixed point, and this single lemma generates Cantor,
Gödel, Tarski, and Rice along with the verdict trilemmata for hallucination and
for prompt-injection defense. The second is a value-crossing schema: a
continuous quantity that changes sign on a connected domain must vanish
somewhere, and this generates the truth-boundary results, the geometry of attack
surfaces, and the coupling of confidence to correctness.

Both schemas are formalized in Lean 4 and proved from first principles. The
accompanying corpus contains 738 declarations across four libraries with no
`sorry` and no axioms beyond the three that Mathlib itself uses, and the
document is gated so that a numbered claim which is neither proved in the text
nor cited to a resolvable declaration fails the build.

The exact theorems assume properties no finite system has. The thesis therefore
develops approximate forms in which each hypothesis is relaxed to a tolerance,
and then measures that tolerance. On a ladder of five open-weight models the
coupling slack falls from 0.225 to 0.075 and the coverage hypothesis rises from
43% to 99% satisfaction, with one documented exception whose training data
differs from the rest. The weakest model in the set escapes the trilemma
entirely, by never committing to an answer, which is the abstention corner
reached through incapacity rather than design.

The conclusion is that these limits tighten as systems become more capable. The
hypotheses that make the impossibility theorems apply are the same properties
that make a model useful, and a system evades the theorems only by failing to
have them.

# How to read this thesis

Part I is background and may be skipped by a reader who knows Lawvere's
fixed-point theorem and its classical instances. Part II is the theoretical
contribution and is where the trilemmata are proved. Part III applies the theory
and tests it. Part IV states what is wrong with the argument and concludes.

Every code block in this document is elaborated by Lean 4 as the document is
built, so the proofs printed in the text are the proofs the kernel accepted.
Results proved elsewhere are cited by name to the companion libraries, and
Appendix A indexes those libraries file by file.

{include 1 Thesis.Th01_Introduction}

# Part I: Background

{include 1 Thesis.Ch00_Preliminaries}

{include 1 Thesis.Ch01_Diagonal}

{include 1 Thesis.Ch02_ClassicalLimits}

{include 1 Thesis.Th02_RelatedWork}

# Part II: The Two Engines

{include 1 Thesis.Ch03_Trilemmata}

{include 1 Thesis.Ch04_FromLogicToAnalysis}

{include 1 Thesis.Ch05_AttackGeometry}

{include 1 Thesis.Ch06_ApproximateBridges}

# Part III: Application and Evidence

{include 1 Thesis.Ch07_AISafety}

{include 1 Thesis.Ch08_JSpace}

{include 1 Thesis.Ch09_CoTMonitoring}

{include 1 Thesis.Ch10_LatentKnowledge}

{include 1 Thesis.Ch11_Watermarking}

{include 1 Thesis.Th15_Empirical}

# Part IV: Assessment

{include 1 Thesis.Th16_Limitations}

{include 1 Thesis.Th17_Conclusion}

{include 1 Thesis.Th18_Exercises}

{include 1 Thesis.Ch12_Appendices}
