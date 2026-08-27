/-
Root document for the book. Each chapter is a separate module, included below.
-/

import VersoManual
-- Chapters
import TrilemmaBook.Ch00_Preliminaries
import TrilemmaBook.Ch01_Diagonal
import TrilemmaBook.Ch02_ClassicalLimits
import TrilemmaBook.Ch03_Trilemmata
import TrilemmaBook.Ch04_FromLogicToAnalysis
import TrilemmaBook.Ch05_AttackGeometry
import TrilemmaBook.Ch06_ApproximateBridges
import TrilemmaBook.Ch07_AISafety
import TrilemmaBook.Ch08_JSpace
import TrilemmaBook.Ch09_CoTMonitoring
import TrilemmaBook.Ch10_LatentKnowledge
import TrilemmaBook.Ch11_Watermarking
import TrilemmaBook.Ch12_Appendices

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "One Diagonal: Verified Limits of Trustworthy AI" =>

%%%
authors := ["Manish Bhatt", "Ken Huang"]
%%%

These are lecture notes on a family of impossibility theorems for machine
learning systems: hallucination, prompt-injection defense, calibration,
verification, and oversight. The organizing claim is that a single mathematical
move, the diagonal argument behind Cantor, Gödel, and Lawvere, generates most of
them, and that a second, analytic move, the intermediate value theorem and its
quantitative refinements, generates the rest.

What makes these notes unusual is that every theorem is machine-checked. The
core arguments are elaborated live by Lean 4 as the book is built, so the proofs
in the text are the proofs the kernel accepts. Where a result depends on the
`Mathlib` library, we cite the verified statement in the companion development
and reproduce the argument in prose.

# How to read this book

The book has two halves that meet in the middle. Chapters 1 through 4 develop
the diagonal engine and its consequences, and are almost entirely self-contained
core Lean: you can read the proofs as they compile. Chapters 5 and 6 turn to the
analytic side, where continuity, connectedness, and measure do work that no
diagonal can, and Chapter 7 draws the practical consequences for deploying
language models.

Chapters 8 through 11 are case studies, and they answer the standing objection
that all of this concerns outputs only. Each takes a construction proposed in
the recent literature as a way of seeing inside or around a model, and asks what
the two engines say about it. Chapter 8 takes J-space, a probe reading the
derivative of the computation rather than its activations. Chapter 9 takes
chain-of-thought monitoring, where the trace being read is text the model itself
chose to emit. Chapter 10 takes Eliciting Latent Knowledge, whose central
obstruction turns out not to be the diagonal at all but a counting fact about
functions agreeing on a subset. Chapter 11 leaves the model entirely and takes
watermark detection, where the mechanism is invariance under paraphrase. The
four are deliberately not four copies of one argument: the shared engines are
the diagonal and the intermediate value theorem, but the load-bearing step
differs in each, and Chapters 10 and 11 in particular reach their main results
without any self-reference.

Prerequisites are light: comfort with functions and sets, a first course in
logic, and enough topology to know what a continuous function on a connected
space is. No prior Lean is assumed; the code is explained as it appears.

{include 1 TrilemmaBook.Ch00_Preliminaries}

{include 1 TrilemmaBook.Ch01_Diagonal}

{include 1 TrilemmaBook.Ch02_ClassicalLimits}

{include 1 TrilemmaBook.Ch03_Trilemmata}

{include 1 TrilemmaBook.Ch04_FromLogicToAnalysis}

{include 1 TrilemmaBook.Ch05_AttackGeometry}

{include 1 TrilemmaBook.Ch06_ApproximateBridges}

{include 1 TrilemmaBook.Ch07_AISafety}

{include 1 TrilemmaBook.Ch08_JSpace}

{include 1 TrilemmaBook.Ch09_CoTMonitoring}

{include 1 TrilemmaBook.Ch10_LatentKnowledge}

{include 1 TrilemmaBook.Ch11_Watermarking}

{include 1 TrilemmaBook.Ch12_Appendices}
