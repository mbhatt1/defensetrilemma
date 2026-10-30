/-
Generator for the thesis edition.

Same source of truth as the book: the theoretical chapters are the same Lean
modules, elaborated here in thesis order, with the framing chapters written for
examination rather than for a general reader.
-/

import VersoManual
import Thesis
import TrilemmaBook.Theme

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := true
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  sectionTocDepth := none
  rootTocDepth := none
  extraHead := #[TrilemmaBook.Theme.head]
  -- Keep the thesis output out of the book's tree.
  destination := "_out_thesis"

def main := manualMain (%doc Thesis) (config := config)
