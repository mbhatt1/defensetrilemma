/-
Generator for the CTVG thesis edition. Independent of the book/thesis
generators: it renders `CTVGThesis` (root document) to its own output
directory so it never collides with the Defense Trilemma outputs.
-/

import VersoManual
import CTVGThesis
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
  destination := "_out_ctvg_thesis"

def main := manualMain (%doc CTVGThesis) (config := config)
