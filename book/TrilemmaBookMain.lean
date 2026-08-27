/-
Generator for "Impossibility Theorems for AI Safety, from One Diagonal".

Emits both outputs from one source:
  * a single-page HTML book (the living, verified edition), and
  * a TeX edition (the print / Springer path).

The HTML is deliberately one page: the book is short enough to read straight
through, and a chapter-per-page split turns the front page into a file listing
and every cross-reference into a navigation round trip.
-/

import VersoManual
import TrilemmaBook
import TrilemmaBook.Theme

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  -- Both outputs from one source.
  emitTeX := true
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  -- One page, so the sidebar ToC is the only navigation anyone needs; show
  -- every section in it rather than chapter titles alone.
  sectionTocDepth := none
  rootTocDepth := none
  -- Book typography and syntax coloring, injected inline.
  extraHead := #[TrilemmaBook.Theme.head]

def main := manualMain (%doc TrilemmaBook) (config := config)
