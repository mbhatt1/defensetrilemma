# Pick Two — Issue 0x01

A *PoC‖GTFO*-style (hacker-gospel) edition of a machine-checked book by Manish Bhatt. The technical
content and every Lean proof are transcribed verbatim from the book's own Verso
sources (`../TrilemmaBook/Ch*.lean`); the gospel voice is added only at the seams
(a Pastor's foreword and per-chapter prefaces), so no proof or claim is altered.

## Artifacts
| File | What it is |
|------|------------|
| `aipocorgtfo-book.pdf` | **The book.** 420 pp, 6×9in, KDP-ready interior. |
| `cover.pdf` | **Full-wrap KDP cover** (back + spine + front), spine locked to 420 pp. |
| `aipocorgtfo.pdf` | The original 10-page tract version (kept for reference). |
| `convert.py` | Regenerates the interior `.tex` from the Verso sources. |
| `cover.tex` | The cover source. |
| `build.sh` | Builds interior + cover, prints page count and spine width. |
| `KDP_CHECKLIST.md` | Everything needed to publish on Amazon KDP. |
| `VIRALITY.md` | Go-viral-but-correct playbook (10-channel synthesis). |
| `SERIES.md` | The AI‖PoC‖GTFO series manifesto, slate, and format bible. |

## Build
```sh
./build.sh
```
Needs a TeX Live / TinyTeX with `mathpazo`, `inconsolata`, `tcolorbox`, `tikz`,
`lettrine`, `titlesec`, `pifont`. Everything is pdfLaTeX.

## Editorial standard (kept from the source)
Every numbered result is machine-checked in Lean 4 or cites a checked declaration;
the only unproved claims say **Not formalized** in their own text. The combinatorial
core is axiom-free; the analytic results use the three standard axioms. The book is
honest that the engine is Lawvere (1969), that the force rests on modeling premises,
and that it proves existence, not frequency. **PoC, or GTFO.**
