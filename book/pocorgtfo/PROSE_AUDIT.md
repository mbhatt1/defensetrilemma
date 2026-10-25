# Prose correctness & readability audit — AI ‖ PoC ‖ GTFO, Issue 0x01

Scope: (a) the *light-touch prose I added* (Pastor's foreword, 13 chapter
prefaces, copyright page, colophon); (b) the *converted body* for conversion and
readability artifacts; (c) *every factual claim* against the source and the Lean
build. The body text itself is transcribed verbatim from the authors' Verso
sources and is not re-copyedited here.

## 1. Factual claims in the added prose — all verified
| Claim (in foreword / copyright / colophon) | Check | Result |
|---|---|---|
| 94 authored Lean files | `find … -name '*.lean'` | 94 ✔ |
| ~17,000 lines | line count | 17,367 ✔ |
| four Lake packages | dir count | 4 ✔ |
| engine is Lawvere, 1969 | source Ch.1 | ✔ (book says so itself) |
| exactly three "Not formalized", all deployment-cost | grep source | 3, all in Ch.7 ✔ |
| combinatorial core axiom-free | `#print axioms` in build | ✔ (no axioms) |
| analytic results use propext/Classical.choice/Quot.sound | build audit | ✔ |
| sorry-free | build + grep | ✔ |
| existence, not frequency | source Ch.3/7 | ✔ |
| 8072 build jobs (geometry pkg) | build log | ✔ |

## 2. Preface accuracy — each previews its chapter correctly
Ch0 Preliminaries → Lean constructs + `#print axioms` ✔ · Ch1 Diagonal → Lawvere
1969, five classical results ✔ · Ch2 → Cantor/Russell/Gödel/Tarski/Turing as one
✔ · Ch3 → three trilemmata = one `rfl`, "grade the premise" ✔ · Ch4 → second
engine, IVT, fixed point at ½ ✔ · Ch5 → basins/Lipschitz tubes/boundary density ✔
· Ch6 → slack, truth slack never closed ✔ · Ch7 → three corners, three "Not
formalized" ✔ · Ch8 → J-space derivative probe ✔ · Ch9 → CoT: faithfulness forces
length, selection destroys signal ✔ · Ch10 → ELK, counting fact, reporter
underdetermined ✔ · Ch11 → watermark/paraphrase, no self-reference ✔ · Ch12 →
build + axiom audit ✔. No preface overclaims beyond the source.

## 3. Conversion / readability artifact scan (generated TeX)
- empty `\emph{}` / `\texttt{}` / `\(\)`: 0 · double `\vp`: 0 · leaked markdown
  headings: 0 · stray bullet markers: 0 · raw code fences: 0.
- stray unicode in prose: 0 (non-ASCII appears only inside code blocks and the
  listings `literate` table, as intended).
- 212 backticks = the opening halves of converted curly quotes (`` `` ``), correct
  LaTeX, not artifacts.
- Overfull boxes (hbox+vbox): **0**. Fonts: all embedded, no Type 3.

## 4. Bug found and fixed during this audit
**Emphasis spans containing inline code were not converted.** Source labels such
as `*Definition 1.1 (`System`).*` (321 of them) left *literal asterisks* in the
output because the parser split on code before handling emphasis. Fixed: the inline
parser now tokenizes emphasis and code in one pass and renders emphasis inner
recursively, and theorem/definition labels render as **bold run-in labels**
(matching the 45 plain-text labels, for a uniform theorem-book look). After the
fix, literal asterisks in prose dropped to **1**, which is a legitimate
multiplication (`2*del`) inside a code span. Verified visually on the congrFun
definition page.

## 5. Content integrity
- Pure-prose sentence sample (130 sentences, no inline code): **99.2% present**
  (1 miss, itself an inline-code artifact of the checker, not dropped text).
- Code blocks: 108 in source → **108** rendered. Chapters: **13 → 13**.
- Banned phrases ("verified gospel", "One Diagonal"): **0** in book, cover, tract.

## 6. Readability render-checks (pages viewed, not just logs)
Systematic per-chapter-type coverage — pages rendered to image and read, not just
logged. Front matter (title, copyright, TOC, foreword); Preliminaries (incl. the
congrFun definition page, post-fix bold label); Ch.1 Diagonal (opening + Turing
subsection); Ch.4 Analysis (math-dense); Ch.5 Geometry (quantitative, snake_case
Lean names); Ch.11 Watermarks (opening + preface); Ch.12 Appendix (build/axiom
section); and the benediction. Every page reads cleanly: correct math glyphs,
inline code in mono with proper line-breaking, bold run-in theorem labels, curly
quotes, intact cross-references, no stray markup.

Spacing scan: no space-before-punctuation and no double-spaces in prose (the raw
counts were all preamble/math false positives); the six `()` are legitimate Lean
`Unit` references; only two standalone display-equations exist (Ch.8), rendered
readably inline. No readability defect remains in the conversion.

## 7. Body-correctness audit (the authors' verbatim text)
Systematic checks of verifiable facts in the body, run against the rendered PDF:
- **Arithmetic.** Every numeric computation verified by hand/script and correct:
  `0.01·0.95·1000 = 9.5`, `0.0001·0.95·1000 = 0.095`, `0.02·0.30 = 0.6 percent`
  (= 0.006), `0.05·10^20 = 5·10^18`, `2·ε/(4L) = ε/(2L)`. No arithmetic errors.
  (The one script "mismatch" was the `0.6 percent` line — correct once "percent" is
  read.)
- **Cross-references.** 913 numbered references (`Theorem/Definition/Lemma/…/Chapter
  N.M`); none points to a chapter > 12; no dangling range. The single apparent
  "Chapter 363" is a pdftotext reflow of a page number into "Chapter 9's trace
  factoring" — the rendered page is correct.
- **Novelty / overclaim.** No unqualified "first/novel/nobody" claims; the lone
  "novelty, such as it is" is the book's own hedged disclaimer that the engine is
  Lawvere 1969.
- **Cited Lean names.** Key backticked identifiers (`lawvere`, `no_universal`,
  `bool_not_fpf`, `hallucination_trilemma`, `boundary_coupling`,
  `stochastic_dichotomy`, `cch_master_trilemma`, `two_slack_approx_coupling`)
  resolve to real declarations that build sorry-free (see `VERIFICATION.md`).

Conclusion: the body's checkable claims are correct. The prose was audited for
*correctness and conversion fidelity*, not restyled — see §7.

## 8. Systematic copyedit pass (six parallel reviewers, all 13 chapters)
A full copyedit review of the body prose, one reviewer per 2–3 chapters, briefed to
report only objective defects (typos, grammar, duplicated/wrong words, garbled
sentences, broken cross-references) with exact quotes — not style preferences.
Result: the prose is exceptionally clean. Four genuine defects were found across
420 pages, all corrected in the homage layer (canonical sources untouched):

| Ch | Defect | Fix | Category |
|----|--------|-----|----------|
| 8 | "nonneglible" | "nonnegligible" | typo |
| 7 | "measurement protocol of Section 6 histograms…" | Section **5** (histogram protocol is in §5; §6 is "What the theorems do and do not claim") | wrong cross-ref |
| 7 | "the warning of Section 3" (Problem 7.26) | Section **2** (the cited Prop 7.8 / "for free" drift is in §2) | wrong cross-ref |
| 5 | "worked corner example of Section 6" | Section **5** (the "corner in the score" example is in §5; §6 is "Dimensional scaling") | wrong cross-ref |

All three section references were off by one (pointing one section too high),
consistent with a section having been inserted after they were written. Each fix
was verified against the chapter's actual heading structure and confirmed present
in the rebuilt PDF. My own added prose (foreword, 13 prefaces, colophon) has no
doubled words or typos.

**Recommendation:** these four are real errors in the canonical book too (not just
the homage). I left `TrilemmaBook/` untouched per policy; say the word and I will
apply the same four fixes there and rebuild the canonical edition.

## 9. Honest residual limitations
- **ISBN** is a placeholder; KDP issues the ISBN at publish time.
- **"KDP-ready"** means the interior and cover meet KDP's file specs (6×9, gutter,
  embedded fonts, correct spine); it is not an actual KDP submission.
- The **body prose is the authors' verbatim text**, audited earlier as high
  quality; this pass did not re-copyedit their wording, only fixed conversion
  fidelity and added the framing.
