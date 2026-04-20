# NeurIPS 2025 Format Compliance Audit — `paper2_neurips.tex`

Auditor: reproducibility/compliance agent. This is a static audit of
`/Users/mbhatt/stuff/paper2_neurips.tex` against
`/Users/mbhatt/stuff/neurips_2025.sty` (revised April 2025). Agent 1
owns the `.tex` source; this file is read-only commentary.

## Verdict at a glance

| Check | Status | Note |
|---|---|---|
| `\usepackage` loads `neurips_2025` correctly | PASS | `\usepackage[preprint]{neurips_2025}` at line 4 |
| Preprint / final / submission option chosen | PASS (preprint) | Consistent with author names being shown and `[17]` reference to companion paper |
| Author block (non-anonymous) | PASS | Preprint option unsets `@anonymous`; authors appear in PDF page 1 |
| Corresponding-author footnote | PASS | Line 42 `\thanks{Corresponding author: ...}` |
| Abstract present | PASS | Lines 67–89 |
| Broader Impact section | PASS | Line 1401, `\section*{Broader Impact}` |
| References | PASS | 23 bibitems, lines 1415–1545, `\bibliographystyle{plain}` |
| Citation style matches sty | PASS | `.sty` loads natbib; line 3 passes `numbers, compress` to natbib → numeric citations in brackets, compressed. Matches NeurIPS house style. |
| Line numbers | PASS for preprint | `.sty` only loads `lineno` in submission mode; under `preprint` line numbers are OFF. Page 1 of the PDF confirms no line numbers. This matches NeurIPS 2025 policy for camera-ready/arXiv. **For the initial submission, the `preprint` option must be removed or replaced with no option** so that reviewers see line numbers. |
| Footer | PASS | "Preprint." text shown on page 1 of the PDF, produced by `\@noticestring` under `preprint`. |
| Figure/table caption style | PASS | Uses `\caption{...}` with `\label{...}` only, inherits `.sty` caption spacing. Table caption-above, figure caption-below convention is respected by the `.sty` (it swaps `abovecaptionskip`/`belowcaptionskip` inside `table`). |
| `fullpage` or similar forbidden packages | PASS | None loaded; `.sty` warns about `fullpage`. |
| `hyperref` / `cleveref` / `booktabs` / `microtype` | PASS | Loaded after `neurips_2025` (lines 10–18), the documented-safe order. |
| Acknowledgments section | NOT PRESENT | No `\acksection` or `ack` env used. Optional for preprint; **required before camera-ready** (NeurIPS 2025 mandates an "Acknowledgments and Disclosure of Funding" section). Flag for Agent 1. |
| NeurIPS Paper Checklist | NOT PRESENT | The paper does not include the NeurIPS 2025 checklist (`\answerYes`/`\answerNo`/`\answerNA` macros). **Required for submission.** Flag for Agent 1. |
| Page count (main text, 9-page limit) | **FAIL (predicted)** | See detailed analysis below. |

Overall verdict for **preprint submission**: **PASS with two caveats** —
(missing checklist, missing acknowledgments section; both required only
when submitted to the conference, not for an arXiv preprint.)

Overall verdict for **NeurIPS submission**: **FAIL** on page count,
checklist absence, and `preprint` option (which hides line numbers). All
three are correctable by Agent 1.

## Page-count analysis

NeurIPS 2025 main-text limit is **9 pages** (acknowledgments, Broader
Impact, references, appendices do not count against it; the same 9
applies to preprints under the `preprint` option only as a style
convention).

**Stale PDF at `/Users/mbhatt/stuff/paper2_neurips.pdf`** (mtime 2026-04-19
14:08, 353 KB): ends main text ("Conclusion") on page 12, "Broader
Impact" + "References" on page 13, appendices through page 16. This PDF
is stale relative to the current `.tex` (it lacks the continuous-defense
sweep tables, GP-kernel sensitivity table, resolution table, and
bootstrap-CI table that were added in Section 10.1). Agent 1 must
recompile before page count can be measured precisely.

**Current `.tex` estimate (from structural counting):**

- Lines 64–1399 constitute the main text (Abstract → Conclusion).
- 13 `\section` environments (not counting `\section*{Broader Impact}`
  and the Appendix sections).
- 3 figures in the main text (`\begin{figure}` at lines 233, 351, 590,
  1170 — line 1170 is the fourth and lives in Section 10).
- 6 tables in the main text (`\begin{table}` at lines 950, 1082, 1204,
  1216, 1227, 1258, 1282).
- Section 10.1 (Experimental Validation) has grown substantially vs the
  stale PDF: the current version adds
  `tables/continuous_sweep.tex`, `tables/gp_sensitivity.tex`,
  `tables/resolution.tex`, `tables/ci.tex` (four new tables; three of
  them are `\input{}`-sourced from Agent 2/4's sweep runs).

Given the stale PDF already renders 12 pages of main text and the
current `.tex` adds four more tables plus additional prose to Section
10.1, we estimate the compiled main text will be **13–15 pages**,
exceeding the 9-page limit by **4–6 pages**. Agent 1 must cut or move
content to the appendix to hit 9.

Concrete suggestions for Agent 1 to reclaim pages (none require math
changes):

1. Move `\section*{Broader Impact}` to after `\section{Conclusion}` but
   before the appendix — it already is, this is a no-op but confirms
   correct placement.
2. Move `\subsection{Stress test: discrete defenses}` (Section 10.1.4,
   lines 1269–1308) to the appendix. The content is explicitly a
   "pipeline stress test, not a theorem check" and adds ~1 page.
3. Move `\subsection{Sanity check: identity defense}` (Section 10.1.1,
   lines 1067–1101) to the appendix; the text itself says these runs
   "only confirm the validator's bookkeeping, not the theorem".
4. Condense the nine `\paragraph{...}` in Section 10 (Llama-3-8B,
   GPT-OSS-20B, GPT-5-Mini bullets + four engineering prescription
   paragraphs) into itemized lists.
5. Move Section 8 (Extensions) subsections to the appendix; only the
   headline statements need to appear in the main text.

## Overfull hboxes

`paper2_neurips.log` is not present in the repo (Agent 1 has not
recompiled after the cli/tex edits). Overfull-hbox analysis cannot be
performed until after Agent 1 recompiles. Flag for Agent 1: after
compilation, grep the log for `Overfull \\hbox` and any entry greater
than 10 pt should be fixed with a hyphenation hint, `\sloppy`, or a
line-break tweak.

## Citation style

- `neurips_2025.sty` loads `natbib` via `\if@natbib` (line 110–112) by
  default.
- `paper2_neurips.tex` line 3: `\PassOptionsToPackage{numbers,
  compress}{natbib}` — this forces numeric, compressed citations. This
  is the NeurIPS 2025 recommended style.
- The paper uses `\cite{...}` (23 uses), which under `natbib`+`numbers`
  renders as `[n]`. This matches the rendered PDF.
- **Compliance:** PASS.

## Figure and table caption style

- `.sty` sets `\abovecaptionskip = 7pt`, `\belowcaptionskip = 0pt`, and
  swaps them inside `table` so tables get caption-above and figures get
  caption-below. This is the standard NeurIPS convention.
- Paper uses `\caption{...}\label{...}` consistently. No `\caption*`
  uses. No side-captions.
- **Compliance:** PASS.

## Cross-reference hygiene

The paper uses `\Cref{...}` via `cleveref`. We observed no broken
cross-references in the stale PDF. However, the current `.tex`
references several labels defined only by inputs from `tables/`:

- `\label{tab:continuous-sweep}` — lives in `tables/continuous_sweep.tex`
  (not yet generated at audit time; present as placeholder).
- `\label{tab:gp-sensitivity}` — lives in `tables/gp_sensitivity.tex`.
- `\label{tab:resolution}` — lives in `tables/resolution.tex`.
- `\label{tab:ci}` — lives in `tables/ci.tex`.
- `\label{tab:seed-replication}`, `\label{tab:independent-dataset}`,
  `\label{tab:judge-robustness}` — referenced in the prompt's task list
  but **not referenced in the current `.tex`**. The only `tables/*.tex`
  present is `tables/independent_dataset.tex`; no `\input{}` of it
  exists. Flag for Agent 1 / Agent 3: either wire the table in or drop
  it from the reproducibility inventory.

Four of the expected `\input{tables/*.tex}` files do not yet exist on
disk (only `tables/independent_dataset.tex` was found). Agent 1's next
compile will fail on `\input{tables/continuous_sweep.tex}` etc. unless
Agents 2/4 have produced them.

## Summary for Agent 1

To go from current state to a clean NeurIPS 2025 submission:

1. **Page count** — cut Section 10 down to fit in the 9-page main text
   budget (see suggestions above).
2. **Line numbers** — remove the `preprint` option from line 4
   (`\usepackage[preprint]{neurips_2025}` → `\usepackage{neurips_2025}`)
   so submission-mode line numbers appear during review.
3. **NeurIPS Paper Checklist** — add the checklist environment to the
   end of the main text (the `.sty` defines `\answerYes` /`\answerNo`
   / `\answerNA` / `\answerTODO` macros; use them).
4. **Acknowledgments** — add `\begin{ack}...\end{ack}` before the
   bibliography for funding disclosure.
5. **Missing table sources** — coordinate with Agents 2/4 so
   `tables/continuous_sweep.tex`, `tables/gp_sensitivity.tex`,
   `tables/resolution.tex`, `tables/ci.tex` land in place before next
   compile.
6. **Stale PDF** — recompile `paper2_neurips.tex` so `paper2_neurips.log`
   is regenerated; re-run this audit against the fresh log for the
   overfull-hbox check.
