# Springer Nature Book Proposal — DRAFT (not submitted)

Items marked **[AUTHOR]** need your input. Items marked **[VERIFY]** are claims I could not check from the repo.

## 1. Title
**One Diagonal: Verified Limits of Trustworthy AI**
Subtitle option (more searchable): *Machine-Checked Impossibility Theorems for Hallucination, Prompt-Injection Defense, and Oversight*

## 2. Book type / series
Research monograph (with lecture-notes use). Current manuscript: 13 chapters, ~329 pp, ~150,000 words in the compiled PDF.
Not SpringerBriefs (50–125 pp cap). Suggested series to ask the editor about: *Artificial Intelligence: Foundations, Theory, and Algorithms*, or *Computer Science Foundations and Applied Logic*. **[VERIFY series fit with the commissioning editor]**

## 3. One-paragraph pitch (≤100 words)
Deployed language models are routinely promised hallucination-free output, injection-proof defenses, and trustworthy oversight. This book proves why those promises cannot all hold. A single idea, the diagonal argument of Cantor, Gödel, and Lawvere, yields the logical impossibilities; the intermediate value theorem yields the geometric ones. Every theorem is machine-checked in Lean 4 and elaborated as the book is built. The text then tests the results against recent proposals (J-space probes, chain-of-thought monitoring, latent-knowledge elicitation, watermarking) and maps what remains possible.

## 4. Description (≈300 words)
The book develops one claim: most impossibility results about trustworthy AI are instances of two mathematical moves. The first is diagonalization. It shows that any system asked to be complete, faithful, and self-calibrated about its own verdicts must contradict itself on a liar input. The second is analytic. If a defense or confidence map is continuous on a connected input space and must separate safe from unsafe inputs, then by the intermediate value theorem it has boundary points it cannot resolve, and quantitative refinements (coarea and cone bounds) bound how large that unresolved region is.

Part I (Ch. 0–4) builds the diagonal engine from Cantor through Gödel's second theorem, Tarski, Turing, Rice–Shapiro, and Lawvere's fixed-point theorem. It then states three trilemmata as one theorem and passes from logic to analysis. Part II (Ch. 5–7) develops the geometry of attacks, shows how the theory bridges to real, approximately continuous models, and draws design consequences as a menu of three relaxations (abstain, price a confident-error band, or decouple confidence from correctness). Part III (Ch. 8–11) applies the machinery to four proposals from the recent literature. In these, the load-bearing step differs each time, and two of the four reach their results with no self-reference at all. An appendix indexes the full formal corpus of four companion Lean libraries.

What sets the book apart is that its mathematics is verified. The build fails if any numbered result lacks either a proof or a citation that resolves to a real Lean declaration. Claims about deployment cost are labeled "Not formalized." in the text. Analytic results rest only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No prior Lean is assumed: Chapter 0 teaches the needed fragment.

## 5. Key features (bullets for the form)
- First book-length treatment unifying diagonal and topological impossibility results for ML safety.
- Every theorem machine-checked; build-time gate ties prose to kernel-accepted declarations.
- Constructive guidance: each impossibility is paired with the relaxations that remain available.
- Case studies on current proposals (J-space, CoT monitoring, ELK, watermarks) with precise statements of what they do and do not escape.
- Self-contained: includes a Lean primer; full artifact (4 libraries) is open and reproducible.

## 6. Table of contents with chapter summaries
| Ch. | Title | Summary (from the manuscript) |
|---|---|---|
| 0 | Preliminaries | Lean 4 primer: types, functions, ∀/∃, structures, inductive types, term-mode proofs; related-work positioning. |
| 1 | The Diagonal | Cantor, Russell, Gödel, Tarski, Turing, Kleene, Lawvere, Yanofsky; the shared skeleton in finite and infinite form. |
| 2 | The Classical Limits | Representability, arithmetized syntax, diagonal lemma, Gödel's second theorem machine-checked, Rice–Shapiro. |
| 3 | Three Trilemmata, One Theorem | Desiderata and precise conditions; the impossibility; the three escapes; relation to statistical inevitability results. |
| 4 | From Logic to Analysis | Connectedness, the IVT, the confidence map and truth-distance; coverage forces a confidence crossing. |
| 5 | The Geometry of Attacks | Boundary as defense fixed point; steepness forces oscillation; coarea and cone bounds; dimension of the boundary; scale. |
| 6 | Approximate Bridges to Real Models | Transfer of the exact theory to approximately continuous, finite-precision models. |
| 7 | What It Means for AI Safety | The three relaxations and their corners; abstaining wrappers; priced residual surface; cost asymmetry; clinical case study. |
| 8 | J-Space, and Why It Does Not Escape | Richness as the surjectivity hypothesis; steering; abstention as the one real exit. |
| 9 | The Trace Is Not a Window | Chain-of-thought monitoring. |
| 10 | The Reporter Is Underdetermined | Eliciting latent knowledge via a counting fact, not the diagonal. |
| 11 | Watermarks, Paraphrase, and the Third Corner | Detection under paraphrase invariance. |
| 12 | Appendices | Index of Foundation, CCHProofs, HallucinationProofs, ManifoldProofs; notation glossary. |

*Form tip: the form wants ~300–400 words per chapter. Expand the rows above from the chapter files; I can do that next.*

## 7. Audience
Primary: researchers and graduate students in AI safety, trustworthy ML, and formal methods. Secondary: logicians and mathematicians curious about applications; security researchers working on prompt-injection and agent defenses. Use as a text for a graduate seminar on the limits of AI verification. Prerequisites: sets and functions, a first logic course, basic topology.

## 8. Competing and adjacent titles **[VERIFY all before submitting]**
- Yanofsky, *The Outer Limits of Reason* (MIT Press): popular diagonal-unification; no ML safety, no machine checking.
- Avigad et al., *Mathematics in Lean* and Nipkow–Klein, *Concrete Semantics*: teach proof assistants, not AI safety.
- Hofstadter, *Gödel, Escher, Bach*: popular and non-technical.
- AI safety surveys and the statistical hallucination-inevitability papers: empirical or statistical; none machine-checked.
Positioning: no book I know of combines unified impossibility theory, AI-safety applications, and a verified artifact. **[AUTHOR: confirm with a literature sweep]**

## 9. Authors **[AUTHOR]**
- Manish Bhatt — affiliation, 3–5 line bio, relevant publications (incl. *Geometric Limits of Defense Design*, 2026).
- Ken Huang — affiliation, bio, publications.

## 10. Status and logistics
- Manuscript: complete draft; builds clean (Verso → LaTeX → PDF; HTML). **[Rebuild PDF first; repo copy dated Sep 1]**
- Format: Lean/Verso source; LaTeX output available. Ask the editor whether Springer's LaTeX template conversion is needed.
- Length: ~329 pp. Figures/tables: **[AUTHOR: count]**.
- Open artifact: GitHub repo + Zenodo DOI (to be minted). Open-access option: **[AUTHOR decide]**.
- Delivery: manuscript ready now; revisions on editor/reviewer feedback within **[AUTHOR]** weeks.
- Prior publication: parts derive from the authors' papers and these notes; confirm reuse permissions for any co-authored papers (the defense paper has seven authors).
- Competing interests statement: **[AUTHOR]**.
- Suggested reviewers: **[AUTHOR]**.

## 11. Sample chapter
Offer Ch. 3 (*Three Trilemmata, One Theorem*) or Ch. 7: both are the most self-contained statement of the thesis.
