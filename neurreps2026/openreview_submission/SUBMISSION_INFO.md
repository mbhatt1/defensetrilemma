# OpenReview Submission Crib Sheet — NeurReps 2026

**Deadline: August 22, 2026 (AoE). Notification: September 29, 2026.**

Portal (Proceedings Track):
https://openreview.net/group?id=NeurIPS.cc/2026/Workshop/NeurReps_Proceedings

(If switching to the Extended Abstract Track — no dual-submission
restrictions, 4-page limit, requires cutting the paper and changing the
documentclass option from `mlmain` to `mlabstract`:
https://openreview.net/group?id=NeurIPS.cc/2026/Workshop/NeurReps_Extended_Abstracts)

## Files in this folder

| File | Purpose |
|---|---|
| `neurreps_truth_boundary.pdf` | Main submission PDF (anonymized, review watermark on) |
| `supplementary.zip` | Anonymized Lean 4 artifact + sub-1B experiment (code, data, results, figure) + reviewer README |
| `source.zip` | LaTeX source + class/style files (for camera-ready; not usually uploaded at submission) |

## Form fields

**Title**
Truth Has a Boundary. A Machine-Verified Topological Constraint on Models That Separate Truth from Falsehood

**TL;DR (one sentence)**
We prove, and machine-verify in Lean 4, a convention-free coupling theorem. Any continuous model on a connected representation space whose confidence separates truth from falsehood must have a query with exact threshold confidence exactly on the truth boundary, with quantitative width bounds and a corollary taxonomy for every guarantee policy.

**Keywords**
representational geometry, topology, uncertainty, calibration, intermediate value theorem, Borsuk-Ulam, formal verification, Lean

**Abstract** (plain text, matches the PDF)
Probing studies read truth off a language model's activations, treating truth as a continuous decodable field over representation space. We ask what the shape of that space requires of any model answering over it. Our central result is a coupling theorem. If a continuous model on a connected representation space ever answers truly and ever answers falsely, and its confidence separates true answers from false ones, then some query must carry confidence exactly at the decision threshold while its answer sits exactly on the truth boundary. The theorem mentions no safety guarantee, so it does not depend on how a guarantee treats its own threshold. A guarantee including its threshold is impossible, and one excluding it survives but is silent at the coupled query. Under Lipschitz regularity the coupled point sits inside an ambiguity tube of computable width, any feasible system must carry strictly positive truth-side slack, and for nonzero linear probes the truth boundary is an affine hyperplane of codimension one. A symmetry version needs no coverage assumption, a discrete analysis prices the removal of topology, and multi-turn and stochastic extensions follow, with the stochastic dichotomy deriving falsehood. We machine-verify every theorem in Lean 4 against Mathlib with no sorry placeholders, and the main results reduce to the three standard kernel axioms. Experiments observe the predicted coupling in five small language models, with the model's own confidence signal and against null baselines, and an adversarial attempt to train away the slack plateaus strictly above zero.

## Pre-submission checklist

- [ ] All authors have OpenReview profiles (required for Proceedings/Extended Abstract tracks)
- [ ] Proceedings track: confirm the >=30% new-material requirement is satisfied relative to any prior/concurrent publication of the trilemma results
- [ ] Upload `neurreps_truth_boundary.pdf` as the submission PDF
- [ ] Upload `supplementary.zip` as supplementary material
- [ ] Do NOT include author names anywhere (PDF and supplementary are already anonymized)
- [ ] Body is 9 pages (pages 1-9, limit is 9), experiments now in the main body; references and appendices excluded — compliant

## Camera-ready (only if accepted)

1. In `neurreps_truth_boundary.tex`: remove the 4 `draftwatermark` lines (marked in the preamble).
2. Uncomment/add the author block (`\Name{...} \Email{...} \addr ...`) per the template sample.
3. Add acknowledgments and, if desired, a de-anonymized code link (also in the `%%% Link to code:` comment for the organizers).
4. Rebuild: `pdflatex`, `bibtex`, `pdflatex` x2 (style files are in `source.zip`).
