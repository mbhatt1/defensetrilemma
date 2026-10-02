# Truth Has a Boundary — TMLR version

TMLR version of the paper. An earlier, unsubmitted draft is in `../neurreps2026/`.

- `main.tex`, `refs.bib`: manuscript (TMLR style files included). Build with
  `latexmk -pdf main.tex`. The compiled PDF is `truth_has_a_boundary_tmlr.pdf`.
- `experiments/`: the original experiment code, data, saved curves and results,
  plus new NumPy-only analyses that compute every statistic in Section 9 from
  the saved curves (no model runs):
  `compute_separation.py` (violation fraction, exact-separation rate, empirical
  truth slack), `compute_paired.py` (per-path gap vs midpoint baseline, sign
  tests), `compute_controls.py`, `compute_crossing_conf.py`. The plotting
  scripts were updated to use paper model names and a shared confidence axis.
- `supplement/`: the anonymized supplementary material to upload (Lean project
  with comment-only edits removing venue and companion-repo references, and
  the experiments with corrected docstrings). Lean code is identical to
  `proofs/HallucinationProofs` apart from comments.
- `notes/`: review history (evidence plan, adversarial review responses, and
  the audit of an intermediate draft).
