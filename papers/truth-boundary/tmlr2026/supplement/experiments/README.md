# Experiments (anonymized supplement)

These scripts measure how far five small language models are from the
paper's separation premise. Theorems in the paper do not depend on any
experiment.

## Model runs (need a GPU or Apple MPS, Hugging Face access)
- `run_experiment.py`: trained linear readouts; writes `results.json`, `curves_<model>.npz`.
- `run_endogenous.py`: model's own p("true") and null heads; writes `results_endogenous.json`, `curves_endog_<model>.npz`.
- `run_nonlinear.py`: MLP readouts; writes `results_nonlinear.json`, `curves_mlp_<model>.npz`.
- `run_gap_experiments.py`: translation dataset and kNN diagnostic; writes `results_gaps.json`.
- `run_layer_sweep.py`: Phi-1.5 layer sweep; writes `results_layer_sweep.json`.
- `run_adversarial.py`: exploratory run, appendix only; writes `results_adversarial.json`.

## Analyses from saved curves (CPU, NumPy only; reproduce every number in Section 9)
- `compute_separation.py`: violation fraction, exact-separation rate, empirical truth slack (Tables 2 and 3).
- `compute_crosspairs.py`: separation statistics on unmatched (cross-city) paths, linear readouts.
- `compute_paired.py`: per-path crossing gap vs midpoint baseline, exact sign tests (Section 9.5).
- `compute_controls.py`: gaps on separating paths and midpoint baseline (Appendix Table 4).
- `compute_crossing_conf.py`: confidence at the probe's zero crossing.
- `compute_bootstrap.py`, `compute_oddness.py`: gap intervals and oddness defect.
- `plot_figure.py`, `plot_endogenous.py`, `make_schematic.py`: figures.

## Data
`data/` holds the `cities`, `neg_cities`, `sp_en_trans` and `neg_sp_en_trans`
statement sets of Marks & Tegmark (2024).

## Environment
Python with numpy, pandas, scikit-learn, scipy, torch, transformers and
matplotlib. Package versions and hardware for the original model runs
were not recorded. The analysis scripts need only numpy (and matplotlib
for figures).
