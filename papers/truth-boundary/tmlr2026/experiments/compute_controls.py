"""Control analyses on the saved interpolation curves (no model runs).

For each readout family (linear, mlp, endogenous) and model:
  gap         median |alpha*(dF) - alpha*(c)| on the 41-point grid
  mid         midpoint baseline: median |alpha*(dF) - 0.5|, i.e. the gap a
              confidence readout with no truth information would obtain if it
              always crossed 1/2 at the path midpoint
  *_sep       the same restricted to paths where c is on the correct side of
              1/2 at both endpoints (endpoint separation)
  cont_gap_sep  gap using closed-form crossings of the endpoint-affine dF and
              logit(c) (exact for linear readouts on linear paths)
Writes results_controls.json.
"""
import json
import numpy as np

MODELS = ["gpt2", "pythia-410m", "qwen2.5-0.5b", "phi-1.5", "qwen2.5-1.5b"]
FAMILIES = {"linear": "curves_{}.npz", "mlp": "curves_mlp_{}.npz",
            "endogenous": "curves_endog_{}.npz"}


def med(x):
    return round(float(np.median(x)), 4) if len(x) else None


out = {}
for fam, pat in FAMILIES.items():
    out[fam] = {}
    for m in MODELS:
        z = np.load(pat.format(m))
        D, C, al = z["D"], z["C"], z["alphas"]
        keep = (D[:, 0] < 0) & (D[:, -1] > 0)
        D, C = D[keep], C[keep]
        ad = al[np.abs(D).argmin(1)]
        ac = al[np.abs(C - 0.5).argmin(1)]
        sep = (C[:, 0] > 0.5) & (C[:, -1] < 0.5)
        lc = np.log(np.clip(C, 1e-12, 1) / np.clip(1 - C, 1e-12, 1))
        tD = -D[:, 0] / (D[:, -1] - D[:, 0])
        with np.errstate(divide="ignore", invalid="ignore"):
            tC = -lc[:, 0] / (lc[:, -1] - lc[:, 0])
        out[fam][m] = {
            "n_paths": int(len(D)), "n_sep": int(sep.sum()),
            "gap": med(np.abs(ad - ac)), "mid": med(np.abs(ad - 0.5)),
            "gap_sep": med(np.abs(ad - ac)[sep]), "mid_sep": med(np.abs(ad - 0.5)[sep]),
            "gap_nonsep": med(np.abs(ad - ac)[~sep]),
            "cont_gap_sep": med(np.abs(tD - tC)[sep]),
        }
json.dump(out, open("results_controls.json", "w"), indent=2)
for fam in out:
    print(fam)
    for m, v in out[fam].items():
        print(f"  {m:13s}", v)
