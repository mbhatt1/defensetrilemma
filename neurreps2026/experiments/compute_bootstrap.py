"""Bootstrap confidence intervals for the crossing-gap statistics.

Resamples paths with replacement (10,000 replicates) from the saved
interpolation curves of the trained-head, MLP, and endogenous
experiments and reports 95 percent percentile intervals for the
median crossing gap. No model runs needed.

Output: results_bootstrap.json.
"""

import json
import numpy as np

rng = np.random.default_rng(0)
B = 10000


def gap_stat(D, C, alphas, thresh=0.5):
    cd = np.array([np.argmin(np.abs(d)) for d in D])
    cc = np.array([np.argmin(np.abs(c - thresh)) for c in C])
    return np.abs(alphas[cd] - alphas[cc])


def boot_ci(gaps):
    n = len(gaps)
    meds = np.median(gaps[rng.integers(0, n, size=(B, n))], axis=1)
    return [round(float(np.percentile(meds, 2.5)), 3),
            round(float(np.percentile(meds, 97.5)), 3)]


out = {}
for name in ["gpt2", "pythia-410m", "qwen2.5-0.5b", "phi-1.5"]:
    entry = {}
    z = np.load(f"curves_{name}.npz")
    g = gap_stat(z["D"], z["C"], z["alphas"])
    entry["linear"] = {"median": round(float(np.median(g)), 3),
                       "ci95": boot_ci(g)}
    z = np.load(f"curves_mlp_{name}.npz")
    g = gap_stat(z["D"], z["C"], z["alphas"])
    entry["mlp"] = {"median": round(float(np.median(g)), 3),
                    "ci95": boot_ci(g)}
    z = np.load(f"curves_endog_{name}.npz")
    dec = z["decisive"]
    if dec.any():
        g = gap_stat(z["D"][dec], z["C"][dec], z["alphas"])
        entry["endogenous"] = {"median": round(float(np.median(g)), 3),
                               "ci95": boot_ci(g)}
    else:
        entry["endogenous"] = None
    out[name] = entry
json.dump(out, open("results_bootstrap.json", "w"), indent=2)
print(json.dumps(out, indent=2))
