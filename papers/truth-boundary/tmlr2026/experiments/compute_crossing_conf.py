"""Per-path confidence at the probe's zero crossing (trained head, linear probe).

Reads curves_<model>.npz written by run_experiment.py, keeps paths whose
endpoints the probe classifies correctly (D[0] < 0 < D[-1]), and reports the
distribution of the head's confidence at argmin |D| along each path.
Writes results_crossing_conf.json.
"""
import json
import numpy as np

MODELS = ["gpt2", "pythia-410m", "qwen2.5-0.5b", "phi-1.5", "qwen2.5-1.5b"]
out = {}
for m in MODELS:
    z = np.load(f"curves_{m}.npz")
    D, C = z["D"], z["C"]
    keep = (D[:, 0] < 0) & (D[:, -1] > 0)
    D, C = D[keep], C[keep]
    c = C[np.arange(len(C)), np.abs(D).argmin(1)]
    out[m] = {
        "n_paths": int(len(c)),
        "mean_conf_at_crossing": round(float(c.mean()), 4),
        "median_conf_at_crossing": round(float(np.median(c)), 4),
        "frac_conf_in_0.4_0.6": round(float(np.mean((c >= 0.4) & (c <= 0.6))), 4),
        "frac_conf_extreme_lt0.1_or_gt0.9": round(float(np.mean((c < 0.1) | (c > 0.9))), 4),
        "frac_head_decisive_endpoints": round(float(np.mean((C[:, 0] > 0.5) & (C[:, -1] < 0.5))), 4),
    }
json.dump(out, open("results_crossing_conf.json", "w"), indent=2)
print(json.dumps(out, indent=2))
