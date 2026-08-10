"""Empirical oddness defect of negation on the truth field.

The symmetry section idealizes negation as acting oddly on delta_F.
This script measures the defect |delta_F(x) + delta_F(sigma x)| on
the matched pairs of the main experiment, relative to the endpoint
scale, from the saved interpolation curves. No model runs needed.

Output: results_oddness.json.
"""

import json
import numpy as np

out = {}
for name in ["gpt2", "pythia-410m", "qwen2.5-0.5b"]:
    z = np.load(f"curves_{name}.npz")
    D = z["D"]
    defect = np.abs(D[:, 0] + D[:, -1])
    scale = np.maximum(np.abs(D[:, 0]), np.abs(D[:, -1]))
    rel = defect / scale
    out[name] = {
        "n_paths": int(D.shape[0]),
        "median_rel_oddness_defect": round(float(np.median(rel)), 4),
        "p90_rel_oddness_defect": round(float(np.percentile(rel, 90)), 4),
    }
json.dump(out, open("results_oddness.json", "w"), indent=2)
print(json.dumps(out, indent=2))
