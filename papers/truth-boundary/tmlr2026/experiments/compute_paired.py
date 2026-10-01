"""Paired per-path comparison of the crossing gap with the midpoint baseline,
on endpoint-separating paths, with exact two-sided sign tests.
Writes results_paired.json."""
import json
from math import comb
import numpy as np

MODELS = ["gpt2", "pythia-410m", "qwen2.5-0.5b", "phi-1.5", "qwen2.5-1.5b"]
FAMILIES = {"linear": "curves_{}.npz", "mlp": "curves_mlp_{}.npz",
            "endogenous": "curves_endog_{}.npz"}


def sign_p(k, n):
    if n == 0:
        return None
    t = sum(comb(n, i) for i in range(0, min(k, n - k) + 1)) / 2 ** n * 2
    return min(1.0, t)


out = {}
for fam, pat in FAMILIES.items():
    out[fam] = {}
    for m in MODELS:
        z = np.load(pat.format(m))
        D, C, al = z["D"], z["C"], z["alphas"]
        keep = (D[:, 0] < 0) & (D[:, -1] > 0)
        D, C = D[keep], C[keep]
        sep = (C[:, 0] > 0.5) & (C[:, -1] < 0.5)
        if not sep.any():
            out[fam][m] = None
            continue
        ad = al[np.abs(D).argmin(1)][sep]
        ac = al[np.abs(C - 0.5).argmin(1)][sep]
        gap, mid = np.abs(ad - ac), np.abs(ad - 0.5)
        worse, better = int((gap > mid).sum()), int((gap < mid).sum())
        p = sign_p(better, worse + better)
        out[fam][m] = {"n_sep": int(sep.sum()), "head_worse": worse,
                       "head_better": better, "ties": int((gap == mid).sum()),
                       "sign_test_p": round(p, 5)}
json.dump(out, open("results_paired.json", "w"), indent=2)
print(json.dumps(out, indent=1))
