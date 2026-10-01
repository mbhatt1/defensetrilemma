"""Cross-city robustness check for the separation statistics (linear readouts only).

For a linear probe and a logistic head, dF and logit(c) are affine along a straight
path, so the whole path is determined by the readout values at its two endpoints.
The saved curves give those values for each kept test city's true affirmative
(alpha = 0) and its negation (alpha = 1). This script builds paths from the true
affirmative of city i to the negation of city j, for all i != j, and recomputes
the separation statistics of compute_separation.py on them.

Caveat: every stored statement is a true affirmative or a false negation, so these
paths still flip truth and polarity together. The check tests whether the results
depend on the matched-negation pairing, not whether they survive decoupling.
Writes results_crosspairs.json.
"""
import json
import numpy as np

MODELS = ["gpt2", "pythia-410m", "qwen2.5-0.5b", "phi-1.5", "qwen2.5-1.5b"]
ALPHAS = np.linspace(0, 1, 41)
rng = np.random.default_rng(0)


def stats(d0, d1, l0, l1):
    """Separation statistics for paths with endpoint values (d0,l0) -> (d1,l1)."""
    a = ALPHAS[None, :]
    D = (1 - a) * d0[:, None] + a * d1[:, None]
    L = (1 - a) * l0[:, None] + a * l1[:, None]          # logit(c) - logit(1/2)
    viol = ((D < 0) & (L <= 0)) | ((D > 0) & (L >= 0))
    scale = np.maximum(np.abs(d0), np.abs(d1))
    eps = np.where(viol.any(1), np.where(viol, np.abs(D), 0).max(1) / scale, 0.0)
    return viol.mean(1), ~viol.any(1), eps


out = {}
for m in MODELS:
    z = np.load(f"curves_{m}.npz")
    D, C = z["D"], z["C"]
    keep = (D[:, 0] < 0) & (D[:, -1] > 0)
    D, C = D[keep], C[keep]
    Cc = np.clip(C, 1e-12, 1 - 1e-12)
    Lg = np.log(Cc / (1 - Cc))
    d0, d1, l0, l1 = D[:, 0], D[:, -1], Lg[:, 0], Lg[:, -1]
    n = len(d0)

    # sanity: affine reconstruction of the matched paths reproduces the saved curves
    vf_m, ex_m, eps_m = stats(d0, d1, l0, l1)
    viol_saved = ((D < 0) & (C <= 0.5)) | ((D > 0) & (C >= 0.5))
    agree = float((viol_saved.mean(1) == vf_m).mean())

    I, J = np.where(~np.eye(n, dtype=bool))
    vf, ex, eps = stats(d0[I], d1[J], l0[I], l1[J])

    # cluster bootstrap over cities (resample cities, keep all cross pairs among them)
    boots = []
    for _ in range(2000):
        s = rng.integers(0, n, n)
        ii, jj = np.meshgrid(s, s, indexing="ij")
        mask = ii != jj
        e = np.abs(stats(d0[ii[mask]], d1[jj[mask]], l0[ii[mask]], l1[jj[mask]])[2])
        boots.append(np.median(e))
    out[m] = {
        "n_cities": int(n), "n_cross_paths": int(len(I)),
        "matched_reconstruction_agreement": round(agree, 4),
        "matched": {"frac_paths_exact": round(float(ex_m.mean()), 4),
                    "mean_viol_frac": round(float(vf_m.mean()), 4),
                    "median_eps_hat": round(float(np.median(eps_m)), 4)},
        "cross": {"frac_paths_exact": round(float(ex.mean()), 4),
                  "mean_viol_frac": round(float(vf.mean()), 4),
                  "median_eps_hat": round(float(np.median(eps)), 4),
                  "median_eps_hat_ci95_cluster": [round(float(np.percentile(boots, 2.5)), 4),
                                                  round(float(np.percentile(boots, 97.5)), 4)],
                  "p90_eps_hat": round(float(np.percentile(eps, 90)), 4)},
    }
json.dump(out, open("results_crosspairs.json", "w"), indent=2)
for m, v in out.items():
    print(f"{m:13s} cities={v['n_cities']:3d} cross={v['n_cross_paths']:6d} recon={v['matched_reconstruction_agreement']:.3f} | "
          f"matched exact={v['matched']['frac_paths_exact']:.2f} viol={v['matched']['mean_viol_frac']:.3f} eps={v['matched']['median_eps_hat']:.3f} | "
          f"cross exact={v['cross']['frac_paths_exact']:.2f} viol={v['cross']['mean_viol_frac']:.3f} eps={v['cross']['median_eps_hat']:.3f} {v['cross']['median_eps_hat_ci95_cluster']} p90={v['cross']['p90_eps_hat']:.3f}")
