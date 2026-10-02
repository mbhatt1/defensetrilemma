"""Separation statistics for the linear readouts on a fine grid (4001 points).

For a linear probe and a logistic head, dF and logit(c) are affine along a straight
path, so each path is fixed by its endpoint values and can be evaluated at any
resolution. The 41-point grid of compute_separation.py understates violations
near the crossings; this script evaluates matched paths and cross-city paths at
4001 points and also reports:
  max_eps_hat      the largest per-path slack (the sup over the measured paths)
  frac_head_endpoint_error   paths where the head is on the wrong side of 1/2
                   at an endpoint (slack is then large by construction)
  median_eps_hat_endpoint_correct   median slack on the remaining paths
Writes results_separation_fine.json.
"""
import json
import numpy as np

MODELS = ["gpt2", "pythia-410m", "qwen2.5-0.5b", "phi-1.5", "qwen2.5-1.5b"]
N = 4001
rng = np.random.default_rng(0)


def endpoints(m):
    z = np.load(f"curves_{m}.npz")
    D, C = z["D"], z["C"]
    keep = (D[:, 0] < 0) & (D[:, -1] > 0)
    D, C = D[keep], np.clip(C[keep], 1e-12, 1 - 1e-12)
    L = np.log(C / (1 - C))
    return D[:, 0], D[:, -1], L[:, 0], L[:, -1]


def path_stats(d0, d1, l0, l1, chunk=2000):
    a = np.linspace(0, 1, N)[None, :]
    vf, ex, eps = [], [], []
    for s in range(0, len(d0), chunk):
        e = slice(s, s + chunk)
        D = (1 - a) * d0[e, None] + a * d1[e, None]
        Lg = (1 - a) * l0[e, None] + a * l1[e, None]
        v = ((D < 0) & (Lg <= 0)) | ((D > 0) & (Lg >= 0))
        sc = np.maximum(np.abs(d0[e]), np.abs(d1[e]))
        vf.append(v.mean(1)); ex.append(~v.any(1))
        eps.append(np.where(v.any(1), np.where(v, np.abs(D), 0).max(1) / sc, 0.0))
    return np.concatenate(vf), np.concatenate(ex), np.concatenate(eps)


def ci(x, f=np.median, B=10000):
    idx = rng.integers(0, len(x), size=(B, len(x)))
    s = f(x[idx], axis=1)
    return [round(float(np.percentile(s, 2.5)), 4), round(float(np.percentile(s, 97.5)), 4)]


r4 = lambda x: round(float(x), 4)
out = {}
for m in MODELS:
    d0, d1, l0, l1 = endpoints(m)
    n = len(d0)
    vf, ex, eps = path_stats(d0, d1, l0, l1)
    head_err = ~((l0 > 0) & (l1 < 0))
    rec = {
        "n_paths": int(n), "grid_points": N,
        "frac_paths_exact": r4(ex.mean()),
        "mean_viol_frac": r4(vf.mean()), "mean_viol_frac_ci95": ci(vf, np.mean),
        "median_eps_hat": r4(np.median(eps)), "median_eps_hat_ci95": ci(eps),
        "max_eps_hat": r4(eps.max()),
        "frac_head_endpoint_error": r4(head_err.mean()),
        "median_eps_hat_head_endpoint_error": r4(np.median(eps[head_err])) if head_err.any() else None,
        "median_eps_hat_endpoint_correct": r4(np.median(eps[~head_err])),
        "median_eps_hat_endpoint_correct_ci95": ci(eps[~head_err]),
    }
    # cross-city paths at the same resolution, with a bootstrap over cities
    I, J = np.where(~np.eye(n, dtype=bool))
    _, exc, epsc = path_stats(d0[I], d1[J], l0[I], l1[J])
    cell = {(i, j): k for k, (i, j) in enumerate(zip(I, J))}
    boots = []
    for _ in range(300):
        s = rng.integers(0, n, n)
        ii, jj = np.meshgrid(s, s, indexing="ij")
        mask = ii != jj
        ks = [cell[(i, j)] for i, j in zip(ii[mask], jj[mask])]
        boots.append(np.median(epsc[ks]))
    rec["cross"] = {"n_paths": int(len(I)), "frac_paths_exact": r4(exc.mean()),
                    "median_eps_hat": r4(np.median(epsc)),
                    "median_eps_hat_ci95_cluster": [r4(np.percentile(boots, 2.5)), r4(np.percentile(boots, 97.5))]}
    out[m] = rec
json.dump(out, open("results_separation_fine.json", "w"), indent=2)
for m, v in out.items():
    print(m, {k: v[k] for k in ("n_paths","frac_paths_exact","mean_viol_frac","median_eps_hat","median_eps_hat_ci95","max_eps_hat","frac_head_endpoint_error","median_eps_hat_head_endpoint_error","median_eps_hat_endpoint_correct","median_eps_hat_endpoint_correct_ci95")}, v["cross"])
