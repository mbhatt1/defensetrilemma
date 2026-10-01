"""Direct measurement of the separation premise along saved interpolation paths.

Exact separation at tau = 1/2 requires, at every point x:
    dF(x) < 0  =>  c(x) > 1/2      and      dF(x) > 0  =>  c(x) < 1/2.
For each kept path (probe correct at both endpoints) we compute on the 41-point grid:
  viol_frac   fraction of points violating the premise
  exact       whether the path has no violating point (separation holds on the grid)
  eps_hat     smallest truth slack eps for which (eps, 0)-separation holds on the path:
              max |dF| over violating points, divided by the endpoint scale
              max(|dF(start)|, |dF(end)|); 0 if no violation.
Under exact separation the theory forces c = 1/2 exactly where dF = 0 (Theorem 2);
eps_hat measures how far each readout pair is from that premise, in units of the
truth field.  No baseline is involved: these are measurements of a hypothesis.
Writes results_separation.json.
"""
import json
import numpy as np

MODELS = ["gpt2", "pythia-410m", "qwen2.5-0.5b", "phi-1.5", "qwen2.5-1.5b"]
FAMILIES = {"linear": "curves_{}.npz", "mlp": "curves_mlp_{}.npz",
            "endogenous": "curves_endog_{}.npz"}
rng = np.random.default_rng(0)


def boot_ci(x, f=np.median, B=10000):
    if len(x) == 0:
        return None
    idx = rng.integers(0, len(x), size=(B, len(x)))
    s = f(x[idx], axis=1)
    return [round(float(np.percentile(s, 2.5)), 4), round(float(np.percentile(s, 97.5)), 4)]


out = {}
for fam, pat in FAMILIES.items():
    out[fam] = {}
    for m in MODELS:
        z = np.load(pat.format(m))
        D, C = z["D"], z["C"]
        keep = (D[:, 0] < 0) & (D[:, -1] > 0)
        D, C = D[keep], C[keep]
        viol = ((D < 0) & (C <= 0.5)) | ((D > 0) & (C >= 0.5))
        scale = np.maximum(np.abs(D[:, 0]), np.abs(D[:, -1]))
        eps = np.array([np.abs(d[v]).max() / s if v.any() else 0.0
                        for d, v, s in zip(D, viol, scale)])
        vf = viol.mean(1)
        out[fam][m] = {
            "n_paths": int(len(D)),
            "frac_paths_exact": round(float((~viol.any(1)).mean()), 4),
            "median_viol_frac": round(float(np.median(vf)), 4),
            "mean_viol_frac": round(float(vf.mean()), 4),
            "mean_viol_frac_ci95": boot_ci(vf, np.mean),
            "median_eps_hat": round(float(np.median(eps)), 4),
            "median_eps_hat_ci95": boot_ci(eps),
            "p90_eps_hat": round(float(np.percentile(eps, 90)), 4),
        }
json.dump(out, open("results_separation.json", "w"), indent=2)
for fam in out:
    print(fam)
    for m, v in out[fam].items():
        print(f"  {m:13s} n={v['n_paths']:3d} exact={v['frac_paths_exact']:.2f} "
              f"viol mean={v['mean_viol_frac']:.3f} {v['mean_viol_frac_ci95']} "
              f"eps med={v['median_eps_hat']:.3f} {v['median_eps_hat_ci95']} p90={v['p90_eps_hat']:.3f}")
