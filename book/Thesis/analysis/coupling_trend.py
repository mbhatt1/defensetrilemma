#!/usr/bin/env python3
"""
Reproduce the capability-ladder table of the empirical chapter.

Reads only artifacts already committed under
papers/truth-boundary/neurreps2026/experiments/; runs no model inference.

    python3 Thesis/analysis/coupling_trend.py
"""
import json
import math
import os

EXP = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "..", "..", "..", "papers", "truth-boundary", "neurreps2026", "experiments",
)

# Parameter counts in billions, from the model cards of the released checkpoints.
PARAMS = {
    "gpt2": 0.124,
    "pythia-410m": 0.41,
    "qwen2.5-0.5b": 0.5,
    "phi-1.5": 1.3,
    "qwen2.5-1.5b": 1.5,
}


def load(name):
    with open(os.path.join(EXP, name)) as fh:
        return json.load(fh)


def pearson(x, y):
    n = len(x)
    mx, my = sum(x) / n, sum(y) / n
    num = sum((a - mx) * (b - my) for a, b in zip(x, y))
    den = math.sqrt(sum((a - mx) ** 2 for a in x) * sum((b - my) ** 2 for b in y))
    return num / den


def main():
    boot = load("results_bootstrap.json")
    odd = load("results_oddness.json")
    endo = load("results_endogenous.json")

    rows = []
    for m in sorted(PARAMS, key=PARAMS.get):
        e = endo.get(m, {}).get("endogenous", {})
        rows.append({
            "model": m,
            "params": PARAMS[m],
            "gap_linear": boot[m]["linear"]["median"],
            "gap_linear_ci": boot[m]["linear"]["ci95"],
            "gap_endog": (boot[m].get("endogenous") or {}).get("median"),
            "gap_endog_ci": (boot[m].get("endogenous") or {}).get("ci95"),
            "frac_decisive": e.get("frac_decisive"),
            "oddness": odd[m]["median_rel_oddness_defect"],
            "probe_acc": e.get("template_probe_test_acc"),
        })

    hdr = f"{'model':16}{'B':>6}{'eps_endog':>11}{'ci95':>16}{'decisive':>10}{'oddness':>9}{'probe':>8}"
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        ge = "--" if r["gap_endog"] is None else f"{r['gap_endog']:.3f}"
        ci = "--" if r["gap_endog_ci"] is None else str(r["gap_endog_ci"])
        fd = "--" if r["frac_decisive"] is None else f"{r['frac_decisive']:.3f}"
        pa = "--" if r["probe_acc"] is None else f"{r['probe_acc']:.3f}"
        print(f"{r['model']:16}{r['params']:>6}{ge:>11}{ci:>16}{fd:>10}{r['oddness']:>9.3f}{pa:>8}")

    # Trend, with and without the outlier. Reported both ways in the text.
    lp = [math.log(r["params"]) for r in rows]
    gl = [r["gap_linear"] for r in rows]
    keep = [i for i, r in enumerate(rows) if r["model"] != "phi-1.5"]
    print()
    print(f"Pearson r(log params, linear-probe gap), all five     : {pearson(lp, gl):+.3f}")
    print(f"Pearson r(log params, linear-probe gap), without Phi  : "
          f"{pearson([lp[i] for i in keep], [gl[i] for i in keep]):+.3f}")


if __name__ == "__main__":
    main()
