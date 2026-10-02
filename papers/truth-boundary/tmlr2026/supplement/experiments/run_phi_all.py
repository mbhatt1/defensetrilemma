"""Run Phi-1.5 (microsoft/phi-1_5, 1.3B) through every experiment and
merge its results into the existing json files. Reuses each experiment
module directly so the pipeline is identical to the other models."""

import json

PHI = "phi-1.5"
PHI_ID = "microsoft/phi-1_5"


def merge(path, key, value):
    d = json.load(open(path))
    d[key] = value
    json.dump(d, open(path, "w"), indent=2)
    print(f"merged {key} into {path}", flush=True)


# 1. Main trained-head experiment (also selects the layer).
import run_experiment as E
df = E.load_data()
res = E.run_model(PHI, PHI_ID, df)
merge("results.json", PHI, res)
LAYER = res["layer"]
print(f"phi layer selected: {LAYER}", flush=True)

# 2. Endogenous confidence + null baselines.
import run_endogenous as N
N.MODELS[PHI] = (PHI_ID, LAYER)
df2 = N.load_data()
entry = {}
entry["endogenous"] = N.run_endogenous(PHI, PHI_ID, LAYER, df2)
entry["nulls"] = N.run_nulls(PHI, PHI_ID, df2)
merge("results_endogenous.json", PHI, entry)

# 3. Spanish-English replication + kNN diagnostic.
import run_gap_experiments as G
G.MODELS[PHI] = (PHI_ID, LAYER)
entry = {}
entry["sp_en"] = G.spen_replication(PHI, PHI_ID, LAYER)
entry["knn"] = G.knn_diagnostic(PHI, PHI_ID, LAYER)
merge("results_gaps.json", PHI, entry)

# 4. Nonlinear probes.
import run_nonlinear as L
df3 = L.load_data()
merge("results_nonlinear.json", PHI, L.run_model(PHI, PHI_ID, LAYER, df3))

# 5. Adversarial falsification.
import run_adversarial as A
df4 = A.load_data()
merge("results_adversarial.json", PHI, A.run_model(PHI, PHI_ID, LAYER, df4))

print("PHI PIPELINE COMPLETE", flush=True)
