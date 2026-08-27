"""Run Qwen2.5-1.5B through every experiment and merge its results,
mirroring run_phi_all.py. Gives a within-family scale comparison
against Qwen2.5-0.5B."""

import json

NAME = "qwen2.5-1.5b"
HF_ID = "Qwen/Qwen2.5-1.5B"


def merge(path, key, value):
    d = json.load(open(path))
    d[key] = value
    json.dump(d, open(path, "w"), indent=2)
    print(f"merged {key} into {path}", flush=True)


import run_experiment as E
df = E.load_data()
res = E.run_model(NAME, HF_ID, df)
merge("results.json", NAME, res)
LAYER = res["layer"]
print(f"{NAME} layer selected: {LAYER}", flush=True)

import run_endogenous as N
N.MODELS[NAME] = (HF_ID, LAYER)
df2 = N.load_data()
entry = {}
entry["endogenous"] = N.run_endogenous(NAME, HF_ID, LAYER, df2)
entry["nulls"] = N.run_nulls(NAME, HF_ID, df2)
merge("results_endogenous.json", NAME, entry)

import run_gap_experiments as G
G.MODELS[NAME] = (HF_ID, LAYER)
entry = {}
entry["sp_en"] = G.spen_replication(NAME, HF_ID, LAYER)
entry["knn"] = G.knn_diagnostic(NAME, HF_ID, LAYER)
merge("results_gaps.json", NAME, entry)

import run_nonlinear as L
df3 = L.load_data()
merge("results_nonlinear.json", NAME, L.run_model(NAME, HF_ID, LAYER, df3))

import run_adversarial as A
df4 = A.load_data()
merge("results_adversarial.json", NAME, A.run_model(NAME, HF_ID, LAYER, df4))

print("QWEN15 PIPELINE COMPLETE", flush=True)
