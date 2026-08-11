"""Full linear-probe layer sweep for a model.

Probes every hidden layer with the same linear pipeline as
run_experiment.py and records validation and test accuracy per layer.
Backs the paper's claim that Phi-1.5's weak linear separability is a
property of the model on this domain, not of the layer choice.

Usage: python3 run_layer_sweep.py [hf_model_id]
Default model: microsoft/phi-1_5.
Output: results_layer_sweep.json (keyed by model id).
"""

import json
import sys
import numpy as np
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
import run_experiment as E

HF_ID = sys.argv[1] if len(sys.argv) > 1 else "microsoft/phi-1_5"

df = E.load_data()
tok = AutoTokenizer.from_pretrained(HF_ID)
if tok.pad_token is None:
    tok.pad_token = tok.eos_token
tok.padding_side = "right"
model = AutoModelForCausalLM.from_pretrained(
    HF_ID, torch_dtype=torch.float32).to(E.DEVICE).eval()
n_layers = model.config.num_hidden_layers

stmts = list(df["pos_stmt"]) + list(df["neg_stmt"])
labels = np.array(list(df["pos_label"]) + list(df["neg_label"]))
split = np.array(list(df["split"]) + list(df["split"]))
H = E.embed(model, tok, stmts, list(range(1, n_layers + 1)))

rows = []
for L in range(1, n_layers + 1):
    h = H[L]
    sc = StandardScaler().fit(h[split == "A"])
    p = LogisticRegression(max_iter=2000).fit(
        sc.transform(h[split == "A"]), labels[split == "A"])
    va = p.score(sc.transform(h[split == "val"]), labels[split == "val"])
    ta = p.score(sc.transform(h[split == "test"]), labels[split == "test"])
    rows.append({"layer": L, "val_acc": round(float(va), 4),
                 "test_acc": round(float(ta), 4)})
    print(f"layer {L}: val {va:.3f} test {ta:.3f}", flush=True)

try:
    out = json.load(open("results_layer_sweep.json"))
except FileNotFoundError:
    out = {}
out[HF_ID] = {
    "n_layers": n_layers,
    "per_layer": rows,
    "max_test_acc": max(r["test_acc"] for r in rows),
}
json.dump(out, open("results_layer_sweep.json", "w"), indent=2)
print("max test acc:", out[HF_ID]["max_test_acc"])
