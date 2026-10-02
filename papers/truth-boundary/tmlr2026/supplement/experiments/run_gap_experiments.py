"""Second-dataset replication and kNN component diagnostic.

Part A. Replicate the trained-head boundary-coupling pipeline of
run_experiment.py on the Spanish-English translation statements
(sp_en_trans + neg_sp_en_trans from the geometry-of-truth datasets).
No city structure exists here, so splits are by statement index.

Part B. Diagnose the kNN connectivity check from run_experiment.py.
For each connected component of the 10-NN graph on held-out cities
activations, report its composition by truth label and by surface
form (positive statement vs negation). This answers what the second
component contains when one appears.

Outputs: results_gaps.json.
"""

import json
import numpy as np
import pandas as pd
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
from sklearn.neighbors import kneighbors_graph
from scipy.sparse.csgraph import connected_components

DEVICE = "mps" if torch.backends.mps.is_available() else "cpu"
MODELS = {
    "gpt2": ("gpt2", 9),
    "pythia-410m": ("EleutherAI/pythia-410m", 18),
    "qwen2.5-0.5b": ("Qwen/Qwen2.5-0.5B", 12),
    "phi-1.5": ("microsoft/phi-1_5", 18),
    "qwen2.5-1.5b": ("Qwen/Qwen2.5-1.5B", 14),
}
N_ALPHA = 41


def load_spen():
    pos = pd.read_csv("data/sp_en_trans.csv")
    neg = pd.read_csv("data/neg_sp_en_trans.csv")
    df = pd.DataFrame({
        "pos_stmt": pos["statement"], "pos_label": pos["label"],
        "neg_stmt": neg["statement"], "neg_label": neg["label"],
    })
    rng = np.random.default_rng(0)
    idx = rng.permutation(len(df))
    n = len(df)
    splits = np.empty(n, dtype=object)
    splits[idx[: n // 5]] = "test"
    splits[idx[n // 5: n // 5 + n // 10]] = "val"
    splits[idx[n // 5 + n // 10: n // 2]] = "B"
    splits[idx[n // 2:]] = "A"
    df["split"] = splits
    return df


def load_cities():
    cities = pd.read_csv("data/cities.csv")
    neg = pd.read_csv("data/neg_cities.csv")
    df = pd.DataFrame({
        "pos_stmt": cities["statement"], "pos_label": cities["label"],
        "neg_stmt": neg["statement"], "neg_label": neg["label"],
        "city": cities["city"],
    })
    rng = np.random.default_rng(0)
    ucities = df["city"].unique()
    rng.shuffle(ucities)
    n = len(ucities)
    test_c = set(ucities[: n // 5])
    df["is_test"] = df["city"].isin(test_c)
    return df


@torch.no_grad()
def embed_raw(model, tok, texts, layer, batch=32):
    out = []
    for i in range(0, len(texts), batch):
        enc = tok(texts[i:i + batch], return_tensors="pt",
                  padding=True).to(DEVICE)
        o = model(**enc, output_hidden_states=True)
        idx = enc["attention_mask"].sum(1) - 1
        rows = torch.arange(len(enc["input_ids"]), device=DEVICE)
        out.append(o.hidden_states[layer][rows, idx].float().cpu())
    return torch.cat(out).numpy()


def load_model(hf_id):
    tok = AutoTokenizer.from_pretrained(hf_id)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    tok.padding_side = "right"
    model = AutoModelForCausalLM.from_pretrained(
        hf_id, torch_dtype=torch.float32).to(DEVICE).eval()
    return tok, model


def spen_replication(name, hf_id, layer):
    print(f"=== sp_en {name} ===", flush=True)
    df = load_spen()
    tok, model = load_model(hf_id)
    stmts = list(df["pos_stmt"]) + list(df["neg_stmt"])
    labels = np.array(list(df["pos_label"]) + list(df["neg_label"]))
    split = np.array(list(df["split"]) + list(df["split"]))
    H = embed_raw(model, tok, stmts, layer)

    scA = StandardScaler().fit(H[split == "A"])
    probe = LogisticRegression(max_iter=2000, random_state=0).fit(
        scA.transform(H[split == "A"]), labels[split == "A"])
    scB = StandardScaler().fit(H[split == "B"])
    head = LogisticRegression(max_iter=2000, random_state=1).fit(
        scB.transform(H[split == "B"]), labels[split == "B"])
    te = split == "test"
    probe_acc = probe.score(scA.transform(H[te]), labels[te])
    head_acc = head.score(scB.transform(H[te]), labels[te])

    def delta_F(h):
        return -(scA.transform(h) @ probe.coef_[0] + probe.intercept_[0])

    def conf(h):
        return head.predict_proba(scB.transform(h))[:, 1]

    pairs = df[(df["split"] == "test") & (df["pos_label"] == 1)]
    pos_index = {s: i for i, s in enumerate(stmts)}
    alphas = np.linspace(0, 1, N_ALPHA)
    D, C = [], []
    for _, row in pairs.iterrows():
        h0 = H[pos_index[row["pos_stmt"]]]
        h1 = H[pos_index[row["neg_stmt"]]]
        path = np.stack([(1 - a) * h0 + a * h1 for a in alphas])
        D.append(delta_F(path))
        C.append(conf(path))
    D, C = np.stack(D), np.stack(C)
    valid = (D[:, 0] < 0) & (D[:, -1] > 0)
    Dv, Cv = D[valid], C[valid]
    sign_change = float(np.mean(
        [(np.diff(np.sign(d)) != 0).any() for d in Dv]))
    cross_d = np.array([np.argmin(np.abs(d)) for d in Dv])
    cross_c = np.array([np.argmin(np.abs(c - 0.5)) for c in Cv])
    gap = np.abs(alphas[cross_d] - alphas[cross_c])
    c_at = Cv[np.arange(len(Cv)), cross_d]
    return {
        "probe_test_acc": round(float(probe_acc), 4),
        "conf_head_test_acc": round(float(head_acc), 4),
        "n_paths": int(valid.sum()),
        "frac_paths_adjacent_sign_change": round(sign_change, 4),
        "median_alpha_gap": round(float(np.median(gap)), 4),
        "mean_conf_at_delta_crossing": round(float(c_at.mean()), 4),
    }


def knn_diagnostic(name, hf_id, layer):
    print(f"=== knn {name} ===", flush=True)
    df = load_cities()
    tok, model = load_model(hf_id)
    sub = df[df["is_test"]]
    stmts = list(sub["pos_stmt"]) + list(sub["neg_stmt"])
    labels = np.array(list(sub["pos_label"]) + list(sub["neg_label"]))
    form = np.array(["pos"] * len(sub) + ["neg"] * len(sub))
    H = embed_raw(model, tok, stmts, layer)
    G = kneighbors_graph(H, n_neighbors=10, mode="connectivity")
    n_comp, comp = connected_components(G, directed=False)
    out = {"n_components": int(n_comp), "components": []}
    for k in range(n_comp):
        m = comp == k
        out["components"].append({
            "size": int(m.sum()),
            "frac_true": round(float((labels[m] == 1).mean()), 4),
            "frac_negated_form": round(float((form[m] == "neg").mean()), 4),
        })
    out["components"].sort(key=lambda c: -c["size"])
    return out


def main():
    results = {}
    for name, (hf_id, layer) in MODELS.items():
        entry = {}
        try:
            entry["sp_en"] = spen_replication(name, hf_id, layer)
        except Exception as e:
            entry["sp_en"] = {"error": repr(e)}
            print(f"ERROR sp_en {name}: {e}", flush=True)
        try:
            entry["knn"] = knn_diagnostic(name, hf_id, layer)
        except Exception as e:
            entry["knn"] = {"error": repr(e)}
            print(f"ERROR knn {name}: {e}", flush=True)
        results[name] = entry
        json.dump(results, open("results_gaps.json", "w"), indent=2)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
