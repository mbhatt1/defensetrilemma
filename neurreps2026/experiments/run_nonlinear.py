"""Nonlinear-probe replication of the boundary-coupling experiment.

With a linear truth probe, the sign change along a linear
interpolation path is analytically guaranteed once the endpoints are
classified correctly. Here both fields are small MLPs, so nothing
about the path behavior is guaranteed by construction. The crossing,
its uniqueness or multiplicity, and the coupling of the two
independently trained fields are all genuine empirical questions,
and the truth boundary is no longer a hyperplane.

Same models, layers, data, and splits as run_experiment.py. The truth
probe delta_F is a one-hidden-layer MLP trained on split A, the
confidence head an independent MLP trained on split B with a
different seed. Fields are evaluated along the same interpolation
paths and the same statistics are reported, plus the number of zero
crossings per path.

Output: results_nonlinear.json, curves_mlp_<model>.npz.
"""

import json
import numpy as np
import pandas as pd
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from sklearn.neural_network import MLPClassifier
from sklearn.preprocessing import StandardScaler

DEVICE = "mps" if torch.backends.mps.is_available() else "cpu"
MODELS = {
    "gpt2": ("gpt2", 9),
    "pythia-410m": ("EleutherAI/pythia-410m", 18),
    "qwen2.5-0.5b": ("Qwen/Qwen2.5-0.5B", 12),
}
N_PATHS = 150
N_ALPHA = 41


def load_data():
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
    val_c = set(ucities[n // 5: n // 5 + n // 10])
    splitB_c = set(ucities[n // 5 + n // 10: n // 2])
    df["split"] = "A"
    df.loc[df["city"].isin(splitB_c), "split"] = "B"
    df.loc[df["city"].isin(val_c), "split"] = "val"
    df.loc[df["city"].isin(test_c), "split"] = "test"
    return df


@torch.no_grad()
def embed(model, tok, texts, layer, batch=32):
    out = []
    for i in range(0, len(texts), batch):
        enc = tok(texts[i:i + batch], return_tensors="pt",
                  padding=True).to(DEVICE)
        o = model(**enc, output_hidden_states=True)
        idx = enc["attention_mask"].sum(1) - 1
        rows = torch.arange(len(enc["input_ids"]), device=DEVICE)
        out.append(o.hidden_states[layer][rows, idx].float().cpu())
    return torch.cat(out).numpy()


def signed_field(clf, scaler, h):
    """Signed truth field from MLP probability, negative on true."""
    p = clf.predict_proba(scaler.transform(h))[:, 1]
    p = np.clip(p, 1e-9, 1 - 1e-9)
    return -np.log(p / (1 - p))


def run_model(name, hf_id, layer, df):
    print(f"=== nonlinear {name} ===", flush=True)
    tok = AutoTokenizer.from_pretrained(hf_id)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    tok.padding_side = "right"
    model = AutoModelForCausalLM.from_pretrained(
        hf_id, torch_dtype=torch.float32).to(DEVICE).eval()

    stmts = list(df["pos_stmt"]) + list(df["neg_stmt"])
    labels = np.array(list(df["pos_label"]) + list(df["neg_label"]))
    split = np.array(list(df["split"]) + list(df["split"]))
    H = embed(model, tok, stmts, layer)

    scA = StandardScaler().fit(H[split == "A"])
    probe = MLPClassifier(hidden_layer_sizes=(64,), max_iter=500,
                          random_state=0,
                          early_stopping=True).fit(
        scA.transform(H[split == "A"]), labels[split == "A"])
    scB = StandardScaler().fit(H[split == "B"])
    head = MLPClassifier(hidden_layer_sizes=(64,), max_iter=500,
                         random_state=1,
                         early_stopping=True).fit(
        scB.transform(H[split == "B"]), labels[split == "B"])

    te = split == "test"
    probe_acc = probe.score(scA.transform(H[te]), labels[te])
    head_acc = head.score(scB.transform(H[te]), labels[te])
    print(f"mlp probe acc {probe_acc:.3f} head acc {head_acc:.3f}",
          flush=True)

    def delta_F(h):
        return signed_field(probe, scA, h)

    def conf(h):
        return head.predict_proba(scB.transform(h))[:, 1]

    pairs = df[(df["split"] == "test") & (df["pos_label"] == 1)].head(N_PATHS)
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
    n_crossings = np.array(
        [(np.diff(np.sign(d)) != 0).sum() for d in Dv])
    cross_d = np.array([np.argmin(np.abs(d)) for d in Dv])
    cross_c = np.array([np.argmin(np.abs(c - 0.5)) for c in Cv])
    gap = np.abs(alphas[cross_d] - alphas[cross_c])
    c_at = Cv[np.arange(len(Cv)), cross_d]

    np.savez(f"curves_mlp_{name}.npz", D=Dv, C=Cv, alphas=alphas)
    return {
        "mlp_probe_test_acc": round(float(probe_acc), 4),
        "mlp_head_test_acc": round(float(head_acc), 4),
        "n_paths": int(valid.sum()),
        "frac_paths_with_sign_change": round(sign_change, 4),
        "median_n_crossings": float(np.median(n_crossings)),
        "frac_single_crossing": round(
            float((n_crossings == 1).mean()), 4),
        "median_alpha_gap": round(float(np.median(gap)), 4),
        "mean_conf_at_delta_crossing": round(float(c_at.mean()), 4),
    }


def main():
    df = load_data()
    results = {}
    for name, (hf_id, layer) in MODELS.items():
        try:
            results[name] = run_model(name, hf_id, layer, df)
        except Exception as e:
            results[name] = {"error": repr(e)}
            print(f"ERROR {name}: {e}", flush=True)
        json.dump(results, open("results_nonlinear.json", "w"), indent=2)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
