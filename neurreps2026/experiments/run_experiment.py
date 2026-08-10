"""Boundary-coupling experiment on sub-1B language models.

The theory models two continuous fields on representation space. A
truth field delta_F (negative on true answers, positive on false) and
a confidence field c that separates truth from falsehood at a
threshold. The canonical instances in the probing literature are
linear readouts of hidden states. We instantiate both fields as
independently trained linear heads and test the theory's predictions.

For each model:
  1. Embed raw true/false statements (cities + neg_cities) at several
     layers, final token. Pick the best layer by validation accuracy.
  2. Train the truth probe delta_F on train split A.
  3. Train an independent confidence head c on disjoint split B
     (different data, different seed). tau = 1/2.
  4. Interpolate hidden states between matched (statement, negation)
     pairs. Record delta_F(alpha) and c(alpha).
     Predictions. Every path has an adjacent sign change of delta_F
     (discrete sign change). The threshold crossing of c and the zero
     of delta_F occur at nearly the same alpha (boundary coupling).
     c is near 1/2 where delta_F is near 0 (confidence pinning).
  5. Estimate the boundary width. The range of |delta_F| over which
     c stays inside [0.4, 0.6].
  6. kNN connectivity check of the activation set (premise T).

Also recorded: the model's own verbalized true/false accuracy under a
question template, documenting that sub-1B base models cannot do the
verbalized task even though their representations separate truth.

Outputs: results.json and curves_<model>.npz.
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
    "gpt2": "gpt2",                           # 124M
    "pythia-410m": "EleutherAI/pythia-410m",  # 410M
    "qwen2.5-0.5b": "Qwen/Qwen2.5-0.5B",      # 494M
    "phi-1.5": "microsoft/phi-1_5",           # 1.3B
}
N_PATHS = 150
N_ALPHA = 41
TEMPLATE = 'Q: Is this statement true or false? "{s}" A: The statement is'


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
    splitB_c = set(ucities[n // 5 + n // 10: n // 2])   # confidence head
    df["split"] = "A"
    df.loc[df["city"].isin(splitB_c), "split"] = "B"
    df.loc[df["city"].isin(val_c), "split"] = "val"
    df.loc[df["city"].isin(test_c), "split"] = "test"
    return df


@torch.no_grad()
def embed(model, tok, texts, layer_ids, batch=32):
    out_h = {L: [] for L in layer_ids}
    for i in range(0, len(texts), batch):
        enc = tok(texts[i:i + batch], return_tensors="pt",
                  padding=True).to(DEVICE)
        out = model(**enc, output_hidden_states=True)
        idx = enc["attention_mask"].sum(1) - 1
        rows = torch.arange(len(enc["input_ids"]), device=DEVICE)
        for L in layer_ids:
            out_h[L].append(out.hidden_states[L][rows, idx].float().cpu())
    return {L: torch.cat(v).numpy() for L, v in out_h.items()}


@torch.no_grad()
def verbalized_accuracy(model, tok, statements, labels, true_id, false_id,
                        batch=16):
    correct, total = 0, 0
    for i in range(0, len(statements), batch):
        chunk = [TEMPLATE.format(s=s) for s in statements[i:i + batch]]
        enc = tok(chunk, return_tensors="pt", padding=True).to(DEVICE)
        out = model(**enc)
        idx = enc["attention_mask"].sum(1) - 1
        rows = torch.arange(len(chunk), device=DEVICE)
        logits = out.logits[rows, idx]
        pred = (logits[:, true_id] > logits[:, false_id]).long().cpu().numpy()
        correct += (pred == labels[i:i + batch]).sum()
        total += len(chunk)
    return correct / total


def run_model(name, hf_id, df):
    print(f"=== {name} ===", flush=True)
    tok = AutoTokenizer.from_pretrained(hf_id)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    tok.padding_side = "right"
    model = AutoModelForCausalLM.from_pretrained(
        hf_id, torch_dtype=torch.float32).to(DEVICE).eval()
    n_layers = model.config.num_hidden_layers
    layer_ids = sorted({n_layers // 4, n_layers // 2, (3 * n_layers) // 4})
    true_id = tok.encode(" true")[-1]
    false_id = tok.encode(" false")[-1]

    stmts = list(df["pos_stmt"]) + list(df["neg_stmt"])
    labels = np.array(list(df["pos_label"]) + list(df["neg_label"]))
    split = np.array(list(df["split"]) + list(df["split"]))
    H_by_layer = embed(model, tok, stmts, layer_ids)

    # Pick layer by validation accuracy of a quick probe on split A.
    best_L, best_acc = None, -1.0
    for L, H in H_by_layer.items():
        sc = StandardScaler().fit(H[split == "A"])
        p = LogisticRegression(max_iter=2000).fit(
            sc.transform(H[split == "A"]), labels[split == "A"])
        acc = p.score(sc.transform(H[split == "val"]), labels[split == "val"])
        if acc > best_acc:
            best_L, best_acc = L, acc
    H = H_by_layer[best_L]
    print(f"layer {best_L}/{n_layers} val acc {best_acc:.3f}", flush=True)

    # Truth probe (split A) and independent confidence head (split B).
    scA = StandardScaler().fit(H[split == "A"])
    probe = LogisticRegression(max_iter=2000, random_state=0).fit(
        scA.transform(H[split == "A"]), labels[split == "A"])
    scB = StandardScaler().fit(H[split == "B"])
    head = LogisticRegression(max_iter=2000, random_state=1).fit(
        scB.transform(H[split == "B"]), labels[split == "B"])

    te = split == "test"
    probe_acc = probe.score(scA.transform(H[te]), labels[te])
    head_acc = head.score(scB.transform(H[te]), labels[te])

    def delta_F(h):     # negative on true
        return -(scA.transform(h) @ probe.coef_[0] + probe.intercept_[0])

    def conf(h):        # P(true | h), independent head
        return head.predict_proba(scB.transform(h))[:, 1]

    # Verbalized baseline on the test split.
    te_idx = np.where(te)[0]
    verb_acc = verbalized_accuracy(
        model, tok, [stmts[i] for i in te_idx], labels[te_idx],
        true_id, false_id)

    # Interpolation paths between matched pairs (test split, pos true).
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
    sign_change = np.mean([(np.diff(np.sign(d)) != 0).any() for d in Dv])
    cross_d = np.array([np.argmin(np.abs(d)) for d in Dv])
    cross_c = np.array([np.argmin(np.abs(cc - 0.5)) for cc in Cv])
    alpha_gap = np.abs(alphas[cross_d] - alphas[cross_c])
    c_at_cross = Cv[np.arange(len(Cv)), cross_d]
    ends = np.concatenate([Cv[:, 0], Cv[:, -1]])
    flat_d, flat_c = Dv.ravel(), Cv.ravel()
    band = (flat_c > 0.4) & (flat_c < 0.6)
    width = float(np.median(np.abs(flat_d[band]))) if band.any() else None
    d_scale = float(np.median(np.abs(np.concatenate([Dv[:, 0], Dv[:, -1]]))))

    Ht = H[te]
    G = kneighbors_graph(Ht, n_neighbors=10, mode="connectivity")
    n_comp, comp = connected_components(G, directed=False)
    main = np.bincount(comp).argmax()
    lab_te = labels[te]
    both = (lab_te[comp == main] == 0).any() and \
           (lab_te[comp == main] == 1).any()

    np.savez(f"curves_{name}.npz", D=Dv, C=Cv, alphas=alphas)
    return {
        "model": hf_id, "layer": int(best_L), "n_layers": int(n_layers),
        "probe_test_acc": round(float(probe_acc), 4),
        "conf_head_test_acc": round(float(head_acc), 4),
        "verbalized_test_acc": round(float(verb_acc), 4),
        "n_paths": int(valid.sum()),
        "frac_paths_adjacent_sign_change": round(float(sign_change), 4),
        "mean_alpha_gap_delta_vs_conf_crossing":
            round(float(alpha_gap.mean()), 4),
        "median_alpha_gap": round(float(np.median(alpha_gap)), 4),
        "mean_conf_at_delta_crossing": round(float(c_at_cross.mean()), 4),
        "mean_abs_conf_margin_at_crossing":
            round(float(np.abs(c_at_cross - 0.5).mean()), 4),
        "mean_abs_conf_margin_at_ends":
            round(float(np.abs(ends - 0.5).mean()), 4),
        "boundary_width_delta_units":
            None if width is None else round(width, 4),
        "endpoint_delta_scale": round(d_scale, 4),
        "boundary_width_relative":
            None if width is None else round(width / d_scale, 4),
        "knn_components": int(n_comp),
        "frac_in_main_component": round(float((comp == main).mean()), 4),
        "true_and_false_share_main_component": bool(both),
    }


def main():
    df = load_data()
    results = {}
    for name, hf_id in MODELS.items():
        try:
            results[name] = run_model(name, hf_id, df)
        except Exception as e:
            results[name] = {"error": repr(e)}
            print(f"ERROR {name}: {e}", flush=True)
        json.dump(results, open("results.json", "w"), indent=2)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
