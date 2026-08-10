"""Endogenous-confidence experiment and null baselines.

Addresses the strongest objection to the trained-head experiment in
run_experiment.py: two heads trained on the same truth target having
nearby boundaries is unsurprising. Here the confidence field is the
model's OWN verbalized uncertainty, not a trained head.

Part A (endogenous confidence via activation patching).
  1. Embed each statement under the question template at layer L,
     final token. Train the truth probe delta_F on split A of these
     template-context representations.
  2. For each held-out matched pair, interpolate the layer-L final
     token state from the true statement to its negation. Patch the
     interpolated state into the true statement's template context at
     layer L and continue the forward pass. The endogenous confidence
     c(alpha) is the model's own p(" true") over {" true", " false"}
     at the answer position.
  3. Record both fields along each path and the crossing-gap
     statistic, exactly as in the main experiment.

Part B (null baselines for the trained-head experiment).
  On the raw-statement representations of run_experiment.py, replace
  the confidence head with (a) heads trained on permuted labels and
  (b) random-direction heads, 20 seeds each. The null distribution of
  the crossing gap calibrates the observed gaps.

Outputs: results_endogenous.json, curves_endog_<model>.npz.
"""

import json
import numpy as np
import pandas as pd
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler

DEVICE = "mps" if torch.backends.mps.is_available() else "cpu"
MODELS = {
    "gpt2": ("gpt2", 9),
    "pythia-410m": ("EleutherAI/pythia-410m", 18),
    "qwen2.5-0.5b": ("Qwen/Qwen2.5-0.5B", 12),
    "phi-1.5": ("microsoft/phi-1_5", 18),
}
N_PATHS = 150
N_ALPHA = 41
N_NULL_SEEDS = 20
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
    splitB_c = set(ucities[n // 5 + n // 10: n // 2])
    df["split"] = "A"
    df.loc[df["city"].isin(splitB_c), "split"] = "B"
    df.loc[df["city"].isin(val_c), "split"] = "val"
    df.loc[df["city"].isin(test_c), "split"] = "test"
    return df


def get_blocks(model):
    for attr in ("transformer", "gpt_neox", "model"):
        mod = getattr(model, attr, None)
        if mod is not None:
            for battr in ("h", "layers"):
                blocks = getattr(mod, battr, None)
                if blocks is not None:
                    return blocks
    raise ValueError("unknown architecture")


@torch.no_grad()
def capture_template_states(model, tok, texts, batch=16):
    """Final-token output of the LAST block under the template, captured
    through the same hook point later used for patching, so the two are
    consistent by construction."""
    blocks = get_blocks(model)
    grabbed = {}

    def hook(_module, _inp, output):
        grabbed["h"] = output[0] if isinstance(output, tuple) else output
        return output

    out = []
    handle = blocks[-1].register_forward_hook(hook)
    try:
        for i in range(0, len(texts), batch):
            chunk = [TEMPLATE.format(s=s) for s in texts[i:i + batch]]
            enc = tok(chunk, return_tensors="pt", padding=True).to(DEVICE)
            model(**enc)
            idx = enc["attention_mask"].sum(1) - 1
            rows = torch.arange(len(chunk), device=DEVICE)
            out.append(grabbed["h"][rows, idx].float().cpu())
    finally:
        handle.remove()
    return torch.cat(out).numpy()


@torch.no_grad()
def patched_confidence(model, tok, context_text, states,
                       true_id, false_id):
    """Run the template context with the LAST block's final-token state
    replaced by each row of `states`; the answer logits are then a
    deterministic function of the patched state (only the final norm and
    unembedding follow). Return the model's own p(true) per row."""
    blocks = get_blocks(model)
    enc = tok(TEMPLATE.format(s=context_text),
              return_tensors="pt").to(DEVICE)
    n = states.shape[0]
    ids = enc["input_ids"].repeat(n, 1)
    mask = enc["attention_mask"].repeat(n, 1)
    pos = ids.shape[1] - 1
    patch = torch.tensor(states, dtype=torch.float32, device=DEVICE)

    def hook(_module, _inp, output):
        if isinstance(output, tuple):
            output[0][:, pos, :] = patch
            return output
        output[:, pos, :] = patch
        return output

    handle = blocks[-1].register_forward_hook(hook)
    try:
        out = model(input_ids=ids, attention_mask=mask)
    finally:
        handle.remove()
    logits = out.logits[:, -1, :]
    pair = torch.stack([logits[:, true_id], logits[:, false_id]], dim=1)
    return torch.softmax(pair, dim=1)[:, 0].float().cpu().numpy()


def crossing_stats(D, C, alphas, thresh=0.5):
    cross_d = np.array([np.argmin(np.abs(d)) for d in D])
    cross_c = np.array([np.argmin(np.abs(c - thresh)) for c in C])
    gap = np.abs(alphas[cross_d] - alphas[cross_c])
    c_at = C[np.arange(len(C)), cross_d]
    return gap, c_at


def run_endogenous(name, hf_id, layer, df):
    print(f"=== endogenous {name} ===", flush=True)
    tok = AutoTokenizer.from_pretrained(hf_id)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    tok.padding_side = "right"
    model = AutoModelForCausalLM.from_pretrained(
        hf_id, torch_dtype=torch.float32).to(DEVICE).eval()
    true_id = tok.encode(" true")[-1]
    false_id = tok.encode(" false")[-1]

    stmts = list(df["pos_stmt"]) + list(df["neg_stmt"])
    labels = np.array(list(df["pos_label"]) + list(df["neg_label"]))
    split = np.array(list(df["split"]) + list(df["split"]))
    H = capture_template_states(model, tok, stmts)

    scA = StandardScaler().fit(H[split == "A"])
    probe = LogisticRegression(max_iter=2000, random_state=0).fit(
        scA.transform(H[split == "A"]), labels[split == "A"])
    probe_acc = probe.score(scA.transform(H[split == "test"]),
                            labels[split == "test"])
    print(f"template probe acc {probe_acc:.3f}", flush=True)

    def delta_F(h):
        return -(scA.transform(h) @ probe.coef_[0] + probe.intercept_[0])

    pairs = df[(df["split"] == "test") & (df["pos_label"] == 1)].head(N_PATHS)
    pos_index = {s: i for i, s in enumerate(stmts)}
    alphas = np.linspace(0, 1, N_ALPHA)
    D, C = [], []
    for _, row in pairs.iterrows():
        h0 = H[pos_index[row["pos_stmt"]]]
        h1 = H[pos_index[row["neg_stmt"]]]
        path = np.stack([(1 - a) * h0 + a * h1 for a in alphas])
        d = delta_F(path)
        c = patched_confidence(model, tok, row["pos_stmt"], path,
                               true_id, false_id)
        D.append(d)
        C.append(c)
    D, C = np.stack(D), np.stack(C)

    valid = (D[:, 0] < 0) & (D[:, -1] > 0)
    Dv, Cv = D[valid], C[valid]
    # keep paths where the endogenous signal is decisive at both ends
    decisive = (Cv[:, 0] > 0.5) & (Cv[:, -1] < 0.5)
    gap_all, c_at_all = crossing_stats(Dv, Cv, alphas)
    Dd, Cd = Dv[decisive], Cv[decisive]
    if decisive.any():
        gap_dec, c_at_dec = crossing_stats(Dd, Cd, alphas)
    else:
        gap_dec, c_at_dec = np.array([]), np.array([])

    np.savez(f"curves_endog_{name}.npz", D=Dv, C=Cv, alphas=alphas,
             decisive=decisive)
    return {
        "model": hf_id, "layer": layer,
        "template_probe_test_acc": round(float(probe_acc), 4),
        "n_paths": int(valid.sum()),
        "n_decisive_paths": int(decisive.sum()),
        "frac_decisive": round(float(decisive.mean()), 4)
            if len(decisive) else None,
        "median_gap_all_paths": round(float(np.median(gap_all)), 4)
            if len(gap_all) else None,
        "median_gap_decisive_paths": round(float(np.median(gap_dec)), 4)
            if len(gap_dec) else None,
        "mean_conf_at_crossing_decisive":
            round(float(c_at_dec.mean()), 4) if len(c_at_dec) else None,
    }


def run_nulls(name, hf_id, df):
    """Null baselines on the raw-statement setup of run_experiment.py."""
    print(f"=== nulls {name} ===", flush=True)
    tok = AutoTokenizer.from_pretrained(hf_id)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    tok.padding_side = "right"
    model = AutoModelForCausalLM.from_pretrained(
        hf_id, torch_dtype=torch.float32).to(DEVICE).eval()
    n_layers = model.config.num_hidden_layers

    stmts = list(df["pos_stmt"]) + list(df["neg_stmt"])
    labels = np.array(list(df["pos_label"]) + list(df["neg_label"]))
    split = np.array(list(df["split"]) + list(df["split"]))

    # raw-statement embeddings at the layer chosen by the main run
    layer = MODELS[name][1]

    @torch.no_grad()
    def embed_raw(texts, batch=32):
        out = []
        for i in range(0, len(texts), batch):
            enc = tok(texts[i:i + batch], return_tensors="pt",
                      padding=True).to(DEVICE)
            o = model(**enc, output_hidden_states=True)
            idx = enc["attention_mask"].sum(1) - 1
            rows = torch.arange(len(enc["input_ids"]), device=DEVICE)
            out.append(o.hidden_states[layer][rows, idx].float().cpu())
        return torch.cat(out).numpy()

    H = embed_raw(stmts)
    scA = StandardScaler().fit(H[split == "A"])
    probe = LogisticRegression(max_iter=2000, random_state=0).fit(
        scA.transform(H[split == "A"]), labels[split == "A"])

    def delta_F(h):
        return -(scA.transform(h) @ probe.coef_[0] + probe.intercept_[0])

    pairs = df[(df["split"] == "test") & (df["pos_label"] == 1)].head(N_PATHS)
    pos_index = {s: i for i, s in enumerate(stmts)}
    alphas = np.linspace(0, 1, N_ALPHA)
    paths = []
    for _, row in pairs.iterrows():
        h0 = H[pos_index[row["pos_stmt"]]]
        h1 = H[pos_index[row["neg_stmt"]]]
        paths.append(np.stack([(1 - a) * h0 + a * h1 for a in alphas]))
    D = np.stack([delta_F(p) for p in paths])
    valid = (D[:, 0] < 0) & (D[:, -1] > 0)
    Dv = D[valid]
    paths_v = [p for p, v in zip(paths, valid) if v]

    scB = StandardScaler().fit(H[split == "B"])
    HB = scB.transform(H[split == "B"])
    labB = labels[split == "B"]
    d_model = H.shape[1]

    def gap_for_head(w, b):
        gaps = []
        for p, dvec in zip(paths_v, Dv):
            c = 1.0 / (1.0 + np.exp(-(scB.transform(p) @ w + b)))
            g, _ = crossing_stats(dvec[None, :], c[None, :], alphas)
            gaps.append(g[0])
        return float(np.median(gaps))

    perm_gaps, rand_gaps = [], []
    for seed in range(N_NULL_SEEDS):
        rng = np.random.default_rng(seed)
        # (a) head trained on permuted labels
        perm = rng.permutation(labB)
        head = LogisticRegression(max_iter=2000, random_state=seed).fit(
            HB, perm)
        perm_gaps.append(gap_for_head(head.coef_[0], head.intercept_[0]))
        # (b) random-direction head, threshold at the split-B median score
        w = rng.standard_normal(d_model)
        w /= np.linalg.norm(w)
        b = -float(np.median(HB @ w))
        rand_gaps.append(gap_for_head(w, b))

    return {
        "n_paths": int(valid.sum()),
        "null_permuted_median_gap": round(float(np.median(perm_gaps)), 4),
        "null_permuted_gap_range":
            [round(float(np.min(perm_gaps)), 4),
             round(float(np.max(perm_gaps)), 4)],
        "null_random_median_gap": round(float(np.median(rand_gaps)), 4),
        "null_random_gap_range":
            [round(float(np.min(rand_gaps)), 4),
             round(float(np.max(rand_gaps)), 4)],
        "n_null_seeds": N_NULL_SEEDS,
    }


def main():
    df = load_data()
    results = {}
    for name, (hf_id, layer) in MODELS.items():
        entry = {}
        try:
            entry["endogenous"] = run_endogenous(name, hf_id, layer, df)
        except Exception as e:
            entry["endogenous"] = {"error": repr(e)}
            print(f"ERROR endogenous {name}: {e}", flush=True)
        try:
            entry["nulls"] = run_nulls(name, hf_id, df)
        except Exception as e:
            entry["nulls"] = {"error": repr(e)}
            print(f"ERROR nulls {name}: {e}", flush=True)
        results[name] = entry
        json.dump(results, open("results_endogenous.json", "w"), indent=2)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
