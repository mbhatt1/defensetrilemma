"""Adversarial falsification attempt: train the impossible object.

The theorem truth_slack_must_be_positive says no continuous confidence
field can satisfy zero-slack separation and a threshold-inclusive
guarantee over a connected domain with coverage. This experiment gives
that impossibility its best shot. A confidence head is trained
directly against the forbidden objective and we measure how it fails.

Setup per model.
  1. Freeze the truth field delta_F, a one-hidden-layer MLP probe
     trained on split A (as in run_nonlinear.py).
  2. Train an adversarial head c_theta (torch MLP) on all non-test
     statements AND on fresh continuum interpolants sampled every
     epoch, with a loss rewarding exactly the forbidden object:
     c > 1/2 wherever delta_F < 0, c < 1/2 wherever delta_F >= 0,
     with the guarantee side weighted harder since a guarantee
     admits no violations at all.
  3. Evaluate on dense held-out paths (201 alphas, matched test
     pairs). The achieved truth slack eps_hat is the deepest
     truly-true point (largest |delta_F|, delta_F < 0) whose
     confidence nevertheless fails to clear 1/2, taken over all path
     points, after any guarantee violations are counted separately.

Predictions from the theory.
  - eps_hat stays strictly positive across training (the floor).
  - The points realizing near-worst slack localize at the boundary,
    so their |delta_F| is small relative to the endpoint scale.
  - Pushing eps_hat down trades against guarantee violations.

Outputs: results_adversarial.json (floor curves and localization).
"""

import json
import numpy as np
import pandas as pd
import torch
import torch.nn as nn
from transformers import AutoModelForCausalLM, AutoTokenizer
from sklearn.neural_network import MLPClassifier
from sklearn.preprocessing import StandardScaler

DEVICE = "mps" if torch.backends.mps.is_available() else "cpu"
MODELS = {
    "gpt2": ("gpt2", 9),
    "pythia-410m": ("EleutherAI/pythia-410m", 18),
    "qwen2.5-0.5b": ("Qwen/Qwen2.5-0.5B", 12),
    "phi-1.5": ("microsoft/phi-1_5", 18),
}
TAU = 0.5
EPOCHS = 60
EVAL_ALPHAS = 201
GUARANTEE_WEIGHT = 5.0


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
    df["is_test"] = df["city"].isin(test_c)
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


class Head(nn.Module):
    def __init__(self, d):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(d, 256), nn.ReLU(),
            nn.Linear(256, 256), nn.ReLU(),
            nn.Linear(256, 1))

    def forward(self, x):
        return torch.sigmoid(self.net(x)).squeeze(-1)


def run_model(name, hf_id, layer, df):
    print(f"=== adversarial {name} ===", flush=True)
    tok = AutoTokenizer.from_pretrained(hf_id)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    tok.padding_side = "right"
    lm = AutoModelForCausalLM.from_pretrained(
        hf_id, torch_dtype=torch.float32).to(DEVICE).eval()

    stmts = list(df["pos_stmt"]) + list(df["neg_stmt"])
    labels = np.array(list(df["pos_label"]) + list(df["neg_label"]))
    is_test = np.array(list(df["is_test"]) + list(df["is_test"]))
    H = embed(lm, tok, stmts, layer)
    del lm
    d = H.shape[1]

    # Frozen truth field: MLP probe on non-test data.
    sc = StandardScaler().fit(H[~is_test])
    probe = MLPClassifier(hidden_layer_sizes=(64,), max_iter=500,
                          random_state=0, early_stopping=True).fit(
        sc.transform(H[~is_test]), labels[~is_test])

    def delta_F(h):
        p = np.clip(probe.predict_proba(sc.transform(h))[:, 1],
                    1e-9, 1 - 1e-9)
        return -np.log(p / (1 - p))

    # Adversary training pool: non-test statements.
    Htr = torch.tensor(sc.transform(H[~is_test]),
                       dtype=torch.float32, device=DEVICE)
    # Endpoint pairs for continuum sampling during training (non-test).
    tr_pairs = df[~df["is_test"] & (df["pos_label"] == 1)]
    pos_index = {s: i for i, s in enumerate(stmts)}
    tr_h0 = np.stack([H[pos_index[r]] for r in tr_pairs["pos_stmt"]])
    tr_h1 = np.stack([H[pos_index[r]] for r in tr_pairs["neg_stmt"]])

    # Held-out dense evaluation paths (test matched pairs).
    te_pairs = df[df["is_test"] & (df["pos_label"] == 1)]
    alphas = np.linspace(0, 1, EVAL_ALPHAS)
    eval_pts, eval_dF, eval_scale = [], [], []
    for _, row in te_pairs.iterrows():
        h0 = H[pos_index[row["pos_stmt"]]]
        h1 = H[pos_index[row["neg_stmt"]]]
        path = np.stack([(1 - a) * h0 + a * h1 for a in alphas])
        dvals = delta_F(path)
        if not (dvals[0] < 0 and dvals[-1] > 0):
            continue
        eval_pts.append(path)
        eval_dF.append(dvals)
        eval_scale.append(max(abs(dvals[0]), abs(dvals[-1])))
    eval_pts = np.concatenate(eval_pts)
    eval_dF = np.concatenate(eval_dF)
    scale = float(np.median(eval_scale))
    Hev = torch.tensor(sc.transform(eval_pts), dtype=torch.float32,
                       device=DEVICE)
    print(f"eval points {len(eval_dF)} over "
          f"{len(eval_scale)} paths, scale {scale:.2f}", flush=True)

    head = Head(d).to(DEVICE)
    opt = torch.optim.Adam(head.parameters(), lr=1e-3)
    rng = np.random.default_rng(0)
    floor_curve = []

    def eval_slack():
        with torch.no_grad():
            c = head(Hev).cpu().numpy()
        true_mask = eval_dF < 0
        fail_true = true_mask & (c <= TAU)      # separation failures
        guar_viol = (~true_mask) & (c > TAU)    # guarantee violations
        eps_hat = float(np.max(-eval_dF[fail_true])) \
            if fail_true.any() else 0.0
        med_fail_depth = float(np.median(-eval_dF[fail_true])) \
            if fail_true.any() else 0.0
        return {
            "eps_hat_rel": round(eps_hat / scale, 4),
            "median_fail_depth_rel": round(med_fail_depth / scale, 4),
            "frac_guarantee_violations":
                round(float(guar_viol.mean()), 4),
            "frac_true_points_failing":
                round(float(fail_true.mean() / max(true_mask.mean(),
                                                   1e-9)), 4),
        }

    for epoch in range(EPOCHS):
        # fresh continuum interpolants each epoch
        k = len(tr_h0)
        a = rng.uniform(0, 1, size=(k, 1))
        interp = (1 - a) * tr_h0 + a * tr_h1
        batch_np = np.concatenate([H[~is_test], interp])
        dvals = delta_F(batch_np)
        Hb = torch.tensor(sc.transform(batch_np), dtype=torch.float32,
                          device=DEVICE)
        target_true = torch.tensor(dvals < 0, device=DEVICE)
        c = head(Hb)
        loss_sep = torch.relu(TAU + 0.02 - c)[target_true].mean()
        loss_guar = torch.relu(c - (TAU - 0.02))[~target_true].mean()
        loss = loss_sep + GUARANTEE_WEIGHT * loss_guar
        opt.zero_grad()
        loss.backward()
        opt.step()
        if epoch % 5 == 4 or epoch == 0:
            m = eval_slack()
            m["epoch"] = epoch + 1
            floor_curve.append(m)
            print(f"epoch {epoch+1} eps_hat_rel "
                  f"{m['eps_hat_rel']} guar_viol "
                  f"{m['frac_guarantee_violations']}", flush=True)

    final = eval_slack()
    return {
        "probe_acc_nontest_fit": round(
            float(probe.score(sc.transform(H[~is_test]),
                              labels[~is_test])), 4),
        "n_eval_paths": len(eval_scale),
        "n_eval_points": int(len(eval_dF)),
        "floor_curve": floor_curve,
        "final": final,
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
        json.dump(results, open("results_adversarial.json", "w"),
                  indent=2)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
