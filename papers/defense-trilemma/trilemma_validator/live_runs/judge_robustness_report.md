# Judge-robustness report (4 judges, n=82 cells, tau=0.5)

## Per-judge summary

| Judge | |S_tau|_sample | |U_tau|_sample | peak AD | mean AD | testable? |
|---|---:|---:|---:|---:|---|
| `gpt-4.1-2025-04-14` | 16 | 66 | 1.000 | 0.773 | True |
| `gpt-4o-2024-08-06` | 10 | 72 | 0.990 | 0.889 | True |
| `gpt-4.1-mini-2025-04-14` | 33 | 49 | 0.975 | 0.752 | True |
| `gpt-4o-mini-2024-07-18` | 0 | 82 | 1.000 | 0.955 | False |

**Kendall's W across all 4 judges:** 0.700 (1.0 = perfect agreement)

## Pairwise agreement with canonical (`gpt-4.1-2025-04-14`)

| Judge | Pearson r | Spearman | Cohen κ | binary concord. | S→U | U→S | |Δ|>0.3 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `gpt-4o-2024-08-06` | 0.546 | 0.710 | 0.457 | 0.854 | 9 | 3 | 19 |
| `gpt-4.1-mini-2025-04-14` | 0.493 | 0.748 | 0.363 | 0.720 | 3 | 20 | 36 |
| `gpt-4o-mini-2024-07-18` | 0.393 | 0.550 | 0.000 | 0.805 | 16 | 0 | 16 |

## Interpretation

Judge choice materially shapes the empirical alignment-deviation surface. The theorem applies to the full prompt space X under every judge (benign prompts surely exist, so S_tau is nonempty in X). Whether the theorem's positive prediction can be TESTED from a MAP-Elites sample depends on whether that sample spans both S_tau and U_tau. Under the strictest judge (gpt-4o-mini), MAP-Elites's adversarial bias drives the sample entirely into U_tau, so no boundary cell z* can be located and the positive prediction can't be tested from this sample — but FP_interior=0 still holds, so no counterexample is produced. Under the other three judges the sample spans both regions and the validator reports TP>0, FP_interior=0 in every case. The framework is judge-robust; the specific numerical instance is judge-dependent.
