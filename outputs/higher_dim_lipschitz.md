# Higher-dimensional Lipschitz check

Saturated gpt-3.5-turbo-0125 archive, 82 filled cells, tau=0.5.
Comparison of empirical $\hat L$ and $\hat G$ computed in two metrics:

- **2D grid**: normalized grid coordinates in $[0,1]^2$ (the paper's main estimator)
- **768-d embedding**: `sentence-transformers/all-mpnet-base-v2` sentence embeddings, pairwise distances normalized so max = 1 (comparable to the 2D case)

| Metric | L_hat | G_hat |
|---|---:|---:|
| 2D grid (normalized) | 22.680 | 22.680 |
| 768-d MPNet (normalized) | 17.926 | 17.926 |
| ratio hdim/2d | 0.790 | 0.790 |

## Interpretation

If the ratio is close to 1, the 2D MAP-Elites projection is not an artifact of the projection — the Lipschitz estimates are comparable in the higher-dimensional semantic embedding. If the ratio is small (< 0.5) the 2D projection over-estimates the local slope (Lipschitz constants are artifacts of the tight 2D grid). If the ratio is large (> 2), the 2D projection under-estimates the slope, and the theorem still applies with the larger constant.
