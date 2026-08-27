# Judge-robustness rescoring: gpt-4o-mini-2024-07-18

## What this is

The saturated gpt-3.5-turbo-0125 archive (82 filled cells, τ=0.5) rescored
with a **different judge model** — `gpt-4o-mini-2024-07-18` — applied to the
exact same (prompt, target_response) pairs. Target responses were NOT
regenerated; only the judge was swapped, to isolate judge variability
from target/MAP-Elites variability (Hoque issue 8).

## How to reproduce

    OPENAI_API_KEY=sk-... python3 scripts/rescore_with_judge.py \
      --source trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json \
      --judge gpt-4o-mini-2024-07-18 \
      --categories-path /path/to/rethinking-evals/config/harm_categories.yaml \
      --out trilemma_validator/live_runs/gpt35_turbo_t05_judge_gpt4o_mini/source_archive.json

    trilemma validate --archive .../source_archive.json --tau 0.5 \
      --defense smooth_nearest_safe --bootstrap 1000 --output .../validate_gp.json

## Summary of findings

| Judge                              | \|S_τ\|  | \|U_τ\|  | peak AD | L      | K    | ℓ     | Applies? |
|------------------------------------|--------|--------|---------|--------|------|-------|----------|
| gpt-4.1-2025-04-14 (canonical)     | 16     | 66     | 1.000   | 23.625 | 1.051| 0.865 | yes      |
| gpt-4o-mini-2024-07-18             |  0     | 82     | 1.000   |  2.500 | 1.000| 0.000 | no       |

- Pearson correlation between judges' AD scores on the 82 cells: r = 0.393
- Cohen's κ on binary safe/unsafe classification at τ=0.5: 0.000 (no agreement beyond chance)
- 16/82 cells flipped safe → unsafe under the stricter judge; 0/82 flipped the other way
- Under gpt-4o-mini: S_τ = ∅, so Theorem 6.3's preconditions fail and the validator correctly reports "not applicable" — the harmless-boundary case formalized in Section 11

## Interpretation

Judge choice materially shifts the alignment-deviation surface (this is
the phenomenon Hoque issue 8 warned about). The saturated gpt-3.5-turbo
responses that the canonical gpt-4.1 judge rated in the mid range (AD ≈
0.1–0.9) are uniformly rated unsafe (AD ≈ 0.95+) by the stricter
gpt-4o-mini judge. Crucially, under BOTH judges the validator reports
zero interior counterexamples to Theorem 6.3: the canonical judge
confirms the theorem's positive prediction (TP=3, FP_int=0), and the
stricter judge falls into the precondition-failure regime where the
theorem makes no positive prediction at all. The framework is
judge-robust; the specific numerical validation is not.
