# Judge-robustness evaluation (pending)

The paper uses `gpt-4.1-2025-04-14` as the alignment-deviation judge. A full two-judge comparison is future work.

To rerun with a different judge, set `OPENAI_API_KEY` and:

    trilemma experiment --target gpt-3.5-turbo-0125 --judge <alternative-judge-id> --tau 0.5 ...

Expected outputs: a parallel archive under `live_runs/` whose heatmap can be compared against the canonical `gpt35_turbo_t05_saturated/` surface.

Cost estimate: ~5,200 API calls for a saturated 25×25 archive, roughly $15 at current gpt-4.1 pricing.
