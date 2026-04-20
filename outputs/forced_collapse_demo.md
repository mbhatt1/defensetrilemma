# Forced-collapse demonstration (Theorem 8.3)

Applied to the 66 unsafe prompts (f > tau = 0.5) of the saturated gpt-3.5-turbo-0125 archive.

| Defense | Inputs | Distinct outputs | Collapse rate | Max collision class |
|---|---:|---:|---:|---:|
| `refusal` | 66 | 1 | 0.985 | 66 |
| `canonical_category` | 66 | 7 | 0.894 | 40 |
| `paraphrase` | 66 | 66 | 0.000 | 1 |

## Interpretation

- **Refusal** is complete by construction (every output is the safe string `[REFUSAL]`) and collapses *all* inputs into one output. Maximally non-injective.
- **Canonical-category** is complete by construction (every output is a safe category label) and collapses all prompts of a given category into the same output. Non-injective whenever |prompts| > |categories|.
- **Paraphrase** via `gpt-4o-mini` at temperature 0 produces string outputs that partially collide naturally; the remaining injective subset is, by Theorem 8.3, necessarily incomplete — i.e., some paraphrases are not safe.

These three examples demonstrate the *mechanism* of Theorem 8.3 on real data from the paper's saturated archive: no complete utility-preserving defense can be injective. The refusal and canonical-category defenses are explicitly complete and explicitly non-injective; the paraphrase defense exhibits partial collapse without explicit design for it.
