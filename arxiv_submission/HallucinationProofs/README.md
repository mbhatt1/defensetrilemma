# Hallucination Trilemma — Lean 4 Formalization

Machine-verifiable proofs for the **Hallucination Trilemma**: no continuous
language model can simultaneously be **faithful**, **covering**, and
**calibrated** when the truth-set has non-trivial topological boundary.

This is the topological companion to the Defense Trilemma (`ManifoldProofs/`).

## Quick start

```bash
# Requires Lean 4.28.0 + Mathlib v4.28.0 (via elan/lake)
lake build
```

## The result, informally

Let `Q` be a connected metric question space, `A` an answer space,
`M : Q → A × [0,1]` a continuous model with confidence, and `T ⊂ Q × A` a
closed truth-set with non-empty boundary. Then `M` cannot simultaneously
satisfy:

1. **Faithfulness** — high-confidence answers lie in `T`.
2. **Coverage** — the image of `M` is dense in a neighborhood of `∂T`.
3. **Calibration** — `M_confidence` is continuous and equals `1/2` exactly on
   the preimage of `∂T`.

The obstruction is purely topological: connectedness of `Q` plus continuity of
`M_confidence` plus calibration force `M_confidence = 1/2` on a level set, but
faithfulness and coverage place contradictory constraints on `M_answer`
across that level set.

## Structure (11 files)

| File | Content |
|------|---------|
| `HoF_01_Foundations` | Question/answer spaces, model map, truth set, truth-distance |
| `HoF_02_TruthSet` | Topology of `T`: closed, boundary, two-component complement |
| `HoF_03_BoundaryCrossing` | IVT-style boundary crossings of model image |
| `HoF_04_Faithfulness` | Faithfulness condition and its consequences |
| `HoF_05_Coverage` | Coverage condition: density / surjectivity on a band |
| `HoF_06_Calibration` | Calibration: confidence equals `1/2` on preimage of `∂T` |
| `HoF_07_TrilemmaCore` | Core trilemma theorem |
| `HoF_08_BorsukUlam` | Antipodal-style obstruction (negation reframing) |
| `HoF_09_Discrete` | Discrete impossibility — no topology needed |
| `HoF_MasterTheorem` | Bundled `HallucinationStructure` and master theorem |
| `HoF_FinalVerification` | `#print axioms` for the headline theorems |

## Key theorems

| Theorem | File | Says |
|---------|------|------|
| `truthSet_boundary_nonempty` | `HoF_02` | Non-trivial `T` has non-empty boundary |
| `image_crosses_boundary` | `HoF_03` | Coverage forces image of `M` to cross `∂T` |
| `faithfulness_forces_truth` | `HoF_04` | High-confidence ⇒ `M_answer ∈ T` |
| `confidence_half_on_boundary` | `HoF_06` | Calibration forces `M_conf = 1/2` on `M⁻¹(∂T)` |
| `hallucination_trilemma` | `HoF_07` | Faith + Coverage + Calibration ⇒ ⊥ |
| `discrete_hallucination` | `HoF_09` | Capacity argument without topology |
| `hallucination_master_theorem` | `HoF_MasterTheorem` | Bundled top-level statement |

## Verification

- **Lean 4.28.0** + **Mathlib v4.28.0**
- Files import only `Mathlib` (no cross-file dependencies); the entry-point
  `HallucinationProofs.lean` imports them all.
- Following the `ManifoldProofs/` pattern.
