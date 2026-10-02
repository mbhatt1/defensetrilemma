# Adversarial review: how each finding was handled

An independent reviewer pass ran four personas (Novelty, Experimental validity, Theory, Clarity) plus a red team. Verdict on draft 1: **major revision, leaning reject**. Every finding below was re-verified before it was acted on.

| # | Sev. | Finding | Verified? | Disposition |
|---|---|---|---|---|
| 1 | BLOCKING | A midpoint baseline with no truth information matches or beats every readout's crossing gap. | Yes. Reproduced; see `experiments/compute_controls.py` → `results_controls.json`. | **Story changed.** The midpoint baseline is now reported everywhere. On separating paths the gap ties or loses to it. The abstract, intro and conclusion now state that the data do not show the coupled query, and the experiments are framed as premise measurement. |
| 2 | MAJOR | For linear readouts the gap is an endpoint statistic, and the separation–gap link is partly mechanical. | Yes. Gaps on separating vs non-separating paths, and closed-form continuous crossings, all reproduced. | Stated in §9 preamble. Table 2 adds Gap\|sep and Mid\|sep. The mechanical component is disclosed. |
| 3 | MAJOR | The MLP "ordering preserved" claim is false. | Yes. | Rewritten: the Qwens are smallest; the ordering among the three weaker models is not preserved. |
| 4 | MAJOR | The endogenous sentence misstates Phi-1.5 (66% separating, gap 0.40 vs 0.20 baseline). | Yes. | Phi is reported explicitly as a case where endpoint separation holds but the crossings disagree; the abstract is fixed. |
| 5 | MAJOR | Truth is confounded with polarity on every path. | Yes. Every path is affirmative-true → negated-false. | Disclosed in §9.4 and the limitations; decoupled-path and polarity-head controls marked **[EVIDENCE NEEDED]**. These cannot be run here: Hugging Face is blocked and there is no torch. |
| 6 | MAJOR | Novelty is thin; the Defense Trilemma already has discrete, ε-relaxed, Lipschitz, boundary and multi-turn variants. | Yes. Analogues found in `ManifoldProofs/MoF_12, MoF_16, MoF_Adv_02`. | Remark 1 added (topology only gives nonemptiness). Related work and Contribution 2 credit the transfer. New elements are stated narrowly. |
| 7 | MAJOR | Unresolved [EVIDENCE NEEDED] markers. | Yes. | Kept visible on purpose; they are real gaps. See the list of open items below. |
| 8 | MAJOR | The supplement README names a workshop venue and an older title from an earlier draft; anonymity risk. | Yes. README lines 1–5. | Fixed: venue and title removed from the supplement. The earlier draft was never submitted, so there is no prior-submission issue. |
| 9 | MINOR | "Shrinks as" trend language. | Yes. | Removed. Wording is now "smaller in models with…" and "rank ordering". |
| 10 | MINOR | Contribution 3 overstated the controls. | Yes. | Rewritten. |
| 11 | MINOR | Lean statements carry extra hypotheses (antipodal: continuous c; trilemma and multi-turn: continuous a, δ). | Yes. | Added to the theorem text and Table 1. |
| 12 | MINOR | The local Thm 9(ii) was used for a global single-crossing claim. | Yes. | Clause removed. |
| 13 | MINOR | The wrong result was cited for the guaranteed sign change. | Yes. | Now attributed to affinity. |
| 14 | MINOR | The dichotomy hypothesis is automatic at a coupled query. | Proof checked. | Added as a paper-only sentence; Table 1 row added. |
| 15 | MINOR | Broader-impact claim was unevaluated. | Yes. | Softened. |
| 16 | MINOR | "True answer" and "single query" were imprecise. | Yes. | Now "strictly true" and "at least one query". |
| 17 | MINOR | The title asserted connectedness. | Yes. | Retitled "…Under Connectedness". |
| 18 | MINOR | The Karbasi et al. verb overstated their result. | Plausible (snippet-level). | Rewritten in hedged form; still [CITATION CHECK NEEDED] in the bib. |
| 19 | MINOR | Coarse bootstrap and differing path sets. | Yes. | Continuous crossings reported (agree within 0.01); the single-seed limitation is stated. Common path sets were not done. |
| 20 | MINOR | The adversarial run is not torch-seeded. | Yes. | Stated in the appendix. |
| 21 | MINOR | Example 1's confidence was unbounded. | Yes. | Changed to the sigmoid 1/(1+e^x). |
| 22–25 | COSM. | Rounding, 0.995, figure caption, layer indexing. | Yes. | All fixed. |

## Remaining open items (author action required)

1. **Supplement README (#8).** Done: venue name and old title removed, and the "every theorem … is formalized" claim fixed. The earlier draft was never submitted, so nothing needs disclosing.
2. **Lean build log.** Run `lake build` and record the `#print axioms` output for every Table 1 identifier. Several of them, e.g. `model_truth_boundary_nonempty` and `discrete_sign_change`, currently have no `#print axioms` line.
3. **New experiments (#1, #5).** To make the empirical section positive rather than negative, run:
   - decoupled paths (false-affirmative → true-negation, and same-polarity attribution swaps);
   - a polarity-probe head;
   - matched nulls on the endogenous and translation runs;
   - ≥5 training seeds.
   These need GPU or Hugging Face access, which this environment does not have.
4. **Reproducibility.** Add a requirements file with versions, the hardware and the runtime, and seed torch in `run_adversarial.py`.
5. **Citations.** Verify the 8 new bib entries against publisher pages; they were found via search snippets only.
6. **Before submission.** Set `\showneededfalse` only after items 2–5 are resolved or the corresponding sentences are removed.
