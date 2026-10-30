import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendices" =>

These appendices are the reference apparatus. Appendix A indexes the formal corpus
file by file; Appendix B is the notation glossary; Appendix C sets the two engines
side by side; Appendix D is the annotated bibliography; Appendix E says how to build
and audit everything.

# The Formal Corpus

The development is large but shallow in a specific sense. Almost everything reduces
to the three-line proof of `lawvere` in Chapter 1, or to a single application of a
value-crossing lemma.

A word on axioms before the tour, because the book makes a point of it. Lean's
kernel admits exactly three standard axioms beyond its type theory: `propext`
(propositional extensionality), `Classical.choice` (the axiom of choice), and
`Quot.sound` (the computation rule for quotients).

The split between axiom-free and classically clean is not a defect and not an
accident. It is the formal shadow of the book's two-engine thesis.

How to use the index that follows. Each library gets a paragraph on what it proves
as a whole, then a file-by-file list.

## Foundation: the core library (F\_01–F\_14)

`Foundation` is the trunk. It proves Lawvere's fixed-point theorem from nothing,
extracts the impossibility schema, and instantiates it across the classical
paradoxes and the AI-safety readings.

*`F_01`* (`F_01_LawvereCore`). The heart of everything. This file states and proves
the fixed-point theorem in both its surjective and its section form, then packages
the contrapositive. The boolean-diagonal results here are axiom-free.

 * `lawvere` : a universal `f : A → A → Y` forces every `t : Y → Y` to have a fixed
   point.
 * `lawvere_diagonal` : the same, but naming the diagonal behavior explicitly so the
   witness is visible.
 * `no_surjection_of_no_fixed_point` : if `t` has no fixed point, no `f` is
   point-surjective.
 * `fixed_point_free_blocks_universality` : the contrapositive stated as a block on
   universality.
 * `lawvere_section` : the section form Lawvere actually published, using `s : (A → Y) → A`
   with `f (s g) = g`…
 * `surjective_of_section` : a section gives point-surjectivity, tying the two forms
   together.
 * `fixedPoint_spec` : the constructed fixed point satisfies its defining equation.
 * `no_universal_with_FPF` : no universal system when the output carries a
   fixed-point-free map, stated for a given `t`.
 * `no_universal_of_FPF_type` : the same phrased as a property of the output type.
 * `lawvere_universal_fixed_point` : universality and a chosen `t` together produce
   the fixed point, the form reused downstream.

*`F_02`* (`F_02_RiceTheorem`). Rice's theorem as a diagonal. Any external decision
procedure that claims to read a nontrivial semantic property of behaviors mismatches
some behavior. Axiom-free at the boolean core.

 * `rice_diagonal` : an external classifier disagrees with the true property on a
   diagonal input.
 * `rice_general` : the general statement that no total classifier decides a
   nontrivial behavioral property.
 * `boolean_diagonal_mismatch` : the boolean instance where the mismatch is a single
   flipped bit.
 * `no_automated_self_test` : no system can run a complete correct self-test of its
   own behavior.

*`F_03`* (`F_03_VerificationLimit`). The verifier version. A universal system cannot
have a fixed-point-free output map, so no complete self-verifier exists over its own
outputs.

 * `no_universal_with_fpf_output` : universality is incompatible with any
   fixed-point-free output transformation.
 * `no_universal_AI_output_type` : the same for an abstract prompt-to-output system.
 * `no_universal_bool_LLM` : specialized to boolean verdicts, no universal
   boolean-output model.
 * `no_universal_nat_LLM` : specialized to natural-number outputs via the successor
   map, which has no fixed point.

*`F_04`* (`F_04_CalibrationUnified`). The confidence reading, still discrete. Here
the output is a probability and the flip is "reflect across one half," whose only
fixed point is the value one half. This is where calibration first meets the
diagonal, and it is the bridge to the analytic hallucination results.

 * `half_complement_fixed_point` : one half is the unique fixed point of the
   probability complement.
 * `complement_no_fp_off_half` : off one half, the complement moves you.
 * `calibration_diagonal_hits_half` : the diagonal question drives a calibrated
   model's confidence to exactly one half.
 * `calibration_no_strict_avoidance` : a calibrated universal model cannot strictly
   avoid the half-confidence boundary.
 * `hallucination_via_lawvere` : the hallucination phenomenon derived directly from
   `lawvere`.

*`F_05`* (`F_05_DeceptionTheorem`). Alignment as a fixed-point obstruction. If an
"aligned" transformation of behavior has no fixed point, no universal system can be
uniformly aligned.

 * `deception_diagonal` : the diagonal behavior a safety filter cannot align with.
 * `no_universal_aligned_system` : no universal system is aligned under a
   fixed-point-free alignment map.
 * `no_universal_safe_LLM` : the LLM reading, no universal model is uniformly safe.
 * `two_diagonals` : two distinct diagonal constructions coincide as witnesses, a
   lemma the corner results reuse.

*`F_06`* (`F_06_OversightHierarchy`). Oversight does not escape the diagonal.
Stacking a watcher on a watcher inherits universality and inherits the diagonal, at
every finite level.

 * `pairwise_oversight_inherits` : a two-party oversight pair inherits the diagonal.
 * `chain_inherits` : a finite chain of overseers inherits it.
 * `oversight_no_escape` : no oversight layer removes the fixed point.
 * `reflective_tower` : an iterated tower of reflection stays universal.
 * `no_level_escapes` : no level of the tower escapes the impossibility.

*`F_07`* (`F_07_CompositionFailure`). Post-processing does not help. Composing any
map after a universal system leaves a universal system, so wrappers and filters
cannot break self-reference.

 * `composition_universal` : composition with a surjection preserves universality.
 * `composition_inherits_diagonal` : the composed system inherits the diagonal.
 * `post_processing_no_escape` : no post-processor removes the fixed point.
 * `two_stage_inherits_diagonal` : a two-stage pipeline still has the diagonal.
 * `two_stage_no_escape` : the two-stage pipeline does not escape.
 * `iterCompose_universal` : iterated composition preserves universality.
 * `iterCompose_inherits_diagonal` : iterated composition inherits the diagonal.
 * `iterCompose_no_escape` : no number of iterations escapes.

*`F_08`* (`F_08_SpecificationBound`). The counting-with-teeth file. Cantor's
power-set gap in its Lean form: the behaviors of a system are strictly more numerous
than its indices, so some behavior is unspecifiable.

 * `cantor_set` : no surjection from `A` onto `Set A`.
 * `specification_bound` : the space of behaviors strictly exceeds any indexing.
 * `behavior_unspecifiable` : some behavior has no specification.
 * `powerset_strictly_larger` : the power set is strictly larger, stated directly.
 * `bool_specification_bound` : the boolean-indicator form of the same bound.

*`F_09`* (`F_09_QuantitativeDegradation`). The first genuinely metric file, and the
hinge between the two engines inside `Foundation`.

 * `approx_lawvere` : an approximate fixed point exists within the flip's
   displacement.
 * `quantitative_trilemma` : the three safety properties trade off with a measurable
   slack rather than failing all at once.
 * `achievable_region_bound` : a bound on the region of jointly achievable property
   levels.
 * `quantitative_impossibility` : impossibility restated with an explicit error
   term.
 * `strict_limit_recovers_trilemma` : as the slack goes to zero the exact trilemma
   returns, so the discrete result is the limit of…

*`F_10`* (`F_10_MasterFoundation`, `F_10_FinalVerification`). The consolidation
layer. A single structure bundles the foundational hypotheses and a master theorem
derives every corner from it; the verification file runs the axiom audit.

 * `master_foundation_theorem` : one theorem from which the foundational corners
   follow.
 * `mirror_trilemma_instance` : the mirror (self-reference) trilemma as an instance.
 * `rice_instance` : Rice recovered as an instance.
 * `spec_bound_instance` : the specification bound recovered as an instance.
 * `nat_succ_instance` : the natural-number successor instance.
 * `unification_statement` : the statement that the instances are one theorem.

*`F_11`* (`F_11_HallucinationGodel`). The Gödel-style naming of the hallucination
result. The liar query is named explicitly, and the trilemma is stated as an
impossibility. This file ends with `#print axioms` on its headline results; the
boolean core is axiom-free.

 * `bool_not_fpf` : boolean negation has no fixed point, proved by `decide`.
 * `tarski_liar` : the Tarski-style undefinability liar for a truth predicate.
 * `hallucination_liar_query` : the exact query on which a reflective model must
   contradict itself.
 * `hallucination_trilemma_godel` : the hallucination trilemma as a self-reference
   impossibility.
 * `controllers_agree` : the boolean and propositional flips agree as controllers.

*`F_12`* (`F_12_DefenseGodel`). The same move for defenses. A defense that judges
prompts, including prompts about its own judgments, is a reflective verdict, so it
is impossible, and the file shows the defense engine is the hallucination engine.

 * `defense_liar_query` : the prompt injection no wrapper neutralizes, as a liar.
 * `defense_trilemma_godel` : the defense trilemma in Gödel form.
 * `defense_trilemma_lawvere` : the same via `lawvere` directly.
 * `reflective_verdict_impossible` : no reflective verdict exists.
 * `defense_is_hallucination_engine` : the two impossibilities share one proof.

*`F_13`* (`F_13_UnifiedTrilemmata`). The unification. All three trilemmas, the
hallucination, the defense, and the truth-boundary coupling, are folded into one
statement about reflective verdicts. Axiom audit printed at the end.

 * `no_reflective_verdict` : the one-line engine, no reflective verdict exists.
 * `schema_boundary` : the schema that produces the boundary object.
 * `coupling_trilemma_godel` : the truth-boundary coupling in Gödel form.
 * `trilemmata_unified` : the three trilemmas as a single theorem.

*`F_14`* (`F_14_JSpace`). The interpretability reading. A probe that reads a
judgment off a model's own activations, over a space rich enough to encode any
readout, is again a reflective verdict, so a complete self-reading probe is
impossible. This is the formal core behind the J-space chapter.

 * `jspace_readout_impossible` : no complete readout of a model's own judgments from
   its activations.
 * `jspace_coupled_activation` : the activation on which the readout must fail.
 * `jspace_is_the_same_engine` : the interpretability obstruction is `lawvere`
   again.

## CCHProofs: the Control-Corner-Hallucination trilemma (CCH\_01–CCH\_Master)

`CCHProofs` develops the trilemma as a geometry of three properties: Universality,
Control, and Transparency, of which any system can enjoy at most two. It restates
Lawvere in its own vocabulary, proves Cantor and the fixed-point-free lemmas, then
walks the three corners one at a time before assembling the master statement.

*`CCH_01`* (`CCH_01_Foundations`). Definitions and the dictionary between the
property language and the fixed-point language.

 * `nonTrivial_iff_no_fixed_point` : a controller is nontrivial exactly when it has
   no fixed point.
 * `universal_iff_surjective` : universality is point-surjectivity.
 * `transparent_eq_diag` : transparency is representability of the diagonal.
 * `nonTrivial_apply`, `universal_exists` : the elimination forms of the two
   definitions.
 * `isUniversal_iff`, `isControlled_iff`, `isTransparent_iff` : the structure-level
   restatements.
 * `isTransparent_eq_diag` : transparency as diagonal equality at the structure
   level.

*`CCH_02`* (`CCH_02_Lawvere`). Lawvere inside the CCH vocabulary.

 * `lawvere_fixed_point` : the fixed-point theorem, CCH form.
 * `no_surjection_of_no_fixed_point` : Cantor's contrapositive.
 * `universal_implies_fixed_point` : universality forces the fixed point.
 * `fixed_point_free_rules_out_universal` : the block on universality.
 * `lawvereFixedPoint_spec` : the fixed point meets its spec.
 * `lawvere_via_section`, `surjective_of_section` : the section form and its bridge.
 * `lawvere_universal_fixed_point` : the packaged form reused by the corners.

*`CCH_03`* (`CCH_03_Cantor`). Cantor, in surjection and power-set forms. Axiom-free.

 * `bool_not_no_fixed_point` : boolean negation has no fixed point.
 * `cantor_no_surjection` : no surjection onto the boolean behaviors.
 * `cantor_no_surjection_set` : no surjection onto the power set.
 * `no_universal_bool_system` : no universal boolean system.

*`CCH_04`* (`CCH_04_FixedPointFree`). A small library of fixed-point-free maps, the
raw material for corners. Axiom-free.

 * `bool_not_fixedPointFree` : boolean negation is fixed-point-free.
 * `succ_fixedPointFree`, `int_succ_fixedPointFree` : successor on the naturals and
   on the integers.
 * `no_surjection_of_fixedPointFree`, `fixedPointFree_blocks_universality` : the two
   block forms.
 * `fixedPointFree_iff` : the characterization of fixed-point-freeness.
 * `not_not_eq_id` : double negation is the identity, the reason a single flip and
   not a double one is needed.
 * `empty_fixedPointFree`, `unit_no_fixedPointFree` : the endpoints, everything on
   the empty type is fixed-point-free and nothing on `Unit` is.
 * `lawvere_section`, `no_section_of_fixedPointFree` : the section-form
   counterparts.

*`CCH_05`* (`CCH_05_Controllers`). The theory of controllers, the maps that play the
role of `t`. A controller is nontrivial when it has no fixed point.

 * `bool_not_nonTrivial`, `nat_succ_nonTrivial` : examples of nontrivial
   controllers.
 * `id_not_nonTrivial` : the identity is never nontrivial.
 * `nonTrivial_iff_no_fixed_point`, `nonTrivial_iff_no_fp_exists` : the two
   characterizations.
 * `controlled_iff` : control expressed via the controller.
 * `universal_excludes_nonTrivial_controller` : universality excludes a nontrivial
   controller.
 * `universal_implies_no_nonTrivial_controller` : the same as an implication.
 * `controlled_universal_nonTrivial_contradiction` : the three-way clash at the
   heart of the trilemma.
 * `nonTrivial_of_image`, `nonTrivial_no_fixed`, `exists_fixed_not_nonTrivial` :
   transport and existence lemmas.
 * `bivalent_nonTrivial`, `nonTrivial_bivalent_of_inhabited` : the bivalent-output
   cases.

*`CCH_06`* (`CCH_06_Transparency`). Transparency, the property that the diagonal is
itself a named behavior.

 * `transparent_iff_eq_diag` : transparency is diagonal equality.
 * `diag_is_transparent` : the diagonal is always transparent for itself.
 * `transparent_symm` : symmetry of the transparency relation.
 * `universal_diag_in_image`, `transparent_universal_diag_representable` : a
   universal transparent system represents its own diagonal.
 * `transparent_universal_self_fixed` : which forces a self-fixed point.
 * `transparent_universal_blocks_nonTrivial` : and blocks any nontrivial controller.
 * `trivial_transparent_construction` : a trivial witness showing the corner is
   inhabited when universality is dropped.

*`CCH_07`* (`CCH_07_CornerUC`). The Universal-plus-Controlled corner, which cannot
also be Transparent.

 * `corner_UC_not_T` : Universal and Controlled excludes Transparent.
 * `corner_UC_impossible` : the corner as an impossibility.
 * `corner_UC_strong` : a strengthened version.
 * `universal_diagonal_hits_fixed_point` : the diagonal lands on the fixed point.
 * `defense_trilemma_face` : this corner is the defense trilemma face.
 * `corner_UC_exists_failure`, `corner_UC_prediction_fixed_point` : the explicit
   failure witness and the prediction fixed point.

*`CCH_08`* (`CCH_08_CornerUT`). The Universal-plus-Transparent corner, which cannot
be Controlled.

 * `corner_UT_not_C` : Universal and Transparent excludes Controlled.
 * `corner_UT_impossible` : the corner as an impossibility.
 * `hallucination_trilemma_face` : this corner is the hallucination trilemma face.
 * `corner_UT_witness_identity`, `corner_UT_needs_universality` : the witness and
   the necessity of the universality hypothesis.

*`CCH_09`* (`CCH_09_CornerCT`). The Controlled-plus-Transparent corner, which cannot
be Universal. This is the Rice face.

 * `corner_CT_not_U` : Controlled and Transparent excludes Universal.
 * `corner_CT_impossible` : the corner as an impossibility.
 * `corner_CT_bool_specialization` : the boolean specialization.
 * `rice_face` : this corner is the Rice face.
 * `corner_CT_witness`, `corner_CT_not_U_of_fpf`, `corner_CT_bool_via_fpf` : the
   witness and the fixed-point-free routes.

*CCH\_LLM (`CCH_LLM_Direct`).* The trilemma spelled out for an in-context learner `M : LLM Prompt Token`,
so the abstract corners become claims about a model.

 * `iclUniversal_iff` : in-context universality is surjectivity of the learner.
 * `LLM_diagonal_fixed_point`, `LLM_no_fixed_point_free` : the diagonal and its
   consequence for the model.
 * `LLM_trilemma` : the trilemma for the model.
 * `LLM_corner_UC`, `LLM_corner_UT`, `LLM_corner_CT` : the three corners, model
   form.
 * `LLM_safety_corner_UC`, `LLM_safety_self_misclassification` : the safety
   readings, including that the model must misclassify itself somewhere.
 * `bool_not_controller` : the boolean flip is a controller.
 * `LLM_approx_fixed_point`, `LLM_approx_trilemma` : the approximate versions with a
   confidence output.

*CCH\_Master (`CCH_MasterTrilemma`, `CCH_FinalVerification`).* The consolidated
trilemma over a `CCHStructure`, and the axiom audit.

 * `cch_master_trilemma` : at most two of Universal, Controlled, Transparent.
 * `cch_corner_UC`, `cch_corner_UT`, `cch_corner_CT` : the three corners at the
   structure level.
 * `cch_at_most_two` : the counting statement, no more than two properties hold.

## HallucinationProofs: the truth-boundary theory (HoF\_01–HoF\_Master)

`HallucinationProofs` is where the second engine takes over. Instead of a diagonal
over a self-naming domain, it works with a signed truth distance `δ`, a confidence
`conf`, and a truth threshold, and it uses value-crossing, the intermediate value
theorem and its topological cousin the Borsuk-Ulam theorem, to force the existence
of a boundary point where the model is confidently on the fence.

*`HoF_01`* (`HoF_01_Foundations`). The truth set and its neighbors, defined from the
signed distance `δ` and the model's confidence.

 * `mem_truthSet`, `mem_falseSet`, `mem_truthBoundary`, `mem_strictTruth`,
   `mem_highConfRegion` : membership unfoldings for the five basic regions.
 * `truthSet_isClosed`, `falseSet_isOpen`, `truthBoundary_isClosed`,
   `strictTruth_isOpen`, `highConfRegion_isClosed` : the topology of each region
   when `δ` and `conf` are continuous.
 * `truth_partition`, `truthSet_union_falseSet`, `truthSet_falseSet_disjoint` : the
   space splits cleanly into truth and falsehood.
 * `strictTruth_subset_truthSet`, `truthBoundary_subset_truthSet`,
   `truthSet_eq_strictTruth_union_boundary` : the inclusions and the decomposition
   of the truth set into strict interior plus boundary.
 * `strictTruth_falseSet_disjoint`, `truthBoundary_falseSet_disjoint` : the
   separations used later.

*`HoF_02`* (`HoF_02_TruthSet`). The truth set as a topological object in its own
right, with the non-closedness that forces a boundary.

 * `truthSet_isClosed`, `falseSet_isOpen`, `strictTruth_isOpen`,
   `truthBoundary_isClosed` : the topology restated for the abstract space.
 * `truthBoundary_nonempty` : the boundary is nonempty under the covering
   hypothesis.
 * `strictTruth_falseSet_separated`, `strictTruth_falseSet_no_intersect` : truth and
   falsehood do not touch except through the boundary.
 * `strictTruth_not_closed`, `boundary_point_in_closure_of_strictTruth` : the strict
   truth region is not closed, and its closure reaches the boundary.

*`HoF_03`* (`HoF_03_BoundaryCrossing`). The intermediate value theorem doing its
work: a path from a confident-true point to a confident-false point must cross.

 * `confidence_path_crosses_half` : a confidence path from above to below one half
   crosses one half.
 * `path_crosses_truth_boundary` : a path from truth to falsehood crosses the truth
   boundary.
 * `model_truth_boundary_nonempty` : the model's truth boundary is nonempty.
 * `model_confidence_half_set_nonempty`, `confidence_half_nonempty` : the
   half-confidence level set is nonempty.
 * `model_truth_boundary_isClosed` : and closed.

*`HoF_04`* (`HoF_04_Faithfulness`). Faithfulness, the property that high confidence
implies truth, and what it forces at the boundary.

 * `StrongFaithful.toFaithful` : strong faithfulness implies faithfulness.
 * `faithful_image_in_truth` : a faithful model's confident answers are true.
 * `highConf_closed`, `highConf_open` : the high-confidence region's topology under
   the two conventions.
 * `truth_preimage_closed`, `faithful_closure_in_truth` : the truth preimage is
   closed and its closure stays in truth.
 * `faithful_at_half_boundary` : at the half-confidence boundary a faithful model is
   pinned to the truth boundary.
 * `low_conf_unconstrained` : where confidence is low the model is free.

*`HoF_05`* (`HoF_05_Coverage`). Coverage, the hypothesis that the model's answers
straddle both sides, which is what makes the boundary unavoidable.

 * `covering_image_straddles_zero` : a covering model's signed distances take both
   signs.
 * `denseCoverage_closure_eq_univ` : dense coverage fills the space in closure.
 * `covering_yields_truth_boundary_point` : coverage produces a boundary point.
 * `covering_yields_two_sided_witnesses`, `covering_two_closed_sides` : two-sided
   witnesses and their closedness.
 * `covering_abs_zero`, `denseCoverage_approximable` : the distance hits zero, and
   dense coverage is approximable.

*`HoF_06`* (`HoF_06_Calibration`). Calibration, the link between confidence and
truth probability, and the half-boundary it induces.

 * `calibrated_levelSet_eq` : the calibrated level set matches the truth level set.
 * `confHalf_isClosed` : the half-confidence set is closed.
 * `monotoneCalibrated_half_on_boundary` : monotone calibration puts half-confidence
   on the truth boundary.
 * `calibrated_confHalf_nonempty` : the half set is nonempty under calibration.
 * `confHalf_implies_truthBoundary` : half confidence implies boundary membership.
 * `off_boundary_conf_not_half` : off the boundary, confidence is never exactly
   half.

*`HoF_07`* (`HoF_07_TrilemmaCore`). The continuous hallucination trilemma. A model
cannot be faithful, calibrated, and covering all at once; some question sits on the
boundary with confidence exactly one half.

 * `hallucination_trilemma_strict` : the strict form of the trilemma.
 * `hallucination_trilemma` : the headline continuous trilemma.
 * `hallucination_trilemma_unfolded`, `hallucination_trilemma_strict_unfolded` : the
   same with definitions unfolded, for downstream use.

*`HoF_08`* (`HoF_08_BorsukUlam`). The topological upgrade. When the question space
is a sphere and the model is antipodally symmetric, the Borsuk-Ulam theorem forces a
boundary point without needing a chosen path. These results use the three standard
axioms.

 * `antipodal_odd_has_zero` : an odd continuous function on a sphere has a zero.
 * `antipodal_yields_truth_boundary` : antipodal symmetry yields a boundary point.
 * `antipodal_hallucination_trilemma` : the trilemma via Borsuk-Ulam.
 * `approx_odd_near_zero` : an approximately odd function is near zero somewhere.
 * `sphere_odd_has_zero` : the higher-dimensional sphere statement.

*`HoF_09`* (`HoF_09_Discrete`). The trilemma with no topology at all, over a finite
or discrete question space using a strict trichotomy and a sign change. Axiom-light,
the discrete core needs no analysis.

 * `strictCal_conf_trichotomy` : confidence is above, below, or exactly at half.
 * `discrete_partition`, `discrete_two_partition` : the discrete partitions.
 * `discrete_trilemma_decisive_impossible` : a decisive discrete model is
   impossible.
 * `discrete_sign_change` : a sign change is forced between covered points.
 * `discrete_hallucination` : the discrete hallucination result.

*`HoF_10`* (`HoF_10_PureDiscrete`). The fully combinatorial version, connecting the
boundary story back to the diagonal engine of `Foundation`.

 * `boundary_conf_half` : the boundary question has confidence one half.
 * `boundary_question_impossible` : the boundary question cannot be answered
   decisively.
 * `discrete_hallucination_trilemma` : the pure-discrete trilemma.
 * `faithful_iff_boundary_free` : faithfulness is exactly the absence of a boundary
   question.
 * `hallucination_trilemma_via_pure_discrete` : the trilemma proved with no
   analysis.

*`HoF_11`* (`HoF_11_MultiTurnProbabilistic`). The multi-turn and stochastic
extension. An adversary steering a conversation can reach the boundary, and the
expected behavior over turns still couples.

 * `multi_turn_per_turn`, `multi_turn_history_dependent` : per-turn and
   history-dependent forms.
 * `adversary_boundary_reachable` : an adversary can reach the boundary.
 * `stochastic_coupling_expected`, `stochastic_trilemma_expected` : coupling and the
   trilemma in expectation.
 * `stochastic_dichotomy`, `boundary_dichotomy` : the stochastic and boundary
   dichotomies.

*`HoF_12`* (`HoF_12_Approximate`). The approximate trilemma with explicit slack
parameters `ε`, and the bridges back to the exact statements. Axiom audit printed.

 * `approx_trilemma` : the trilemma with a slack `ε`.
 * `exact_from_approx` : the exact trilemma recovered as `ε` goes to zero.
 * `strictCalibrated_to_epsCalibrated_zero_half`,
   `trilemmaCovering_to_epsCovering_zero` : the exact hypotheses as zero-slack
   cases.
 * `no_boundary_in_upper_band`, `no_boundary_in_upper_band_two_slack` : where no
   boundary can hide.
 * `epsCalibrated_iff_twoSlack`, `two_slack_approx_coupling`,
   `truth_slack_must_be_positive`, `two_slack_band_bridge` : the two-slack
   reformulation and its coupling.

*`HoF_13`* (`HoF_13_BoundaryCoupling`). The coupling theorem, the truth-boundary
analogue of the reflective-verdict impossibility, with the closed-versus-open
guarantee dichotomy that Chapter 3 turns on. Axiom audit printed.

 * `boundary_coupling` : truth and confidence are coupled at the boundary.
 * `closed_guarantee_impossible` : a closed (two-sided) guarantee at the boundary is
   impossible.
 * `open_guarantee_silent` : an open guarantee is silent exactly on the boundary.
 * `slack_must_be_positive` : any honest guarantee needs strictly positive slack.

*`HoF_14`* (`HoF_14_QuantitativeGeometry`). The metric geometry of the boundary, the
tubes and the linear-probe cosets that feed the interpretability chapter. Axiom
audit printed.

 * `confidence_gap_width` : the width of the confidence gap around the boundary.
 * `truth_margin_tube`, `ambiguity_tube` : the truth-margin tube and the ambiguity
   tube around the boundary.
 * `linear_probe_boundary_coset` : a linear probe's boundary is an affine coset.
 * `linear_probe_boundary_dim` : its dimension.

*`HoF_15`* (`HoF_15_NonlinearBoundary`). The nonlinear boundary, its regular points
and tangent structure.

 * `regular_point_is_crossing` : a regular point of the boundary is a genuine
   crossing.
 * `nonlinear_boundary_tangent` : the tangent to a nonlinear boundary.
 * `tangent_hyperplane_dim` : the dimension of the tangent hyperplane.

*HoF\_Instantiation (`HoF_Instantiation_PromptSpace`).* The trilemma over a concrete
prompt space of dimension `d` with `k` classes, so the abstract theorem becomes a
statement about prompts.

 * `prompt_truth_boundary_exists` : the prompt-space truth boundary is nonempty.
 * `prompt_confidence_half_exists` : a half-confidence prompt exists.
 * `prompt_hallucination_trilemma` : the trilemma over prompt space.
 * `prompt_near_boundary` : prompts arbitrarily near the boundary exist.

*HoF\_Master (`HoF_MasterTheorem`, `HoF_FinalVerification`).* The consolidated
hallucination theorem over a `HallucinationStructure`, and the axiom audit.

 * `hallucination_master_theorem` : the master statement bundling the hypotheses.
 * `hallucination_trilemma_three_clause` : the three-clause form, at most two of
   faithful, calibrated, covering.

## ManifoldProofs: the geometry of attack basins (`MoF`)

`ManifoldProofs` is the quantitative wing. Where `HallucinationProofs` establishes
that a boundary exists, `ManifoldProofs` measures it: the volume of the safe basin,
the radius of robustness `robustnessRadius = (fp - τ) / L`, the cost of an attack
that walks to the failure manifold, and how these scale with dimension and model
size.

The base modules fix the objects. `MoF_01_Foundations` defines the safety score `f`,
the threshold `τ`, and the safe, unsafe, boundary, and failure-manifold regions,
with their topology (`mem_safeRegion`, `boundary_isCompact`, `space_partition`,
`failureManifold_eq_union`).

The Lipschitz group turns qualitative crossing into quantitative robustness.
`MoF_04_LipschitzBasin` proves the robustness radius is positive and that a ball of
that radius stays in the basin (`lipschitz_basin_ball`, `robustnessRadius_pos`,
`basin_ball_subset`, `perturbation_stability`, `robustnessRadius_monotone`).

The defense and scaling group. `MoF_08_DefenseBarriers` formalizes barriers a
defense erects around the basin.

The measure and coarea group sharpens the volume estimates. `MoF_17_CoareaBound`
uses the coarea formula to bound the boundary's measure; `MoF_18_ConeBound` gives a
cone estimate; `MoF_19_OptimalDefense` characterizes the defense that maximizes the
robustness radius; `MoF_20_RefinedPersistence` and `MoF_21_GradientChain` refine
persistence of the basin under perturbation and chain gradient steps together.

The advanced group `MoF_Adv_01` through `MoF_Adv_10` covers basin connectedness,
boundary dimension, fine-tuning, model scale, convexity, approximation,
fragmentation, stability, the optimization landscape, and measure bounds, in that
order. The cost group `MoF_Cost_01` through `MoF_Cost_10` is the attack-economics
core: ball volume, basin volume, hitting time, concentration, attack cost, defense
cost, transfer cost, the cost ratio, Lipschitz estimation, and the unified theory.

## Reading the corpus as one argument

Put the four libraries in a line and the book's thesis is visible in the dependency
graph. `Foundation` proves the engine and reads it into every AI-safety corner
combinatorially.

A few cross-library correspondences are worth naming, because they are the seams
where the book's claims about sameness become theorems rather than assertions. The
hallucination result appears three times, and the three are provably the same
boundary.

The two-engine seam is the most important one. `HoF_07`'s continuous trilemma and
`F_11`'s Gödel-form trilemma are about the same phenomenon and reach the same
boundary question, but they are genuinely different proofs with different axiom
footprints, and the book keeps both on purpose.

# A Notation Glossary

The book reuses a small alphabet across very different readings. The same letter can
be a prompt in one chapter and an activation vector in another; what stays fixed is
the role the letter plays in the argument. This glossary lists each symbol with its
meaning and, where it helps, the role it plays in the engine.

Two conventions help before the list. First, the letters track roles, not types.

*Sets and spaces.*

 * `A` : the domain of \_indices\_.
 * `Y` : the set of \_outcomes\_ a behavior can produce.
 * `Q` : a domain of \_questions\_ or queries over which a verdict is defined.
 * `X` : the ambient space in the manifold chapters, the space attacks move through.
 * `Z` : an intermediate type in composition results, the target of a
   post-processor.
 * `Prompt`, `Token`, `Output`, `Act` : concrete instantiations of `A` and `Y`, the
   prompt space, token space, output space, and…
 * `Set A` : the power set of `A`, identified with indicator functions `A → Bool`.

*The system and its parts.*

 * `f` : a \_system\_, `f : A → A → Y`.
 * `g` : an arbitrary behavior `A → Y`, the thing universality asks to be named.
 * `d` : the \_diagonal behavior\_, `d a = t (f a a)`, apply each behavior to its
   own name and then flip.
 * `s` : a \_section\_, `s : (A → Y) → A`, a chosen index for each behavior, with `f (s g) = g`.
 * `M` : a \_model\_, usually `M : Q → A × ℝ`, returning an answer and a confidence.

*The engine's moving parts.*

 * `t` : the \_controller\_ or output flip, `t : Y → Y`.
 * `v` : a \_reflective verdict\_, `v : Q → Q → Bool`, a boolean self-application in
   which every…
 * `a₀`, `q₀`, `q_0` : the \_liar\_, the diagonal witness.

*The analytic alphabet.*

 * `δ` : the \_signed truth distance\_, `δ (q, a)`, negative on true answers,
   positive on false ones,…
 * `conf`, `confOf` : the model's \_confidence\_, the second projection of `M`.
 * `τ` : the \_threshold\_ in the manifold chapters.
 * `ε` : a \_slack\_ or tolerance.
 * `c` : a confidence \_level\_ used to cut out the high-confidence region.
 * `L` : a \_Lipschitz constant\_ for the safety score, the rate at which the score
   can change per…
 * `fp` : the safety score at a point, written `fp` in `robustnessRadius = (fp - τ) / L`.

*Regions and objects.*

 * \_truth set\_, \_false set\_ : where `δ` is nonpositive and where it is positive.
 * \_strict truth\_ : the open interior of the truth set, where `δ` is strictly
   negative.
 * \_truth boundary\_ : the zero set of `δ`, where true meets false.
 * \_high-confidence region\_ : where `conf` is at least `c`.
 * \_basin\_ : the safe basin, the open set where the score `f` exceeds `τ`, of
   positive measure and…
 * \_failure manifold\_ : the closure of the unsafe region against the boundary, the
   codimension-one set an attacker…
 * \_robustness radius\_ : `(fp - τ) / L`, how far a safe point can be pushed before
   it crosses.

*Properties named in the trilemmas.*

 * \_universal\_, \_point-surjective\_ : every behavior is named, `∀ g, ∃ a, f a = g`.
 * \_faithful\_ : high confidence implies truth.
 * \_calibrated\_ : confidence matches truth probability;
 * \_covering\_ : the model's answers straddle both sides of the boundary;
 * \_control\_, \_nontrivial controller\_ : the output can be steered by a `t` with
   no fixed point.
 * \_transparent\_ : the diagonal is itself a named behavior.

*Logical and Lean symbols.*

 * `∀`, `∃`, `¬`, `→`, `≠`, `=` : the usual quantifiers and connectives.
 * `!` : boolean negation, the controller in the Cantor instance.
 * `Nat.succ`, `+ 1` : the successor, a fixed-point-free controller on the naturals
   and integers.
 * `False`, `True`, `Prop`, `Bool` : Lean's falsehood, truth, the type of
   propositions, and the type of booleans.
 * `congrFun` : the step "equal functions agree at every point," the one nontrivial
   move in the proof of…
 * `decide` : the tactic that settles a finite boolean claim, how `bool_not_fpf` is
   proved axiom-free.
 * `closure`, `Continuous`, `IsOpen`, `IsClosed`, `IsCompact` : the topological
   vocabulary the analytic chapters run on.

# The Two Engines, Side by Side

| | Diagonal | Value-crossing |
|---|---|---|
| Hypothesis on the domain | universality: every behavior is named | connectedness |
| Hypothesis on the maps | none | continuity, and Lipschitz for quantities |
| Controller | fixed-point-free `t`, typically `!·` | complement `y ↦ 1 - y`, one fixed point at the threshold |
| Output | a liar index `a₀` | a boundary point `q₀` |
| Axioms | none in the Boolean core | the three standard ones, through Mathlib's reals |
| Quantitative content | none | band widths, basin volumes, attack and defense cost |
| Escaped by | breaking universality | breaking connectedness, coverage, continuity, or exact separation |

The two rows that matter are the last two. The diagonal buys an unconditional
existence proof with the smallest possible trust story and gives nothing measurable.

They agree where both apply. `Foundation.F_04` records the agreement as a theorem
rather than an analogy: both engines extract the fixed point of the same controller,
the Boolean flip having none and the real complement having exactly one, at the
threshold.

The practical rule for reading the corpus is to ask which engine is running. A claim
of bare impossibility is the diagonal. A claim carrying a number — a width, a rate,
a probability, a cost — is the value-crossing engine and its Lipschitz refinements.

# Annotated Bibliography

The book stands on a short list of sources. The foundational papers are the ones
that isolate the diagonal and the boundary; the companion papers are the AI-safety
readings this development formalizes; the interpretability work is where the two
engines are seen firing together.

*Foundational.*

 * F. William Lawvere, \_Diagonal arguments and cartesian closed categories\_
   (1969). The origin of the whole book. Lawvere shows that Cantor, Russell, Gödel,
   Tarski, and Turing are one theorem about a point-surjective map in a cartesian
   closed category, and that the theorem is a fixed-point statement. Every
   impossibility in these notes is an instance of his lemma, and `lawvere` in `F_01`
   is his proof in Lean.
 * Noson Yanofsky, \_A universal approach to self-referential paradoxes,
   incompleteness and fixed points\_ (2003). The most readable modern account of
   Lawvere's unification, working the classical instances out by hand. It is the
   template Chapter 2 follows, and the reason the book can present five paradoxes as
   one schema without categorical machinery.
 * Kurt Gödel, on the incompleteness theorems (1931). The archetype of a
   self-referential impossibility: a sentence that asserts its own unprovability is
   a fixed point of the provability flip. In the corpus this is the shape of
   `tarski_liar` and the Gödel-form trilemma statements in `F_11`–`F_13`.
 * Alfred Tarski, on the undefinability of truth (1936). Truth cannot be defined
   inside the language it is about, because the liar is a fixed point of negation.
   This is the direct ancestor of the reflective-verdict impossibility
   `no_reflective_verdict`, and `tarski_liar` carries his name for that reason.
 * Henry Gordon Rice, on properties of recursively enumerable sets (1953). Every
   nontrivial semantic property of programs is undecidable. The book reads this as
   "no complete automated self-test," formalized in `F_02` and appearing as the
   Controlled-Transparent corner `rice_face` of the CCH trilemma.
 * Georg Cantor, on the non-denumerability of the reals and the power-set theorem
   (1874, 1891). The first diagonal, and the counting-with-teeth that no set
   surjects onto its power set. It is `cantor_set` and `specification_bound` in
   `F_08`, and the boolean flip `bool_not_fpf` is Cantor's flipped diagonal digit.

*Companion papers.*

 * \_The Hallucination Trilemma\_. The claim that a language model cannot be
   simultaneously faithful, calibrated, and covering; some question forces
   confidence to the fence. This is the subject of `HallucinationProofs`, with the
   continuous proof in `HoF_07` and the Gödel-form proof in `F_11`. The book's
   Chapter 3 is the argument that these three properties really do make a model's
   verdict reflective.
 * \_The Defense Trilemma\_. The claim that a prompt-injection defense that judges
   prompts, including prompts about its own judgments, cannot be universal,
   controlled, and transparent at once. Formalized in `F_12` and as the CCH corners,
   with `defense_is_hallucination_engine` showing it is the same theorem as the
   hallucination result.
 * \_Truth Has a Boundary\_. The coupling result: truth and confidence are pinned
   together on a boundary, and no honest guarantee can be two-sided there without
   positive slack. This is `HoF_13`'s `boundary_coupling`,
   `closed_guarantee_impossible`, and `slack_must_be_positive`, and it is what ties
   the diagonal's liar to the value engine's zero of `δ`.

*Interpretability.*

 * The \_J-space\_ interpretability work. The program of reading a model's judgments
   off its own activations. The book's contribution is negative and sharp: a
   complete self-reading probe is a reflective verdict, so it is impossible, and the
   boundary it fails on has the metric geometry of `HoF_14`. This is `F_14`'s
   `jspace_readout_impossible` and `jspace_is_the_same_engine`, the clearest place
   where the interpretability question and the diagonal turn out to be one question.

*How the sources fit together.* The foundational six are a single arc that the book
compresses into one theorem. Cantor supplies the diagonal move and the flipped
digit.

# Building and Checking This Thesis

*Layout.* Four Lake packages carry the corpus: `Foundation` (`F_01`–`F_14`),
`CCHProofs` (`CCH_01`–`CCH_Master`), `HallucinationProofs` (`HoF_01`–`HoF_15` with
instantiation, master, and verification files), and `ManifoldProofs` (the `MoF_`
families). The numbering is a reading order as much as a build order: lower numbers
are the engine and the setup, higher numbers the readings and refinements.

*Building the libraries.* From a package root, `lake exe cache get` fetches the
prebuilt Mathlib and `lake build` compiles the package. A successful build is the
whole guarantee: the kernel has checked every proof, and because the packages are
sorry-free a clean build means no gaps.

*Building the document.* `lake build` elaborates every code block in the chapters,
including the live proofs, and renders the manual. Because the blocks are elaborated
at build time, the proofs you read are the proofs the kernel accepted; there is no
separate step that could drift. This appendix contains no live blocks, only
backticked names, so it renders as reference text.

*Checking the prose against the corpus.* Elaboration checks the code blocks, but a
theorem stated in prose and attributed to a library is checked by nothing: rename
the declaration and the text keeps asserting it. The build script closes that gap
before calling Lean.

*Running the axiom audit.* `#print axioms name` reports the complete transitive axiom
list. Several files already end with these commands: `F_11`, `F_13`, `F_14`,
`CCH_FinalVerification`, `HoF_08`, `HoF_12`, `HoF_13`, `HoF_14`,
`HoF_FinalVerification`, and `MoF_FinalVerification`. To audit any other theorem,
add a line after its file's imports and rebuild.

*Reading the output.* Three outcomes matter. "Does not depend on any axioms" means
axiom-free in the strict sense, which is what the Boolean diagonal core reports. A
list of exactly `propext`, `Classical.choice`, and `Quot.sound` means classically
clean, which is what the analytic results report.

*A suggested check.* Build `Foundation` and print the axioms of `no_reflective_verdict`
in `F_13` and `hallucination_trilemma_godel` in `F_11`; the engine is clean. Then
build `HallucinationProofs` and print the axioms of `hallucination_trilemma` in
`HoF_07` and `boundary_coupling` in `HoF_13`; the three standard axioms appear where
the analysis enters.
