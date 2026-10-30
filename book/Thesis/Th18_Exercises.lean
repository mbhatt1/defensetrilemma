import VersoManual
import Thesis.Ch00_Preliminaries
import Thesis.Ch01_Diagonal
import Thesis.Ch02_ClassicalLimits
import Thesis.Ch03_Trilemmata
import Thesis.Ch04_FromLogicToAnalysis
import Thesis.Ch05_AttackGeometry
import Thesis.Ch06_ApproximateBridges
import Thesis.Ch07_AISafety
import Thesis.Ch08_JSpace
import Thesis.Ch09_CoTMonitoring
import Thesis.Ch10_LatentKnowledge
import Thesis.Ch11_Watermarking
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Exercises" =>

The exercises are collected here rather than distributed through the chapters, so
that the argument runs uninterrupted. They are grouped by the chapter they belong
to and numbered accordingly. Those marked (Lean) ask for a machine-checked term;
those marked (open) have no single answer.

# Preliminaries

_0.1_ Define `c0_triple` in both styles, prove `c0_triple 4 = 12` by `rfl`, and say
why `rfl` suffices.
_0.2_ Prove `p ∧ q → p` and `p → q → p ∧ q` in term mode; say which packs a
structure and which projects one.
_0.3_ Using only `congrFun`, derive `f 0 = g 0` from `h : f = g`, and name the
principle needed for the converse.
_0.4_ Prove `c0_pred 5 = 4` by `rfl`, and explain why `∀ n, c0_pred (n+1) = n` needs
a genuine proof though each instance is `rfl`.
_0.5_ Prove `∀ b : Bool, b && b = b` by `decide`, and say which hypothesis of
Definition 0.14 fails for `∀ n : Nat, n * 1 = n`.
_0.6_ Re-derive Example 0.25 by flipping the diagonal, then say why counting misleads
for infinite `A` and what the diagonal supplies instead.
_0.7_ Give a fixed-point-free `t : Bool → Bool`, show no `t : Unit → Unit` is one,
and say what that means for a system whose only outcome is "accept."
_0.8_ Find the fixed point of `t y = 1 - y` and relate it to the analytic threshold.
_0.9_ Prove the section form of the engine, identifying the step that shortens when a
section replaces a surjection.
_0.10_ Give a counterexample to Theorem 0.36 on a two-point discrete space, and
conclude why connectedness is not optional.
_0.11_ Predict, then check, `#print axioms` on a Boolean and an analytic result, and
say what the difference tells you.
_0.12_ Argue that two indices naming the twisted diagonal are both boundary objects
and that nothing selects one.
_0.13_ Prove a composite of injections is injective, and say why injectivity is the
retraction-side property and surjectivity the section-side one.
_0.14_ (open) Without symbols, explain why the intermediate value theorem and
Cantor's diagonal are the same argument, naming each engine's domain hypothesis,
outcome-map property, and boundary object.

# The Diagonal

_1.1_ Verify Example 1.3 by flipping `f a a`, and say why finiteness was essential to
the counting step but idle in the diagonal step.
_1.2_ (Lean) Prove Theorem 1.8 from scratch, and say why the section form needs no
`match`.
_1.3_ Show the converse of Corollary 1.10 fails, and state what the corollary does not
claim about `f`.
_1.4_ (Lean) Give a fixed-point-free endomap of a three-element type, modeling
`c1_optFlip_fpf`, and say what `c1_no_fpf_unit` means for a system that can only
accept.
_1.5_ Prove Cantor's usual form by identifying `Set A` with `A → Bool`, pointing to
the line corresponding to `bool_not_fpf`.
_1.6_ (Gödel.) Show a sentence asserting its own unprovability is a fixed-point-free
instance, and say which hypothesis corresponds to representability and which to
completeness.
_1.7_ (Tarski.) Repeat for truth, saying why Tarski's conclusion is about definability
and Gödel's about provability.
_1.8_ (Turing.) Cast halting as an instance and explain why the argument refutes `H`
rather than the diagonal program.
_1.9_ Show two indices naming the diagonal behavior are both liars, relating this to
non-uniqueness of the boundary question.
_1.10_ (Lean) Prove the one-sided refinement via `c1_lawvere_diagonal` and recover
`liar_query`.
_1.11_ In one paragraph without symbols, say why counting is the wrong intuition for
the infinite case.
_1.12_ Give a `Y` and `t` with exactly one fixed point and connect the result to
Kleene's theorem read forwards.
_1.13_ (Harder.) Formulate the partial version, and say which classical instance
arises when `t` only toggles `none`.
_1.14_ (Lean) Decide whether the flip swapping `none` with `some false` and fixing
`some true` is fixed-point-free, and use the answer to explain Rice's nontriviality.
_1.15_ Prove every section gives point-surjectivity and say why the converse needs
choice.
_1.16_ For `Bool`, `Unit`, a two-point verdict type, `Option Bool`, and a one-point
space, decide which admit a fixed-point-free endomap, and state the principle.
_1.17_ (open) Speculate on a system satisfying both universality and connectedness,
and what its boundary object would be.
_1.18_ (open) Phrase a safety desideratum as a universality claim and identify the
sentence someone must refute to escape it.

# The Classical Limits

_2.1_ Prove {lean}`c2_no_universal_bool` by a direct `match`, checking both proofs
give the same witness.
_2.2_ Show no `t : Unit → Unit` has `t u ≠ u`, and say why this is the degenerate row
of the table.
_2.3_ Write "no surjection `A → Set A`" using indicators, and say where the `Set`-form
proof uses decidability the `Bool` form avoids.
_2.4_ Derive `False` from `hmem`, concluding {lean}`c2_russell` has an empty
hypothesis, and relate this to the repairs of comprehension.
_2.5_ Prove `¬ (P ↔ ¬ P)` without classical axioms and say why the `Bool` version is
compiled instead.
_2.6_ Reprove {lean}`c2_godel_semantic` in tactic mode and confirm it depends on no
axioms.
_2.7_ Say which property of ordinary proof each derivability condition internalizes,
and why the third makes the second theorem harder.
_2.8_ State Löb's theorem as a fixed point, verify Gödel II is the case `φ = 0 = 1`,
and say why `Con(T)` is the antecedent Löb refuses.
_2.9_ Give the liar as the diagonal behavior in Tarski's theorem, and show a definable
truth predicate would fall to {lean}`c2_godel_semantic`.
_2.10_ Explain, in terms of recursive enumerability, why `Prov` is definable and
`True` is not.
_2.11_ (Harder.) Prove a two-input Turing theorem and show `a = b` recovers
{lean}`c2_turing_halting`.
_2.12_ Say why the contrarian program must be partial and why the argument fails if
deciders may abstain.
_2.13_ Show a nontrivial `P : Bool → Bool` is the identity or negation, and sketch the
reduction of `Foundation.rice_general`.
_2.14_ (Harder.) Write both cases of the reduction in Theorem 2.22 and say where
classical logic enters.
_2.15_ Fill in the table for Grelling–Nelson and for the `Y` combinator, saying
whether each fixed point is a contradiction or a construction.
_2.16_ (open) Say what distinguishes the destructive uses of the diagonal from the
constructive `Y` combinator.
_2.17_ (open) Force one AI-safety property into the recipe, naming `A`, `Y`, `t`, and
the universality hypothesis, and say what a working system gives up.
_2.18_ (open) Formulate a quantitative question Rice does not answer and say what
structure would make it precise.
_2.19_ State the section form categorically and identify, for Cantor and Turing, what
plays `Y`, `t`, and `s`.
_2.20_ (Harder.) Write the map whose fixed point Löb takes and show its fixed point at
`φ = 0 = 1` is Gödel II's sentence.
_2.21_ (open) Place three properties of a language model on the Rice–Shapiro spectrum
and say what changes when each is weakened to approximate.

# Three Trilemmata

_3.1_ Verify the three trilemma types differ only in the bound domain variable, and
say what {lean}`c3_trilemmata_unified` adds.
_3.2_ Write out in English the query {lean}`c3_hallucination_liar` produces, and say
which desideratum each escape drops.
_3.3_ Show in Lean that the hallucination and defense liars are the same witness.
_3.4_ Show the constant model is faithful and calibrated but not covering, and exhibit
a pattern it fails to name.
_3.5_ Say why reflectivity restates the threat model for prompt injection, then give a
restriction under which it fails.
_3.6_ (Harder.) Argue that a model prompted about its own probe makes self-encoding
real and a passive activation space does not; say which a probing experiment deploys
over.
_3.7_ Prove {lean}`c3_lawvere_point` from {lean}`lawvere` and say what extra
information it exposes.
_3.8_ Instantiate {lean}`c3_cch_master` at `Y = Bool` with the flip and the diagonal,
concluding the hallucination trilemma is the `UC` corner.
_3.9_ Exhibit a system for each achievable pair, showing no edge of the triangle is
empty.
_3.10_ Prove the three corners reduce to {lean}`c3_cch_master` and state
`c3_cch_at_most_two`.
_3.11_ For each trilemma name the two horns fixing the flip and the source of
universality, and rank the sources from free to strong.
_3.12_ Say what quantitative question the diagonal cannot answer and why Chapter 5
needs the analytic engine.
_3.13_ (Harder, Lean.) Define `C3_Faithful` and prove a reflective `v` cannot satisfy
it; say which lemma the proof reduces to.
_3.14_ Restate `faithful_iff_boundary_free` in diagonal language and say why
reflectivity removes the escape.
_3.15_ (open) Sketch a single theorem covering both the real-complement and the
connectedness relaxations.
_3.16_ (open) Without symbols, explain why "no total exact self-applicable truth
predicate" is the same statement as the three trilemmata.
_3.17_ Restate {lean}`c3_hallucination_trilemma` with a section, and say why for
auditing the section form is the more honest premise.
_3.18_ Carry out Remark 3.12 in Lean, discharging transparency by `rfl`.
_3.19_ For each trilemma name the premise you would attack in a real deployment and
its engineering cost.
_3.20_ (open) Design an experiment for or against a representation space encoding
patterns over its own states.
_3.21_ Redo the micro-instance on four elements and identify the liar row.
_3.22_ Prove the flip is fixed-point-free and say what the complement's exceptional
point at one half corresponds to.
_3.23_ Sketch a `CCHStructure` witnessing each achievable pair.
_3.24_ Say which property a wrapper refusing self-referential prompts gives up, and
prove in Lean it cannot satisfy completeness there.
_3.25_ Write the Tarski correspondence term by term, and say which hypothesis does the
work "sufficiently expressive language" does.
_3.26_ Say what the topological proof knows about the boundary object that the
diagonal does not, using the ambiguity tube and the reflectivity premise.
_3.27_ (Harder.) Prove one theorem returning both `False` and the witness, and say why
it summarizes all three trilemmata.

# From Logic to Analysis

_4.1_ Prove a two-point discrete space is disconnected and say why the analytic engine
cannot run on `Bool`.
_4.2_ Show the continuous image of a connected space is connected, and relate this to
Lemma 4.15.
_4.3_ Fill in the omitted lines of Proposition 4.6 at the supremum.
_4.4_ State and prove the two-function IVT, deriving Theorem 4.7 as the constant case.
_4.5_ Say which direction of each calibration biconditional is used forward and which
backward, and show one-way calibration does not pin the truth-distance.
_4.6_ Show Theorem 4.17 fails if faithfulness is weakened to `≤ 0`, and locate the
coupled point of your weakened model.
_4.7_ Reprove {lean}`c4_boundary_question_impossible` at an arbitrary threshold and say
why the threshold is a convention.
_4.8_ Rewrite {lean}`c4_discrete_sign_change` to return the least crossing index, and
say why the continuous IVT has no canonical choice.
_4.9_ Prove the truth boundary is closed using only that singletons are closed.
_4.10_ Show an odd field on a connected space with a free involution has two zeros
unless identically zero on an orbit, and say what the second corresponds to.
_4.11_ Prove the approximate-oddness bound and show it is tight.
_4.12_ Use the diagonal with `y ↦ 1 - y` to produce `s a a = 1/2`, identifying which
step replaces the IVT.
_4.13_ Say why the complement's single fixed point makes Lawvere yield a contradiction
in the Boolean case and a point in the real case.
_4.14_ Give a system satisfying universality but not connectedness and one satisfying
connectedness but not universality.
_4.15_ (Harder.) Give a hypothesis on a finite question space, weaker than
connectedness, still forcing a boundary question.
_4.16_ (Harder.) If the confidence is continuous but the answer map is not, say which
of Lemmas 4.14, 4.15 and Theorem 4.16 survive.
_4.17_ (open) Conjecture how the tube radius scales with the Lipschitz constant and the
confidence margin.
_4.18_ (open) Say what a system satisfying both the diagonal and antipodal hypotheses
would need.
_4.19_ Prove `Q × Q` connected by the slice argument and state the two-turn coupling
theorem, saying where the second turn entered.
_4.20_ Prove the stochastic dichotomy and say why it alone concludes with confident
error rather than uncertainty.
_4.21_ (Harder.) Design a reporting policy making the exclusive guarantee's silence
visible, and argue the flagging band cannot be empty.

# The Geometry of Attacks

_5.1_ Verify the Gaussian bump's basin is a ball of radius `√(2 ln(M/τ))` and confirm
the three soft predictions.
_5.2_ Exhibit a continuous non-Lipschitz `f` whose guaranteed ball is arbitrarily
small.
_5.3_ Construct an `f` on `[0,1] ∪ [2,3]` with empty boundary, and say why
connectedness is exactly what `no_gap_theorem` needs.
_5.4_ Verify the robustness ball touches the boundary hyperplane at exactly one point
and compute it.
_5.5_ Show a model safe at two inputs and grossly unsafe at their midpoint needs
`L ≥ 2M`, and read this as a no-free-lunch statement for smoothing.
_5.6_ Derive `μ(band) ≥ ε/(2L)` and generalize to `ℝ^n`.
_5.7_ Show the surviving steep region has measure `δ₀` and interpret `(c - s)` as the
defender's shortfall.
_5.8_ Prove the shallow-boundary escape and its converse.
_5.9_ Compute `N^d` and `r^d` for `d = 10` and `30` and identify the critical
dimension for a budget of `10^6`.
_5.10_ Show a nonvanishing derivative gives an isolated boundary, then construct a
degenerate case whose level set contains an interval.
_5.11_ Prove gradient ascent halts only at critical points and that the gradient step
maximizes immediate gain.
_5.12_ Trace the gradient chain on an affine surface and reconcile it with the corner
example.
_5.13_ For `δ = 0.2`, say for which margins transfer is guaranteed and construct a
failure below `δ`.
_5.14_ Compare `1/p` for `p = 10^-6` with a gradient attack's step count and say why
gradients dominate when the basin is small.
_5.15_ Assemble the master asymmetry and say which quantity's independence from `d` is
its source.
_5.16_ (Harder.) Show that at `K*` the band has width at least `G·δ`, and argue no `K`
drives both cone measure and band volume to zero when `G > L`.
_5.17_ (open) Propose a common currency for both budgets and say whether the asymmetry
survives the change of units.
_5.18_ (open) Say what plays the role of `L`, the ball, and the coarea band in a
discrete token space, and which conclusions survive.
_5.19_ Contrast the Markov upper bound with the coarea lower bound on the Gaussian
annulus, and say why the gradient attack ignores the former.
_5.20_ Show a defense with `n` slots facing `n+1` attacks leaves one uncorrected, prove
the discrete crossing lemma, and say why it and the diagonal are two proofs of one
fact.

# Approximate Bridges

_6.1_ Write the contrapositive of each clause of Definition 6.1 and confirm
Proposition 6.2, noting where linearity is used.
_6.2_ Verify the `ε = 0` clauses are the forward implications of strict calibration and
say which direction the IVT never uses.
_6.3_ Say which endpoint of `[-ε, 0)` is attainable, which hypothesis supplies each,
and why swapping the strictness breaks Theorem 6.9.
_6.4_ With `c = 0.5` and `ε = 0.2`, compute the guaranteed margin and the transition
band, and say what a deployment must monitor.
_6.5_ Prove the tightening principle from {lean}`c6_tightening` and show the margin
bound is attained.
_6.6_ Construct a scenario improving calibration at fixed faithfulness and identify
where Remark 6.13 says it must stall.
_6.7_ Prove Proposition 6.15 and strengthen it to the closed band.
_6.8_ Say which hypothesis of Theorem 6.16 gives which side of the bound, and
re-elaborate {lean}`c6_band` with the roles exchanged.
_6.9_ Re-elaborate {lean}`c6_band` with a separate confidence margin, obtaining the
integer form of Theorem 6.21.
_6.10_ Rescale confidence by `100` and confirm `γ` scales while `ε` does not; say what
this means for reporting a single `ε`.
_6.11_ Prove Theorem 6.24 as an instantiation of Chapter 1's engine, identifying the
target fed to universality.
_6.12_ Trace the triangle inequality to see which legs contribute the coefficient two,
and redo the count for a `K`-Lipschitz controller.

# What It Means for AI Safety

_7.1_ Explain via {lean}`lawvere` and {lean}`bool_not_fpf` why adding `abstain`
converts the diagonal into a consistent value, and identify it.
_7.2_ For `Cerr = 1000 · Cref`, find the abstention rate at which the two corner costs
are equal, and redo for `Cerr = 2 · Cref`.
_7.3_ Prove the defense analogue of Proposition 7.8 and say why it makes decoupling
attractive to one team and dangerous to another.
_7.4_ If `ρ` rises from `0.002` to `0.02` at fixed `ε`, give the factor change and
design a monitor that would have caught it.
_7.5_ (Design.) Specify a three-region blend for clinical decision support and state
the quantity you must measure before placing the boundaries.
_7.6_ (Design.) Repeat for platform-scale moderation, justifying the smaller reject
region and identifying which consumer forces calibration.
_7.7_ Say why a discontinuous blocklist escapes the Defense Trilemma, what it pays, and
whether it is abstention in disguise.
_7.8_ (open) Describe a deployment where decoupling is correct, and state the condition
on downstream consumers making it safe.
_7.9_ Construct two traffic distributions whose confident-error rates differ by a
hundredfold for one model, and say why no benchmark decides between them.
_7.10_ For a nonzero linear probe, write the distance to the boundary explicitly and
say why the histogram is cheap at scale.
_7.11_ (Harder.) Sketch how hitting time bounds an attacker's steps and why lowering
the Lipschitz constant raises that cost.
_7.12_ (open) Name the premise you find least defensible in your application and say
what evidence would settle it.
_7.13_ (open) Propose a domain where the cost models fail and identify the assumption
it violates.

# J-Space

_8.1_ Prove that post-composing a decoder is also a no-escape result and say what it
models.
_8.2_ Instantiate {lean}`jspace_factoring` at `J := Unit` and say why the most
degenerate probe is still refuted.
_8.3_ Show two queries realizing the diagonal pattern are both coupled and nothing
selects one.
_8.4_ Prove {lean}`c8_steering_no_escape` by absorbing `steer` into the encoder, and
conclude steering is a choice of encoder.
_8.5_ Explain how {lean}`bool_not_fpf` drives both the liar and the discrete failure,
and where the real complement enters instead.
_8.6_ Add a sparsity budget to {lean}`c8_Coord` and show the theorem still applies;
say what this means for sparsity as a safety measure.
_8.7_ Give a score on J-space failing one hypothesis of Theorem 8.17 and say what
breaking it costs.
_8.8_ Say why convexity permits a straight segment, and why a finite set of observed
activations does not.
_8.9_ If the transport map were curved, say which engine applies unchanged.
_8.10_ Write the four-stage pipeline theorem and state the general principle your proof
illustrates.
_8.11_ Give the sense in which {lean}`c8_jlens_impossible` and
{lean}`no_reflective_verdict` are one theorem, and why a `rfl` proof is the honest
signal.
_8.12_ (Design.) Argue whether a target coupled-query rate is reachable by
slack-removal alone, and what deployment information you would need.
_8.13_ (open) Speculate on a representation connected but not self-applicable.
_8.14_ (Harder.) For the affine model, identify the self-applicable map, its
linearization, and the liar activation as the fixed point.
_8.15_ For a three-valued readout with `unknown` fixed, show the diagonal produces no
contradiction and say what the probe gave up.
_8.16_ (open) Design an experiment distinguishing a structural floor, whose residual
set churns, from a resource-limited error, whose residual set is stable.
_8.17_ (open) Construct the most plausible representation meeting one of the three
escape demands, and check which of the others it fails.

# Chain-of-Thought Monitoring

_9.1_ Show that if `T` is `Unit` the monitor is constant and errs on any pair differing
in `harm`.
_9.2_ State and prove the contextual analogue of Theorem 9.7, and say where it breaks.
_9.3_ Prove {lean}`c9_collision_forces_error` in term mode by case-splitting on
`harm q₁`.
_9.4_ Weaken selection to a subset and say what the queries left out mean for a
deployment.
_9.5_ (Design.) With one monitor trained against and one held out, say what each flag
rate licenses and construct a case where the divergence is informative.
_9.6_ Give hypotheses under which traces reachable by bounded paraphrase are connected,
and say why unbounded paraphrase strengthens the argument.
_9.7_ Combine Theorem 9.10 with Chapter 8's factoring for a monitor reading trace and
activations; does reading both help?

# Latent Knowledge

_10.1_ Prove `c10_flipOff` is an involution on reporters.
_10.2_ Given two unchecked questions, construct four pairwise-distinct reporters
agreeing on the checkable set, and state the counting law for `n`.
_10.3_ Formalize a length penalty and give the extra hypothesis pinning the direct
translator; say why the data does not supply it.
_10.4_ Prove the converse of Theorem 10.9, making the dichotomy an equivalence.
_10.5_ Combine {lean}`c10_reporter_factoring` with Chapter 9's trace factoring into one
theorem.
_10.6_ Give hypotheses under which the set of reporters agreeing within `ε` is
connected, and say why that is bad news for a selection procedure.
_10.7_ (Design.) Give the measurement distinguishing a technique that enlarged the
checkable set from one that merely enlarged where the reporters agree.

# Watermarking

_11.1_ For each pair of the three properties, exhibit a detector satisfying that pair
under a stripping paraphrase.
_11.2_ Prove {lean}`c11_detection_trilemma` in term mode using `Bool.noConfusion`.
_11.3_ Generalize Corollary 11.10 to orbits under iterated paraphrase.
_11.4_ Formalize a bounded paraphrase with an edit budget and say what replaces the
stripping hypothesis.
_11.5_ Add a utility function to Definition 11.3 and compare the resulting four-property
theorem to the Defense Trilemma.
_11.6_ Derive the edit-count bound `(s x − τ)/L`, stating the hypotheses on the edit
metric and which fails for very short texts.
_11.7_ (Design.) Choose a corner for a moderation platform, name the population it
fails, and give the measurement of that failure rate.
