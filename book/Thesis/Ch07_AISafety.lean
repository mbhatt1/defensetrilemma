import VersoManual import Thesis.Ch01_Diagonal

open Verso.Genre Manual open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "What It Means for AI Safety" =>

A theorem saying "you cannot have all three" is a menu, not a counsel of
despair. This chapter spends the result: it reads the trilemma as a design
constraint, works out what each corner costs, says when each is right, and marks
the one quantity the theory refuses to fix. That quantity is where deployment
risk lives.

The tone shifts. The rest of this thesis is mathematics checked by the kernel;
this chapter is engineering, and its claims are judgments about costs, domains,
and traffic. I mark explicitly which sentences are theorems and which are
recommendations.

Three sentences carry the practical upshot. Every deployed system already lives
at one of exactly three corners, and the theorem's value is that the list is
complete, so the fourth option you may be chasing does not exist. Which corner
is right is decided by your domain and by one number the theory does not give
you, the density of real traffic near the boundary.

# The constraint, stated as a triangle

Two results from Chapter 3 drive the chapter, both one line of Lean:
{lean}`no_reflective_verdict`, read twice.

The Hallucination Trilemma reads `v p q` as "the model is confident and correct
about `q`." _Faithfulness_ says a confident answer is correct, _calibration_
that confidence tracks correctness, _coverage_ that the model actually answers.
Add reflectivity and the diagonal forces a query confidently correct exactly
when it is not: {lean}`liar_query` in a safety costume.

The Defense Trilemma reads `v p q` as "the wrapper renders `q` safe," with
_utility preservation_ and _completeness_, and the arbitrary-text premise as the
third leg. The forced witness is the injection "be unsafe exactly if you would
be made safe."

*Definition 7.1 (The design triangle).* The _design triangle_ has the three named
conditions as vertices. A _corner policy_ gives up exactly one vertex. The
trilemma says the interior is empty.

*Remark 7.2.* The two readings share a proof term, checked by `rfl` in Chapter 3, so
the menu below is written once and applies to both problems under the
translation of Definition 7.1.

The corners are three ways of removing one leg of the diagonal, and the
theorem's completeness is the statement that there is no fourth leg to remove.

# Three relaxations, three cost models

Each corner has a characteristic cost, failure mode, and class of domains. The
cost models use symbols like `ρ`, `ε`, `Cerr`, `Cref` and combine them into
expressions like `ρ · ε`. These are not theorems and are not precise.

## Relaxation I: drop coverage, and abstain

Keep faithfulness and calibration, and buy them by refusing where a confident
answer would be a gamble. This is abstention with a reject option, and it is the
corner most safety-critical deployments already run, sometimes without knowing
it.

Why does it escape the diagonal? Because the diagonal needs the outcome type to
have no fixed point under the flip. Abstention adds a third outcome the flip
leaves alone, and once the flip has a fixed point Lawvere's theorem stops
producing a contradiction and starts producing a consistent value.

```lean
inductive Outcome where
  | correct
  | wrong
  | abstain

def c7_flip : Outcome → Outcome
  | .correct => .wrong
  | .wrong   => .correct
  | .abstain => .abstain

theorem c7_flip_fixed : ∃ y : Outcome, c7_flip y = y :=
  ⟨.abstain, rfl⟩
```

Read this against {lean}`lawvere`. On a universal system with these outcomes,
the diagonal behavior is named and evaluating there gives a fixed point of
{lean}`c7_flip`. With the two-valued flip no such point exists and the system
cannot be universal; with the abstaining flip the fixed point is `abstain`, and
the self-referential query resolves to "I decline." The liar does not vanish; it
becomes a query the system may refuse. In the continuum reading this is a cut:
abstaining on an open region around the boundary can disconnect the true region
from the false one, which is why refusal training is connectedness surgery.

*Definition 7.3 (Abstention policy).* An _abstention policy_ returns a designated
`abstain` outcome on a region `R` and answers on the complement. The _abstention
rate_ is the probability that deployment traffic lands in `R`.

*Proposition 7.3a (Abstention preserves the surviving vertices).* _Outside `R`, an
abstention policy leaves faithfulness and calibration exactly as they were,
changing only coverage._

_Proof._ The answer map is unchanged outside `R`, so queries answered there receive
the same answer and confidence, and faithfulness and calibration are conditions
on answered queries. Coverage is the only vertex touched, since `R` can be
placed over the strictly-wrong witnesses. ∎

Not formalized. The argument is bookkeeping over which hypotheses the policy
touches, and the companion libraries model total answer maps only, so there is
no declaration of partial answering for it to cite.

_Cost model._ You pay in refused queries: roughly `a · u` for abstention rate
`a` and average value `u` of answering a query in `R`. Two features matter. `R`
should hug the boundary, because that is where confident answers are least
trustworthy, and the geometry of Chapter 5 tells you how small `R` can be for a
target error rate through concentration near the boundary
(`MoF_Cost_04_Concentration`).

*Remark 7.4.* Abstention preserves both surviving vertices exactly, which is why it
is the safest corner to reason about. It does not blur the confidence signal and
does not tolerate a class of errors; it removes queries from scope. The failure
mode is a gap in coverage, and gaps are auditable in a way confident errors are
not. If you can afford to refuse, refuse.

## Relaxation II: relax faithfulness, and price a band

*Definition 7.5 (Confident-error band).* A _confident-error band_ of half-width `ε`
is the set of queries with `|dF| ≤ ε` for the realized truth field. The policy
answers confidently everywhere and accepts that answers inside the band may be
wrong. The _band mass_ is the probability that traffic lands in it.

_Cost model._ The confident-error rate is about `ρ · ε`, boundary density times
band width, and the cost is that times `Cerr`.

*Remark 7.6.* The band is not a bug you failed to fix but a resource you spend on
purpose. The danger is the temptation to pretend `ε` is zero and discover the
band the hard way when traffic shifts and `ρ` rises. A team running this corner
honestly writes down its `ε`, monitors its `ρ`, and treats both as shipped
parameters.

*Proposition 7.6a (The band has a positive floor).* _Under coverage and a
threshold-inclusive guarantee on a connected domain, the truth slack compatible
with separation cannot be zero. There is a strictly positive infimum of feasible
slack._

_Proof._ This is `truth_slack_must_be_positive` of Chapter 6. ∎

*Remark 7.6b (The band is where monitoring is cheap).* Because the errors are
confined to a neighborhood of a known surface, you can spend the monitoring
budget on that surface rather than the whole input space. This is the
hallucination reading of "monitor, don't eliminate."

## Relaxation III: weaken calibration, and decouple

*Definition 7.7 (Decoupling).* A model is _decoupled_ at level `κ` if the mutual
information between reported confidence and correctness is at most `κ`. Full
decoupling is `κ = 0`: a confidence signal carrying no information about
correctness.

*Proposition 7.8 (Decoupling is invisible to accuracy).* _Top-1 accuracy depends on
the answer map alone, so two models with identical answer maps and any two
confidence fields have identical accuracy._

```lean
theorem c7_decoupling_invisible_to_accuracy
    {Q A C S : Type _} (acc : (Q → A) → S)
    (M₁ M₂ : Q → A × C)
    (h : ∀ q, (M₁ q).1 = (M₂ q).1) :
    acc (fun q => (M₁ q).1) = acc (fun q => (M₂ q).1) := by
  congr 1
  funext q
  exact h q
```

_Proof._ The accuracy functional sees only the first projection. ∎

This is why the corner is attractive to a team optimizing accuracy and dangerous
to whatever consumes the confidence: the metric that would catch the drift is
blind to it by construction.

*Remark 7.9.* The corners differ in where failure shows up. Abstention fails visibly
in the coverage log as refusals. The band fails monitorably at a known surface
as localized confident errors. Decoupling fails invisibly and downstream, as
degraded decisions in systems that trusted the number. Prefer failures you can
see.

*Remark 7.9a (Decoupling cannot be detected by the producer alone).* Whether
weakening calibration is safe depends on the set of downstream consumers, which
is not a property of the model. So the model's own team, looking only at the
model, cannot determine whether it has entered the dangerous regime.

## The corners side by side

*Remark 7.10a (There is no dominant corner).* No corner dominates across all domains,
which is why the trilemma is a menu. If one were always best the theorem would
be a wall pointing at it. The right corner changes with the domain, and a shop
that runs the same corner everywhere is running it in domains where it is wrong.

*Proposition 7.10 (Blends satisfy the trilemma by partition).* _If the query space is
partitioned into a region dropping coverage, one relaxing faithfulness, and one
enforcing calibration, no single region carries all three conditions._

```lean
theorem c7_blend_no_region_has_all_three {Q : Type _}
    (A B C R₀ R₁ R₂ : Q → Prop)
    (hcover : ∀ q, R₀ q ∨ R₁ q ∨ R₂ q)
    (h₀ : ∀ q, R₀ q → ¬ A q)
    (h₁ : ∀ q, R₁ q → ¬ B q)
    (h₂ : ∀ q, R₂ q → ¬ C q) :
    ∀ q, ¬ (A q ∧ B q ∧ C q) := by
  intro q h
  rcases hcover q with hr | hr | hr
  · exact h₀ q hr h.1
  · exact h₁ q hr h.2.1
  · exact h₂ q hr h.2.2
```

_Proof._ Case analysis on which region the query lies in. ∎

*Remark 7.10b (Region boundaries are themselves boundaries).* Placing the reject
region and the band introduces new decision surfaces, and those edges are
decision boundaries with their own coupled points under the same theorem. This
is not a regress that undoes the design: the edges are chosen by you, in the
truth-field coordinate, so you can place them where behavior is benign rather
than where the model's own boundary happens to fall.

# The same menu for defense

The three corners translate. The abstaining wrapper refuses a region of prompts,
giving up completeness there. The priced residual surface accepts a bounded
region of prompts the wrapper does not fully neutralize. The misreported safety
score decouples the published score from actual safety, which is the defense
analogue of decoupling and carries the same invisibility.

*Remark 7.11 (Where the analogy strains).* The strain is in the premise, not the
menu. The diagonal form of the hallucination trilemma assumes reflectivity, and
for prompt injection that premise is realistic because prompts are arbitrary
self-describing text. For a fixed representation space it is strong, and the
topological route of Chapter 4 is the honest one there.

Cost asymmetry and capacity parity, from Chapter 5, say the defender's budget
grows exponentially in effective dimension while the attacker's does not, so for
defense the band corner is usually forced rather than chosen.

# Reading a domain: which corner fits

*Definition 7.12 (High-stakes domain).* `Cerr ≫ Cref`, and errors are hard to
reverse.

*Definition 7.13 (High-throughput domain).* Refusal cost accumulates with volume, so
refusing a fixed fraction of a large stream loses more than it saves, and
per-item error cost is bounded and recoverable.

*Definition 7.14 (Confidence-consumed-downstream domain).* Some automated component
reads the confidence or safety score and acts on it without a human in the loop.

These are not exclusive, and most deployments are two of the three at once.

*Remark 7.14a (Stakes are a function of the pipeline, not the model).* The same model
is high-stakes in one pipeline and low-stakes in another, because stakes are set
by what the pipeline does with the answer, how fast it acts, and whether it can
undo. A team that classifies its domain by benchmark behavior rather than by its
pipeline's consequences has classified the wrong object.

*Proposition 7.15 (Default corner by archetype).* _Under the cost models above, the
utility-maximizing pure corner is abstention for a high-stakes domain, the
confident-error band for a high-throughput domain, and, for a
confidence-consumed-downstream domain, whichever of the first two preserves
calibration, never decoupling._

_Justification._ For high-stakes, `Cerr ≫ Cref` makes `a · u` smaller than `ρ · ε · Cerr`
at any tolerable error rate. For high-throughput the accumulated refusal cost
exceeds the bounded per-item error cost, reversing the inequality. For
confidence-consumed, Proposition 7.8 shows decoupling destroys downstream value
while leaving accuracy untouched, so it is dominated. ∎

Not formalized. This is an engineering argument, not a theorem: it assumes the
cost models of the preceding sections are the right accounting, and no companion
declaration states it.

_Clinical decision support._ High-stakes and confidence-consumed. The default is
abstention: decline on the hard middle and route those cases to a human. The
band is wrong because a bounded per-item error is not bounded when the item is a
person, and decoupling is doubly wrong because the routing system reads the
confidence.

_Platform-scale content moderation._ High-throughput. Refusing a fixed fraction
of a billion-item stream is not viable, so the band is the default, with `ε`
chosen against a measured `ρ` and the residual errors monitored at the boundary
rather than eliminated. The reject region is much smaller than in the clinical
case, and whichever downstream system consumes the score is what forces
calibration to be kept.

_An agentic router consuming a safety score._ Confidence-consumed by
construction. Decoupling is excluded, and the choice is between abstention and
the band on throughput grounds.

_Retrieval-grounded question answering._ Grounding restricts the answer set to
retrieved content, which can break coverage honestly rather than by refusal: if
the system is never strictly wrong within its grounded scope, the coverage
hypothesis fails and the trilemma does not apply. The cost is that the scope is
now the retrieval corpus, and questions outside it are refused.

# The one empirical unknown

*Definition 7.16 (Boundary density).* The _boundary density_ of a deployment is the
probability, under real traffic, that a query lands within a fixed truth-field
distance of the boundary. It is a property of the model and the traffic jointly.

*Proposition 7.17 (Two deployments, same model, different fate).* _Two deployments of
an identical model differing only in traffic distribution can have boundary
densities differing by orders of magnitude, and hence confident-error rates
differing by the same factor at fixed band width._

_Proof._ The confident-error rate is about `ρ · ε` with `ε` fixed by the model and `ρ`
by the traffic; vary the traffic and the rate varies freely. ∎

Not formalized. The step is arithmetic on a product whose two factors this
thesis fixes separately, one by the model and one by the deployment; the
companion libraries state neither factor as a theorem.

*Remark 7.16a (Benign and adversarial boundary density differ).* For hallucination,
boundary density is a property of benign traffic drifting slowly with the user
population. For defense it is set by an adversary steering toward the boundary,
so the relevant number is the density an attacker can induce, not the one benign
users produce. These can differ enormously, and the hitting-time geometry
(`MoF_Cost_03_HittingTime`) is the tool for the adversarial number.

Proposition 7.17 is why benchmark numbers do not transfer. A benchmark is a
traffic distribution, usually enriched for hard cases, so its boundary density
is not yours. A model that hallucinates often on adversarial trivia may almost
never approach its boundary on a narrow production workload. The theorem is the
same in both; the risk is not.

_How Chapter 5's geometry estimates it._ For a nonzero linear probe the boundary
is an affine hyperplane, so the distance from a query embedding to it is an
explicit formula, which makes a histogram of truth-field distances cheap at
deployment scale. Histogram representative traffic, read off the mass within `ε`
of zero, and that is `ρ`.

*Remark 7.18.* Measuring boundary density well is the open empirical problem the whole
development points at, and it is hard for two reasons. Real traffic is not
stationary, so `ρ` drifts. And the truth field is only estimated, usually by a
probe whose agreement with semantic truth away from its fitted samples is an
empirical premise rather than a theorem.

*Remark 7.18a (Drift is the operational reality).* Traffic shifts with the season, the
product surface, and the user population, and each shift moves `ρ` without any
change to the model. A boundary density measured once and trusted for a year is
a latent incident. The correct treatment is a control chart: recompute `ρ` on a
schedule and alarm on the change, not the level.

*Remark 7.18b (The probe is a premise, not a truth).* Everything rests on the probe's
boundary being the truth boundary, and that identification is an empirical
premise the theorems never grant. Whether a probe's boundary tracks semantic
truth away from its fitted samples is Problem 7.23.

# What the theorems do and do not claim

*Remark 7.18c (Structural, not a training defect).* The obstruction does not depend on
how the model was trained, on its size, or on its architecture. It depends only
on the stated premises, so no amount of data, scale, or architectural change
removes it while those premises hold.

*Remark 7.19 (Existence is not frequency).* The theorems are existential. From "a
coupled point exists" one cannot derive "coupled points are queried with
probability at least `p`" for any `p > 0` without an additional premise about
traffic.

*Proposition 7.20 (Idealized target, not deployed model).* _Faithfulness, calibration,
exact separation, and completeness are properties of an idealized limit. A
deployed model satisfying them only approximately is not the object the exact
theorems refute, and its behavior is governed by Chapter 6._

*Proposition 7.20a (The impossibility tightens toward the ideal).* _As a model is
pushed toward exact faithfulness and calibration, the guarantee it can still
satisfy tightens: the forced question's margin is bounded by the slack, with the
exact contradiction as the `ε = 0` limit._

_Proof._ Theorem 6.12. ∎

*Remark 7.21 (The premises are where the argument belongs).* An honest impossibility
result moves the disagreement to the premises, and that is a feature. For
hallucination the premise to argue about is whether
faithful-plus-calibrated-plus-covering is the right idealization of what you
want, and whether your representation space is really self-referential or really
connected. For defense it is whether your prompt space is really unrestricted.

# An agenda of open problems

*Problem 7.22 (Boundary density at scale).* Measure boundary density on real
production traffic across domains and characterize its drift. Every cost model
here depends on it and it is essentially unmeasured. A good answer is a
methodology and a set of measurements, since Proposition 7.17 says the number is
deployment-specific.

*Problem 7.23 (Probe validity away from fitted samples).* Give a method to certify or
bound a probe's agreement with semantic truth off its training samples, so a
measured boundary density can be trusted as a truth boundary density rather than
a probe artifact.

*Problem 7.24 (Optimal region placement).* Given a measured density and a cost model,
compute the optimal three-region blend of Proposition 7.10. This is an
optimization with Chapter 5's geometry as its constraint set, unsolved in
general.

*Problem 7.25 (Dynamic boundary density under adversaries).* Combine the hitting-time
geometry with an adversary model to predict the density an attacker can induce,
and price the defense against it. `stochastic_dichotomy` and
`multi_turn_history_dependent` are the starting points.

*Problem 7.26 (Calibration under decoupling pressure).* Training objectives rewarding
accuracy do not price the confidence report, so they drift toward decoupling for
free. Design a regularizer penalizing decoupling directly and quantify its
accuracy cost.

*Problem 7.27 (The full symmetry theorem).* The symmetry version needs a vector
Borsuk-Ulam statement for jointly odd axes, verified so far only in the scalar
case. Completing it would remove the coverage premise entirely for symmetric
spaces, which matters because it would apply to models that never answer
strictly falsely.

*Problem 7.28 (Cost asymmetry beyond the grid).* The `N^d` defense cost assumes
exhaustive enumeration. Determine whether a learned defense that generalizes can
beat the grid bound, or prove a matching lower bound for learned defenses.

*Problem 7.29 (J-space and the two engines at once).* Characterize the boundary object
of a system satisfying both the diagonal and the continuum hypotheses, and
determine whether the engines give the same coupled point. This is the most open
of the problems.

# The chapter in one constraint

The constraint: faithful, calibrated, and covering do not coexist over a
self-referential or connected domain, and neither do utility-preserving and
complete over a connected prompt space. The consequence: you will give up one of
the three, so give it up on purpose, price what you give up, and place the
sacrifice where it hurts least.

Choose the corner from the domain. Abstain where a confident error dwarfs a
refusal. Price a confined band where refusing constantly is worse than erring
occasionally. Weaken calibration only where you have proven nothing downstream
reads the confidence. Blend across regions so no region carries all three. Then
chase the number the theory withholds, because every cost here is that number
times something you control.

None of this is defeat. A theorem closing off an impossible ideal ends a search
that would otherwise never end. The trilemma does not say safe useful AI is
impossible; it says exactly which single perfection is unavailable, and leaves
the whole space of good-enough systems open.
