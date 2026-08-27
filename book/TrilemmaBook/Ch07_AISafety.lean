import VersoManual
import TrilemmaBook.Ch01_Diagonal

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "What It Means for AI Safety" =>

A theorem that says "you cannot have all three" is not a counsel of despair. It
is a menu. The earlier chapters proved the impossibility and traced it to a single
diagonal. This chapter spends the result. It reads the trilemma as an engineering
design constraint, works through what each way of satisfying it costs, says when
each choice is the right one, and marks the one quantity the theory refuses to
fix. That quantity is where deployment risk actually lives, and being honest about
it is the difference between using an impossibility result and misusing it.

The tone shifts here. The rest of the book is mathematics, and its claims are
checked by the Lean kernel. This chapter is engineering. Its claims are judgments
about costs, domains, and traffic, and they are only as good as the premises you
grant. I will be explicit about which sentences are theorems and which are
recommendations, because the whole point of a machine-checked impossibility result
is that it lets you argue about the right things.

A reader who wants only the practical upshot can take three sentences from this
chapter. First, every deployed system already lives at one of exactly three corners,
and the value of the theorem is that the list of three is complete, so the fourth
option you may be chasing does not exist. Second, which corner is right is decided
by your domain and by one number the theory does not give you, the density of your
real traffic near the model's boundary, so measuring that number is the highest
-leverage thing you can do. Third, the theorems say a bad point exists and are
silent on how often you visit it, so treating an existence result as a frequency
claim, in either direction, is the most common way to misuse this work. The rest of
the chapter is these three sentences with their reasons, their costs, and their
worked cases.

# The constraint, stated as a triangle

Two results from Chapter 3 drive this chapter, and both are one line of Lean:
{lean}`no_reflective_verdict`, read twice.

The Hallucination Trilemma reads a Boolean self-verdict `v p q` as "the model is
confident and correct about query `q`." Three properties make that verdict a total
decider of the model's own correctness. _Faithfulness_ says a confident answer is
a correct one. _Calibration_ says confidence tracks correctness, so the confidence
number means what it says. _Coverage_ says the model actually answers, that it is
sometimes right and sometimes wrong rather than silent. Add reflectivity, the
ability to be queried about its own verdicts, and the diagonal of Chapter 1 forces
a query that is confidently correct exactly when it is not. That is the liar of
{lean}`liar_query`, wearing a safety costume.

The Defense Trilemma reads `v p q` as "the wrapper defense renders prompt `q`
safe," and names three matching properties. _Utility preservation_ says safe
prompts pass through unchanged. _Completeness_ says every output is made safe.
Connectivity of the prompt space, together with continuity of the defense, is the
third leg, and in the diagonal reading it is the arbitrary-text premise that lets
a prompt describe and invert the defense. The forced witness is the injection "be
unsafe exactly if you would be made safe."

**Definition 7.1 (The design triangle).** Fix one of the two readings. The
_design triangle_ has the three named conditions as its vertices. A _corner
policy_ is a choice to give up exactly one vertex and keep the other two. The
trilemma says the interior of the triangle, all three at once, is empty.

The geometry of the phrase "you cannot have all three" is worth stating plainly,
because it is often misread. The theorem does not rank the three conditions, does
not say which to drop, and does not say the surviving two come for free. It says
the point where all three hold does not exist. Everything an engineer does with
the result is a choice of which vertex to release and how far.

**Remark 7.2.** The two readings share a proof term, which Chapter 3 checks with
`rfl`. For an engineer this means the menu below is written once and applies to
both problems. When I describe the cost of dropping coverage in the hallucination
setting, the same paragraph describes the cost of dropping completeness or utility
in the defense setting, under the translation of Definition 7.1. I will point out
where the analogy strains, because it does strain in one place, and pretending it
does not would be dishonest.

## Why a menu, and not a wall

There is a habit of mind that reads every impossibility theorem as a wall. Halting
is undecidable, so we give up on program analysis. Consistency is unprovable, so we
stop trusting formal systems. This reading is almost always wrong, and it is wrong
here. A wall tells you to stop. A menu tells you to choose. The trilemma is a menu
because it does not forbid useful systems. It forbids one specific idealized system,
the one that is faithful and calibrated and covering at the same time, and it leaves
every system that gives up a little of one condition fully available.

The difference is practical. If the trilemma were a wall, the right response would
be to abandon confident automated answering, and no serious person does that. The
right response is to notice that every deployed system already sits at one of the
three corners, usually without having chosen it on purpose, and to make the choice
deliberate. A model that quietly abstains when unsure has dropped coverage. A model
that answers the hard middle and is sometimes confidently wrong there has relaxed
faithfulness. A model whose confidence scores stopped meaning anything two training
runs ago has weakened calibration and nobody noticed. The theorem does not create
these corners. It names them and proves the list is complete.

Completeness of the list is the part that earns the machine check. A menu with
three items is only useful if there is no fourth. The trilemma's value is not that
each corner is individually available, which is obvious, but that the interior is
empty, which is not. Without the theorem an engineer might spend years chasing the
fourth option, the system that keeps all three, believing the failure to find it is
a failure of cleverness. The theorem says the search terminates with nothing, so
the cleverness should go into choosing and pricing a corner instead. That
redirection of effort is the entire practical payload of an impossibility result.

There is a second reading of "menu" that is worth naming. A menu is something you
choose from repeatedly, not once. A product does not pick a corner at launch and
keep it forever. Traffic shifts, downstream consumers appear, stakes change as the
product is trusted with more, and the right corner moves with them. So the menu is
not a one-time decision but a standing one, revisited whenever the domain changes,
and the review cadence is itself a design choice. A team that picked abstention for a
low-traffic pilot and never revisited the choice when the product went to scale is
running the wrong corner, not because it chose badly, but because it stopped
choosing.

## The diagonal, read as a design fact

The proof from Chapter 1 is worth reading once more with an engineer's eye, because
the mechanism tells you where the corners come from. The diagonal builds a behavior
that disagrees with whatever the system would do on itself. In the safety reading
this behavior is a query about the system's own verdicts, engineered to be
confidently correct exactly when it is not. The system cannot answer it correctly,
because answering correctly would make it incorrect, and answering incorrectly is
the failure. That is {lean}`liar_query`, and every corner is a way of denying the
diagonal one of the things it needs.

The diagonal needs three things. It needs the system to name its own behaviors,
which is reflectivity. It needs the outcome to have no fixed point under the flip,
which is what a two-valued confident verdict guarantees. And it needs the system to
actually produce that outcome, which is coverage. Deny reflectivity and the query
cannot be posed, but you cannot deny reflectivity for prompt injection because
prompts are arbitrary text, and denying it for a representation space is the strong
premise Remark 7.11 discusses. Deny the fixed-point-free flip by adding an
abstention outcome, and the diagonal resolves consistently instead of
contradicting, which is Relaxation I. Deny coverage by refusing to produce an
outcome near the boundary, which is the same move seen from the outside. The three
corners are three ways of removing one leg of the diagonal, and the theorem's
completeness is the statement that there is no fourth leg to remove.

# Three relaxations, three cost models

A corner policy drops one vertex. There are three vertices, so there are three
relaxations. Each has a characteristic cost, a characteristic failure mode, and a
class of domains where it is the right choice. I take them one at a time. For each
I give an informal cost model, meaning a rough accounting of what you pay and in
what currency, not a theorem. The theorems say the corner exists and the interior
does not. The cost models are engineering estimates layered on top.

A word on the status of what follows. The cost models use symbols like `ρ`, `ε`,
`Cerr`, and `Cref`, and they combine them into rough expressions like `ρ · ε` for a
band error rate or `a · u` for an abstention loss. These are not theorems and they
are not precise. They are the simplest accounting that captures the first-order
behavior of each corner, good enough to compare corners and to see which quantity
dominates, and no better. Where a factor is a proven bound I will say so and name the
Lean result. Where it is an estimate I will leave it as an estimate. Confusing the
two is exactly the error this chapter warns against, so I try not to commit it while
describing it. Read the formulas as scaling relations, not as predictions to three
digits.

## Relaxation I: drop coverage, and abstain

The cleanest way to satisfy the trilemma is to let the model decline. Keep
faithfulness and keep calibration, and buy them by refusing to answer where a
confident answer would be a gamble. In the selective-prediction literature this is
abstention with a reject option, and it is the corner policy most safety-critical
deployments already run, sometimes without knowing it is a corner policy.

Why does abstention escape the diagonal, when faithfulness and calibration alone
could not? Because the diagonal needs the outcome type to have no fixed point
under the behavior-flip. For a two-valued verdict the flip is Boolean negation,
and {lean}`bool_not_fpf` says negation fixes nothing, which is exactly why
{lean}`cantor` and {lean}`no_reflective_verdict` bite. Abstention adds a third
outcome that the flip leaves alone. Once the flip has a fixed point, Lawvere's
theorem stops producing a contradiction and starts producing a consistent value,
and that value is the abstention.

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

Read this against {lean}`lawvere`. On a universal system whose outcomes are
`Outcome`, the diagonal behavior `a ↦ c7_flip (f a a)` is named by some index, and
evaluating there gives a fixed point of `c7_flip`. With the two-valued flip that
fixed point could not exist, and the system could not be universal. With the
abstaining flip the fixed point is `abstain`, and the self-referential query
resolves to "I decline." The liar query does not vanish. It becomes a query the
system is allowed to refuse. In the continuum reading of Chapter 4 the same move
is a cut: abstaining on an open region around the boundary deletes it from the
domain and can disconnect the true region from the false one, which is why the
paper calls refusal training connectedness surgery.

**Definition 7.3 (Abstention policy).** An _abstention policy_ replaces the answer
map with a partial one that returns a designated `abstain` outcome on a region `R`
of query space, and answers on the complement. The _abstention rate_ is the
probability that a query drawn from deployment traffic lands in `R`.

**Proposition 7.3a (Abstention preserves the surviving vertices).** _On the
complement of `R`, an abstention policy leaves faithfulness and calibration exactly
as they were. It changes only coverage, by removing `R` from the answered set._

_Proof._ The answer map is unchanged outside `R`, so any query answered outside `R`
receives the same answer and the same confidence it did before, and the faithfulness
and calibration statements, which are conditions on answered queries, hold on the
complement exactly as they held before. Coverage, the condition that the model is
sometimes strictly right and sometimes strictly wrong, is the only vertex the policy
touches, since it can delete the strictly-wrong witnesses by placing `R` over them. ∎

Proposition 7.3a is the formal content of "abstention is the clean corner." It does
not trade a bit of one vertex for a bit of another. It surrenders coverage on a
chosen region and keeps the other two intact and unmodified everywhere else. That is
why an abstention policy is the easiest to reason about and to audit: the only thing
that changed is a region you chose and can inspect.

_Cost model._ You pay in utility, and the currency is refused queries. Let `a` be
the abstention rate and let `u` be the average value of answering a query that
falls in `R`. The direct utility loss is about `a · u`. Two features of this cost
matter. First, `R` should hug the boundary, because that is where confident answers
are least trustworthy, so a well-placed `R` of small measure removes most of the
confident errors while refusing few queries. The geometry of Chapter 5 is what
tells you how small `R` can be for a target error rate, through the concentration
of measure near the boundary (`MoF_Cost_04_Concentration`). Second, refusal is not
free of second-order cost. A system that abstains too often trains its users to
route around it, and a refused query frequently becomes someone else's confident
answer downstream, often a worse one. The honest cost of abstention includes where
the refused query goes.

_When it is right._ Abstention is the correct corner when a confident error is
much more expensive than a refusal. Write `Cerr` for the cost of a confident wrong
answer and `Cref` for the cost of a refusal. Abstention dominates when
`Cerr ≫ Cref`. This is the regime of clinical decision support, legal analysis,
financial control, and any actuation loop where a wrong action is hard to reverse.
In these settings a system that says "I do not know, escalate to a human" on the
hard middle is behaving well, and the utility it gives up is utility it should not
have been claiming.

**Remark 7.4.** Abstention preserves both surviving vertices exactly, which is why
it is the safest corner to reason about. It does not blur the confidence signal
and does not tolerate a class of errors. It removes queries from scope. The failure
mode is not a wrong answer but a gap in coverage, and gaps are auditable in a way
that confident errors are not. If you can afford to refuse, refuse.

_Worked scenario._ A radiology triage assistant answers a yes-or-no question about
whether a scan shows a finding that needs urgent review. Suppose a confident wrong
"no urgent finding" costs, in expectation over its downstream consequences, a
thousand times what a refusal costs, since a refusal simply routes the scan to the
normal radiologist queue. Suppose further that traffic near the model's truth
boundary is one percent of volume, and that abstaining on the whole boundary shell
removes ninety-five percent of the confident errors. Answering everywhere and
accepting the boundary errors costs about `0.01 · 0.95 · 1000 = 9.5` refusal-units
per hundred scans in expected error, against an abstention cost of about `1` per
hundred scans, one refusal per hundred routed to the human queue. Abstention wins
by roughly a factor of nine here, and the factor grows with the cost ratio. The
number that could flip the decision is the boundary density: if only one scan in ten
thousand approaches the boundary, the error cost falls to `0.095` per hundred and
answering everywhere becomes cheaper than the refusals. The design decision is
downstream of a measurement, which is the recurring theme of this chapter.

_The second-order cost, made concrete._ The `a · u` term is the direct loss, but a
refusal is rarely the end of the query's life. A refused clinical question goes to a
human who is now busier, a refused search query goes to a competitor, a refused
agent action gets retried with a reworded prompt. The honest cost of abstention is
`a · u + a · d`, where `d` is the expected damage of what happens to the refused
query next. In the radiology case `d` is small, because the human queue is a good
fallback. In a consumer product where the refused query goes to an ungoverned
alternative, `d` can exceed `u`, and an abstention policy that looks safe in
isolation exports its risk. A team choosing this corner should know where its
refusals land before it congratulates itself on its low error rate.

## Relaxation II: relax faithfulness, and price a confident-error band

The second corner keeps coverage and keeps calibration, and pays by accepting that
a thin band of queries near the boundary will receive confident answers that are
wrong. The model answers everywhere, its confidence still separates the clearly
true from the clearly false, and in exchange it is allowed to be confidently wrong
inside a controlled region around the threshold.

This is the corner that the approximate results of Chapter 6 make precise. Exact
separation is impossible next to a live boundary, but two-sided slack is not. The
verified statement `two_slack_approx_coupling` says a model can be separating with
a truth slack `ε` and a confidence margin `γ`, and `truth_slack_must_be_positive`
says the slack cannot be driven to zero while coverage and the guarantee both hold.
The companion `no_boundary_in_upper_band_two_slack` says that once you accept the
slack, the boundary is excluded from the high-confidence band, which is the whole
value of the trade. You are not tolerating errors everywhere. You are confining
them to a band whose width you chose.

**Definition 7.5 (Confident-error band).** A _confident-error band_ of half-width
`ε` is the set of queries with `|dF| ≤ ε`, where `dF` is the realized truth field.
The policy answers confidently on the whole space and accepts that answers inside
the band may be wrong. The _band mass_ is the probability that deployment traffic
lands in the band.

_Cost model._ You pay in confident errors, and the currency is band mass. The
confident-error rate is about `ρ · ε`, where `ρ` is the local density of traffic
near the boundary and `ε` is the band half-width in units of the truth field. Two
levers set this cost. The first is `ε`, which you control by how aggressively you
require the confidence signal to separate. Shrinking `ε` shrinks the error rate,
and the theory says you cannot shrink it to zero, so there is a floor. The second
is `ρ`, which you do not control at all. It is the boundary density on real
traffic, the one empirical number this chapter keeps returning to. A band of fixed
width `ε` is nearly harmless if traffic almost never approaches the boundary, and
nearly useless if traffic piles up there.

_When it is right._ Relaxing faithfulness is correct in high-throughput settings
where refusing constantly is worse than occasionally erring, and where the per-item
cost of an error is bounded and recoverable. Content ranking, autocomplete,
first-pass triage, and recommendation are examples. A system that abstained on
every boundary query in these settings would abstain constantly and deliver no
value, while a small confident-error band costs little per item and is absorbed by
volume. The band policy also has an operational virtue the abstention policy lacks.
The errors it produces are localized near a known surface, so you can monitor that
surface directly rather than watching the whole input space. That is the
"monitor, don't eliminate" prescription of the defense paper, read for
hallucination.

**Remark 7.6.** The band is not a bug you failed to fix. It is a resource you are
spending on purpose. The danger of this corner is not the band itself but the
temptation to pretend `ε` is zero, to ship a model as if it were exactly faithful
and discover the band the hard way when traffic shifts and `ρ` rises. A team that
runs the band policy honestly writes down its `ε`, monitors its `ρ`, and treats
the product `ρ · ε` as a service-level number, not an embarrassment.

**Proposition 7.6a (The band has a positive floor).** _Under coverage and a
threshold-inclusive guarantee on a connected domain, the truth slack `ε` compatible
with separation cannot be zero. There is a strictly positive infimum of feasible
slack, and pushing the model toward exact faithfulness drives the required slack
down toward that infimum but never to it._

_Discussion._ This is the engineering content of `truth_slack_must_be_positive` and
`two_slack_approx_coupling`, imported here as a fact about the corner rather than
reproved. It has a sharp consequence: the band cannot be closed by better training.
A team that keeps shrinking `ε` will see diminishing returns and then a floor, and
past a point the effort spent shrinking `ε` would be better spent measuring and
managing `ρ`. The floor is not a limit of the current model. It is a property of
the geometry, so no model on that geometry escapes it. ∎

_Worked scenario._ An autocomplete feature suggests the next line of code. A
confident wrong suggestion costs the developer a few seconds to reject, so the
per-item error cost is small and recoverable, which is the high-throughput profile.
Abstaining whenever the model is near its boundary would blank the feature on
exactly the ambiguous cases where a suggestion is most wanted, and a feature that
goes silent when the developer hesitates trains the developer to stop looking. The
band corner fits: answer always, accept a thin ring of confident-but-wrong
suggestions near the boundary, and confine monitoring to that ring. Suppose `ε` is
tuned so the band mass on current traffic is two percent, and the acceptance rate of
in-band suggestions is thirty percent, so about `0.02 · 0.30 = 0.6` percent of
accepted suggestions are confident errors the developer must catch. That is a
service-level number the team can state and defend. The failure it must guard
against is not the band but a silent rise in `ρ` when the language or codebase mix
shifts, which widens the same `ε` into a larger band mass without any code change.

**Remark 7.6b (The band is where monitoring is cheap).** The operational advantage
of this corner deserves emphasis. Because the errors are confined to a
neighborhood of a known surface, the truth boundary, you can spend your monitoring
budget on that surface instead of on the whole input space. This is the
hallucination reading of the defense paper's "monitor, don't eliminate" line. You
cannot afford to audit every answer, but you can afford to audit the small fraction
that fall in the band, and the band is defined by a computable distance to the
boundary, so membership is cheap to test at serving time. The band corner turns an
unbounded auditing problem into a bounded one, which is a reason to prefer it even
when abstention would also work.

## Relaxation III: weaken calibration, and decouple confidence from correctness

The third corner keeps coverage and keeps faithfulness in the weak sense that the
answer is often right, and pays by letting the confidence number stop tracking
correctness. The model answers everywhere and is frequently correct, but the
scalar it reports as confidence no longer means what a calibrated number would
mean. High confidence no longer implies likely correct, and the ordering of
confidences no longer ranks queries by reliability.

This is the corner that looks cheapest and is usually the most expensive. It looks
cheap because top-1 accuracy does not move. A model whose confidence is
decorrelated from correctness can score exactly as well on an accuracy benchmark as
one whose confidence is perfectly calibrated, because accuracy never reads the
confidence number. The cost is invisible to the metric most teams watch.

**Definition 7.7 (Decoupling).** A model is _decoupled_ at level `κ` if the mutual
information between its reported confidence and the correctness of its answer is at
most `κ`. Perfect calibration is high mutual information; full decoupling is `κ = 0`,
a confidence signal that carries no information about correctness.

**Proposition 7.8 (Decoupling is invisible to accuracy).** _Top-1 accuracy is a
function of the answer map alone and does not depend on the confidence field.
Hence two models with identical answer maps and any two confidence fields, one
calibrated and one fully decoupled, have identical accuracy._

Read a model as `M : Q → A × C`, an answer paired with a confidence, and read a
metric that scores answers as any function `acc` of the answer map alone. The
proposition is then a statement about what such a metric can see, and it holds
for every metric of that shape, not merely for top-1 accuracy.

```lean
theorem c7_decoupling_invisible_to_accuracy
    {Q A C S : Type _} (acc : (Q → A) → S) (M₁ M₂ : Q → A × C)
    (h : ∀ q, (M₁ q).1 = (M₂ q).1) :
    acc (fun q => (M₁ q).1) = acc (fun q => (M₂ q).1) := by
  congr 1
  funext q
  exact h q
```

_Proof._ The two answer maps are equal by function extensionality, since they
agree at every query, and `acc` applied to equal arguments gives equal results.
The confidence components never appear. ∎

_Proof._ Accuracy counts queries where the answer is correct, and the answer map
is fixed. The confidence field never enters the count. ∎

Proposition 7.8 is trivial as mathematics and important as engineering. It is the
reason this corner is chosen by accident. A team optimizing accuracy, or a training
objective that rewards being right without pricing the confidence report, drifts
into decoupling for free and cannot see it on the dashboard.

_Cost model._ You pay wherever the confidence number is consumed by something other
than a human reading it once. Every downstream system that thresholds on
confidence, routes on it, triages on it, or gates an action on it is now acting on
noise. Write `V` for the value that a downstream consumer extracts from a
calibrated confidence signal, through better routing or cheaper human review. Full
decoupling destroys that `V` entirely, and partial decoupling degrades it in
proportion to the lost mutual information. The cost is not a rate of wrong answers.
It is the collapse of a signal that other systems were built to trust, and it
lands on those other systems, often out of sight of the model's own team.

_When it is right._ Rarely, and only when nothing downstream reads the confidence.
If the model's confidence is never surfaced, never thresholded, and never consumed
by a router or a triage queue, then decoupling costs nothing, because the signal it
corrupts was not being used. A closed system that always answers, always shows the
answer, and never acts on its own certainty can weaken calibration for free. The
moment any consumer appears downstream, this corner becomes the most dangerous of
the three, because it fails silently and the failure surfaces in a different
component than the one that caused it.

**Remark 7.9.** The three corners differ in where the failure shows up. Abstention
fails in the coverage log, visibly, as refusals. The band fails at a known surface
near the boundary, monitorably, as localized confident errors. Decoupling fails
downstream, invisibly, as degraded decisions in systems that trusted the
confidence number. Prefer failures you can see. This is the single most useful
heuristic in the chapter, and it orders the corners for a default: abstain if you
can afford it, band if you cannot, and decouple only if you have proven nothing
reads the confidence.

_Worked scenario, and why it is subtle._ A question-answering assistant reports a
confidence with every answer, and the confidence is shown to the user as a colored
badge. Nothing automated reads it. The team, chasing accuracy on a benchmark,
switches to a training objective that improves top-1 accuracy by two points.
Proposition 7.8 guarantees this move cannot hurt accuracy no matter what it does to
the confidence, and in fact the new objective decorrelates confidence from
correctness, because it never had a reason to preserve the correlation. Accuracy is
up, the launch looks like a win, and the confidence badge is now decorative. If the
badge really is only decorative, this is fine, and the decoupling corner was the
right free lunch. The subtlety is that a later team, seeing a confidence field
already there, wires it into an auto-approval path for an agent. They inherit a
signal that looks like confidence, is typed like confidence, and carries no
information about correctness, and nothing in the code says so. The failure is now
downstream and invisible, and it was seeded two launches earlier by a change that
improved the dashboard. This is the characteristic life cycle of the decoupling
corner: chosen for free, safe until a consumer appears, dangerous the moment one
does.

**Remark 7.9a (Decoupling cannot be detected by the producer alone).** _Whether
weakening calibration is safe depends on the set of downstream consumers of the
confidence signal, which is not a property of the model. Hence the model's own team,
looking only at the model, cannot determine whether it has entered the dangerous
regime of this corner._


_Proof._ Safety of decoupling is the statement that no consumer reads the confidence
in a way that degrades under decoupling. The consumers live outside the model. A
purely model-internal audit has no access to them, so it cannot decide the
statement. ∎

Proposition 7.9a is the reason decoupling is an organizational hazard as much as a
technical one. The information needed to judge it is split between the team that
produces the confidence and the teams that consume it, and neither half can decide
the question alone. The mitigation is a contract: if a system publishes a
confidence number, it commits to a calibration property, and any consumer may rely
on it. That contract is what turns a shared signal from a liability into an asset.

## The three corners side by side

It helps to hold the three corners against each other on the axes that decide a
design. Each drops one condition, pays in one currency, fails in one place, and
suits one kind of domain.

Dropping coverage keeps faithfulness and calibration, pays in refused queries plus
the fate of those queries, fails visibly in the coverage log, and suits high-stakes
domains where a confident error is far worse than a refusal. Relaxing faithfulness
keeps coverage and calibration, pays in a confined confident-error rate `ρ · ε`,
fails monitorably at the boundary surface, and suits high-throughput domains with
bounded recoverable per-item errors. Weakening calibration keeps coverage and the
weak sense of faithfulness, pays wherever the confidence is consumed, fails
invisibly and downstream, and suits only closed systems whose confidence nothing
reads.

Two structural facts cut across the comparison. First, the currencies are not
interchangeable. A refusal is not a small error and an error is not a small refusal.
They land on different parties, surface in different logs, and are governed by
different costs, so a design that treats them as fungible will misprice the corner.
Second, the failure locations order the corners by how much organizational trust
they demand. Abstention demands the least, because its failures are in your own
logs. The band demands more, because you must actually run the boundary monitor.
Decoupling demands the most, because its safety is a claim about systems you may not
control, which Proposition 7.9a says you cannot verify from inside the model. When
in doubt, prefer the corner whose failures you can see without anyone else's
cooperation.

**Remark 7.10a (There is no dominant corner).** No corner dominates the others
across all domains, which is why the trilemma is a menu and not a recommendation.
If one corner were always best, the theorem would effectively be a wall pointing at
that corner. The domain analysis of the next section exists precisely because the
right corner changes with the domain, and a shop that runs the same corner for every
product has either a very uniform product line or an unexamined default.

## The corners are not exclusive

Real systems blend the corners, and the blend is often better than any pure corner.
A deployment can abstain on the innermost band, answer with a priced confident-error
band on the next ring out, and be calibrated in the confident interior. This is a
three-region policy: a reject region `R`, a band region `B`, and a trusted region.
The trilemma does not forbid the blend. It forbids the point where all three
conditions hold at once, and the blend never claims that point. It claims coverage
outside `R`, faithfulness outside `B`, and calibration in the interior, three
weaker conditions on three different regions.

**Proposition 7.10 (Blends satisfy the trilemma by partition).** _If the query
space is partitioned into a region where coverage is dropped, a region where
faithfulness is relaxed, and a region where calibration is enforced, then no single
region carries all three conditions, and the impossibility of Definition 7.1 is not
contradicted on any region._

Carry the three conditions as predicates `A`, `B`, `C` on queries and the three
regions as predicates `R₀`, `R₁`, `R₂` covering the query space. The partition
design is the hypothesis that each region drops one condition, and the
conclusion is that no query carries all three.

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

_Proof._ Every query lies in some region by coverage, and that region's
hypothesis contradicts the corresponding conjunct. ∎

The theorem needs no property of the three conditions at all, which is what
makes it a statement about blending rather than about hallucination. Any three
requirements dropped region by region are consistent in exactly this way, and
the impossibility is never contradicted because it never applies to a region.

_Proof sketch._ The trilemma is a statement about a region on which all three hold.
By construction no region of the partition is such a region. There is nothing to
contradict. ∎

The value of Proposition 7.10 is that it licenses the standard engineering
practice of tiered confidence without any tension with the theorem. The design
question is not whether to blend but where to place the region boundaries, and that
placement is governed by the same empirical number as everything else, the density
of traffic near the truth boundary.

The blend also clarifies a confusion that surrounds impossibility results. A
practitioner will object that real systems clearly do abstain sometimes, answer
sometimes, and report useful confidence, so the trilemma must be violated in
practice. It is not. The system abstains in one region, answers with a priced band
in another, and is calibrated in a third, and no single region carries all three
conditions. The appearance of having all three is an artifact of looking at the
whole system at once and not noticing that the three properties hold on three
different sets of queries. The theorem is about a region where all three hold
together, and the blend is precisely the design that never creates such a region.
Seeing this dissolves the apparent contradiction between the theorem and every
working product, and it locates the real design work in the placement of the region
boundaries rather than in an imagined escape from the theorem.

**Remark 7.10b (Region boundaries are themselves boundaries).** Placing the reject
region and the band introduces new decision surfaces, the edges of `R` and `B`, and
those edges are decision boundaries with their own coupled points under the same
theorem. This is not a regress that undoes the design. The edges of `R` and `B` are
chosen by you, in the truth-field coordinate, so you can place them where behavior
is benign, which is the "make the boundary shallow" prescription applied to the
policy's own thresholds. The lesson is that a tiered policy does not remove
boundaries; it replaces one semantic boundary you do not control with policy
boundaries you do, and the whole art is putting the latter where crossing them costs
little.

# The same menu for prompt-injection defense

Under Definition 7.1 the defense reading inherits the three corners, with the
vertices renamed. Dropping coverage becomes dropping utility preservation. Relaxing
faithfulness becomes accepting a residual attack surface. Weakening calibration
becomes reporting a safety score that no longer tracks actual safety. The
translation is exact for the first two corners and instructive where it strains for
the third.

## Corner I for defense: the abstaining wrapper

A defense that refuses to pass a class of prompts, rather than rewriting them into
safe equivalents, is the abstention corner. It gives up utility preservation, since
some safe prompts get blocked along with the unsafe ones, and in exchange it can be
complete on what it does pass. This is the "reinforced concrete wall with a strict
bouncer" prescription of the defense paper, and it is the reason discontinuous
defenses escape the theorem. A hard blocklist is not a continuous utility-preserving
wrapper, so the impossibility that assumes continuity and utility preservation
simply does not apply to it. The cost is the same as abstention above, paid in
blocked legitimate prompts, and the second-order cost is the same too, users
routing around a bouncer that blocks too much.

## Corner II for defense: the priced residual surface

A continuous utility-preserving wrapper that accepts it is not complete is the band
corner for defense. The verified `ε`-robust constraint of the defense paper is this
corner made quantitative: the wrapper can push near-boundary prompts below the
safety threshold `τ`, but only so far, `f(D(x)) ≥ τ − L(K+1)δ` within distance `δ`
of the fixed boundary point. The residual surface is the analog of the
confident-error band, and its depth is bounded by the Lipschitz constant `L`. The
engineering levers are the same ones the paper lists: make the boundary shallow, so
that boundary-level behavior is a polite refusal rather than a harmful compliance;
reduce `L`, so the surface is smoother and the persistent region shrinks; and
reduce the effective dimension `d`, because the cost of covering the surface grows
as `N^d`. The GPT-5-Mini example in the paper, whose alignment deviation ceiling
sits at exactly the threshold, is a band policy where the band contains no actual
harm. The manifold exists and is empty of damage.

## Corner III for defense: the misreported safety score

A defense that always claims to have handled the prompt, and reports a safety score
decoupled from whether the prompt was actually made safe, is the decoupling corner.
It is the most dangerous for defense for the same reason it is most dangerous for
hallucination. Any orchestration layer that reads the safety score and decides
whether to run a tool, escalate to review, or auto-approve is now gated on noise.
This is where the analogy is at its sharpest rather than where it strains, because
agentic pipelines consume safety scores constantly, and a decoupled score in a
tool-calling loop is a silent authorization of unsafe actions.

**Remark 7.11 (Where the analogy strains).** The strain is in the premise, not the
menu. The hallucination trilemma in its diagonal form assumes reflectivity, that
every verdict pattern is named by some query. For prompt injection this premise is
realistic, because prompts are arbitrary self-describing text, so the diagonal
applies directly and needs no topology. For a fixed representation space the
reflectivity premise is strong and less physical, and Chapter 4 replaces it with
continuity on a connected domain, a weaker and more defensible hypothesis. So the
menu is shared, but the two problems earn their impossibility differently. Defense
gets it from self-reference, cheaply and robustly. Hallucination gets it either
from the strong reflectivity premise or from the weaker geometric one, and an
honest deployment argument should say which premise it is relying on.

## Cost asymmetry and capacity parity

Two further facts from the defense development change how a corner is priced, and
both favor the attacker. The first is cost asymmetry. Covering the residual surface
by exhaustive enumeration costs on the order of `N^d`, exponential in the effective
dimension `d` of the prompt interface, while an attacker needs to find only one
crossing. This is the verified grid cost result, and its practical reading is that
brute-force defense over a rich interface is hopeless, which is why the defense
paper's prescription is to shrink `d` by constraining the interface rather than to
enumerate. The caveat is real and stated as a limitation: a learning-based defense
that generalizes across the space may beat the grid bound, and whether it can is
Problem 7.28. The exponential cost is proven for enumeration, not for every possible
defense.

The second fact is capacity parity. Under equal resources split between preserving
utility and enforcing safety, the safety side loses capacity to the utility side,
because utility preservation constrains almost the whole space while the unsafe set
is thin. The prescription is architectural separation: a lightweight classifier that
flags, paired with a separate response generator, so that the defense does not pay a
capacity tax to the utility pipeline. For a corner analysis this means the decoupling
danger has a structural cousin. A single model asked to be both useful and safe will,
under pressure, spend its capacity on the more frequent demand, which is utility, and
let the safety signal degrade, which is the decoupling corner arrived at through
resource competition rather than through a training objective. Separating the two
functions is how you keep that from happening by default.

# Reading a domain: which corner fits

The corner you should choose is a function of your domain, and the domain reduces
to three questions. What does a confident error cost relative to a refusal? Does
refusal cost accumulate with volume? And does anything downstream consume the
confidence number? These three questions name three archetypes.

**Definition 7.12 (High-stakes domain).** A domain is _high-stakes_ if the cost of
a confident error greatly exceeds the cost of a refusal, `Cerr ≫ Cref`, and errors
are hard to reverse.

**Definition 7.13 (High-throughput domain).** A domain is _high-throughput_ if
refusal cost accumulates with volume, so that a policy refusing a fixed fraction of
a large stream loses more than it saves, and the per-item error cost is bounded and
recoverable.

**Definition 7.14 (Confidence-consumed-downstream domain).** A domain is
_confidence-consumed-downstream_ if some automated component reads the model's
confidence or safety score and acts on it without a human in the loop.

These are not exclusive, and most real deployments are two of the three at once,
which is what makes design hard. A clinical triage bot feeding an automated
escalation queue is high-stakes and confidence-consumed. A moderation pipeline at
platform scale is high-throughput and confidence-consumed. The three questions
give a default policy, and the intersections tell you where the default is not
enough.

A fourth question refines the first, and it is the one teams most often skip.
Reversibility and time-to-detect together set the true cost of an error, because an
error that is caught and undone within a second is not the same error as one that
acts irreversibly before anyone notices. Formally, the effective error cost is not
`Cerr` alone but `Cerr` weighted by the probability that the error is neither
detected nor reversed in time. A high-stakes domain with fast detection and cheap
reversal can behave, for corner-selection purposes, like a high-throughput one, and
a nominally low-stakes domain with slow detection and irreversible actions can
behave like a high-stakes one. An agent that can spend money or send messages is the
canonical case where low nominal stakes hide high effective stakes, because the
action commits before review. When you read a domain, read its detection and
reversal latency, not only its headline error cost.

**Remark 7.14a (Stakes are a function of the pipeline, not the model).** The same
model is high-stakes in one pipeline and low-stakes in another, because stakes are
set by what the pipeline does with the answer, how fast it acts, and whether it can
undo. This is the same lesson as Proposition 7.17 for boundary density, applied to
cost instead of frequency: the model fixes neither the frequency of boundary queries
nor the cost of getting them wrong. Both are properties of the deployment. A team
that classifies its domain by the model's benchmark behavior rather than by its
pipeline's consequences has classified the wrong object.

**Proposition 7.15 (Default corner by archetype).** _Under the cost models of the
previous sections, the utility-maximizing pure corner is abstention for a
high-stakes domain, the confident-error band for a high-throughput domain, and,
for a confidence-consumed-downstream domain, whichever of the first two preserves
calibration, never the decoupling corner._

_Justification._ For high-stakes, `Cerr ≫ Cref` makes the abstention cost `a · u`
smaller than the band cost `ρ · ε · Cerr` at any tolerable error rate. For
high-throughput, accumulated refusal cost exceeds the bounded per-item error cost,
reversing the inequality. For confidence-consumed, Proposition 7.8 shows decoupling
destroys the downstream value `V` while leaving accuracy untouched, so it is
dominated by either calibration-preserving corner. This is an engineering
argument, not a theorem, and it assumes the cost models are the right accounting. ∎

## Case study: clinical decision support

A model reads a patient summary and proposes a differential diagnosis with a
confidence for each candidate. The domain is high-stakes, since a confident wrong
diagnosis can send a clinician down a harmful path, and a refusal costs only the
clinician's time. It is also confidence-consumed, because an automated system uses
the confidence to decide which cases route to a specialist.

The default is abstention. The model should decline on the hard middle, the region
near its own truth boundary where its confident answers are least trustworthy, and
route those cases to a human. The confident-error band corner is wrong here,
because a bounded per-item error is not bounded when the item is a person. The
decoupling corner is doubly wrong, because the specialist-routing system reads the
confidence, and a decoupled confidence sends the wrong cases to the specialist and
auto-clears the dangerous ones.

The design work is placing the reject region `R`. Too wide and the model refuses
so often the clinicians ignore it, which is the second-order cost of abstention
made real. Too narrow and confident errors leak through. The geometry of Chapter 5
is what sizes `R`: the concentration of traffic near the boundary
(`MoF_Cost_04_Concentration`) tells you how much error you remove per unit of
refusal, and you widen `R` until the marginal error removed no longer justifies the
marginal refusal. The one number you cannot get from theory is how much real
patient traffic sits near the boundary, and that must be measured on representative
cases, not on a benchmark of textbook presentations.

## Case study: platform-scale content moderation

A model scores billions of posts for a policy violation, and a threshold on the
score decides auto-removal, human review, or clearance. The domain is
high-throughput, since even a small refusal fraction on billions of items is an
unmanageable review queue, and it is confidence-consumed, because the threshold is
the whole mechanism.

The default is the confident-error band, tuned tightly, with calibration
preserved because the threshold consumes the score. The model answers on
everything, accepts a thin band of confident misclassifications near the boundary,
and confines those errors to a surface the moderation team monitors directly.
Abstention as a pure corner is wrong at this scale, because a reject region large
enough to matter for safety produces a review queue no team can staff. Decoupling
is wrong because the threshold is exactly a downstream consumer of the confidence,
and a decoupled score makes the threshold meaningless.

The design work is choosing `ε` and watching `ρ`. The band mass `ρ · ε` is the
confident-error rate, and it moves when traffic shifts, for instance when a new
class of borderline content appears and `ρ` rises even though `ε` is unchanged.
The correct operational posture treats `ρ` as a monitored quantity and re-tunes
`ε` when it drifts. A team that fixes `ε` once and forgets `ρ` has shipped a band
policy that silently widens its error rate whenever the traffic distribution
moves toward the boundary.

## Case study: an agentic router consuming a safety score

A tool-using agent asks a safety classifier whether a proposed action is safe, and
runs the tool when the score clears a bar. This is the confidence-consumed
archetype in its purest form, and it is where the third corner does its worst
damage.

Here the danger is not primarily the abstention or band choice, which follow the
high-stakes or high-throughput reading of the underlying action. The danger is
decoupling, because the router is a machine reading the safety score with no human
to notice that the score has stopped meaning anything. Under the defense reading of
Remark 7.11 the reflectivity premise is live, since the agent's own outputs become
its next inputs and can describe and invert the classifier, so the diagonal
applies directly and the residual surface is not a modeling idealization but a real
attack target. The correct posture combines a shallow boundary, so that a
score-boundary action is benign by construction, with architectural separation of
the classifier from the action generator, so that the classifier does not lose
capacity to the utility pipeline. Both are prescriptions the defense paper states,
and both are ways of making the unavoidable coupled point land somewhere harmless.

## Case study: retrieval-grounded question answering

A model answers questions only from a fixed corpus of verified documents, and is
instructed to say "not found" when the corpus does not contain the answer. This
case is worth including because it looks like it escapes the trilemma entirely, and
understanding exactly how it does is instructive.

The escape route is the one named in the truth-boundary paper's discussion: a model
that never answers strictly falsely breaks the coverage premise. If the system truly
only asserts what the corpus supports and abstains otherwise, then it is never
strictly wrong, coverage fails, and the impossibility does not apply. This is
vacuous for a general-purpose assistant, because a general assistant is asked about
everything and cannot restrict itself to a verified corpus. It is meaningful here,
because the retrieval design deliberately shrinks the answer space to grounded
content. So retrieval grounding is a real escape, and it is a form of the
abstention corner: "not found" is the abstain outcome, and the corpus boundary is
the reject region.

The escape is only as good as its premise, and the premise fails in two familiar
ways. First, the model may answer confidently from parametric memory even when the
corpus does not support the claim, which reinstates coverage and with it the
boundary. Second, the truth field that decides "supported by the corpus" is itself
estimated, usually by a retrieval-relevance score, and its agreement with actual
support away from clear cases is an empirical premise exactly like the probe-validity
premise of Chapter 4. So retrieval grounding does not repeal the theorem. It moves
the whole problem to the corpus boundary and to the fidelity of the grounding check,
which is often a better place to have the problem, because a corpus boundary is
auditable and a semantic truth boundary is not. That relocation, and not any
repeal, is what makes retrieval grounding a good design.

# The one empirical unknown

Every cost model in this chapter contains a quantity the theory does not fix. For
abstention it is how much traffic falls in the reject region. For the band it is
`ρ`, the density of traffic near the boundary. For the geometry of Chapter 5 it is
the measure concentrated near the decision surface. These are the same quantity
under different names, and it is the single empirical unknown on which the felt
severity of the trilemma depends.

**Definition 7.16 (Boundary density).** The _boundary density_ of a deployment is
the probability, under the real traffic distribution, that a query lands within a
fixed truth-field distance of the model's truth boundary. It is a property of the
model and the traffic jointly, not of either alone.

The theorems are silent on boundary density, and the earlier chapters are explicit
about that silence. The diagonal argument produces a bad point and says nothing
about how many there are or how often one is queried, a limit stated in Chapter 1.
The topological argument is an existence statement, so nothing about error rates
follows from it, a limit stated in the discussion of the truth-boundary paper. The
theory guarantees the boundary exists and is unavoidable. It says nothing about
whether your users ever go near it.

**Proposition 7.17 (Two deployments, same model, different fate).** _The felt cost
of the trilemma is not determined by the model. Two deployments of an identical
model, differing only in their traffic distribution, can have boundary densities
that differ by orders of magnitude, and hence confident-error rates that differ by
the same factor at fixed band width._

_Proof._ The confident-error rate is about `ρ · ε` with `ε` fixed by the model and
`ρ` fixed by the traffic. Vary the traffic and hold the model fixed, and `ρ`, hence
the rate, varies freely. ∎

**Remark 7.16a (Benign and adversarial boundary density are different numbers).**
For the hallucination reading, boundary density is a property of benign traffic, and
it drifts slowly with the user population. For the defense reading it is set by an
adversary who is actively steering queries toward the boundary, so the relevant
number is not the density benign users produce but the density an attacker can
induce. These can differ enormously. A deployment whose benign boundary density is a
fraction of a percent may face an adversarial boundary density near one, because the
attacker's entire job is to find and hit the coupled point. The hitting-time
geometry of Chapter 5 (`MoF_Cost_03_HittingTime`) is the tool for the adversarial
number, and the histogram protocol below is the tool for the benign one. A safety
case that uses the benign number where the adversarial one is called for has
measured the wrong quantity, and this substitution is a common and serious error in
practice.

Proposition 7.17 is the reason benchmark numbers do not transfer to deployment. A
benchmark is a traffic distribution, usually one enriched for hard cases, so its
boundary density is not your deployment's boundary density. A model that
hallucinates often on a benchmark of adversarial trivia may almost never approach
its boundary on a narrow production workload, and a model that looks clean on an
easy benchmark may sit on its boundary constantly under real users. The theorem is
the same in both. The risk is not.

## How the geometry of Chapter 5 would estimate it

Boundary density is measurable, and Chapter 5 gives the geometry that turns the
measurement into a design number rather than a single observed rate. Three of its
verified quantities matter here. Basin volume (`MoF_Cost_02_BasinVolume`) measures
how much of the input space flows to each outcome, and the boundary density is
governed by how much traffic mass sits in the thin shell between basins.
Concentration of measure near the boundary (`MoF_Cost_04_Concentration`) tells you
how sharply that shell is peaked, which sets how much error a reject region of
given width removes. Hitting time (`MoF_Cost_03_HittingTime`) measures how many
steps a walk needs to reach the boundary, which is the adversarial reading of the
same shell: an attacker's cost to drive a query to a coupled point.

A measurement protocol follows from these. Sample queries from representative
traffic, not from a benchmark. For each, estimate the realized truth field and its
distance to the boundary, using the linear-probe geometry of Chapter 4 when a probe
is available, since a nonzero linear probe has an affine hyperplane boundary and
distance to it is a dot product. Histogram those distances. The mass near zero is
the boundary density, the shape of the histogram near zero is the concentration,
and the dimensional scaling of the shell (`MoF_09_DimensionalScaling`) tells you
how the density will move as you change the interface dimension `d`. This gives you
`ρ`, the concentration that sets your reject region, and a forecast of how both
move under interface changes, which is more than a single measured error rate can
give.

**Remark 7.18.** Measuring boundary density well is the open empirical problem the
whole development points at, and it is genuinely hard for two reasons. Real traffic
is not stationary, so `ρ` drifts, and the truth field is only estimated, usually by
a probe whose agreement with semantic truth away from its fitted samples is itself
an empirical premise rather than a theorem. A deployment that takes the trilemma
seriously invests in measuring `ρ` continuously and in validating the probe that
defines the boundary, and treats both as running instruments rather than one-time
calibrations. Everything else in this chapter is downstream of that number.

## A worked estimation

Suppose you have a linear truth probe validated to agree with ground truth on held
out cases at a rate you find acceptable, and a sample of one hundred thousand
queries drawn from a week of representative traffic. For each query you compute the
signed distance to the probe hyperplane, which by the hyperplane result of Chapter 4
is a normalized dot product, one multiply-accumulate per query, cheap at any scale.
You histogram the absolute distances. Suppose the histogram shows five hundred
queries within the band half-width `ε` you have chosen, so the raw boundary density
estimate is `ρ = 0.005`. The shape near zero matters as much as the count: if the
histogram is flat near zero, traffic is spread across the band and the concentration
is low, so widening the band adds error slowly; if it spikes at zero, traffic piles
on the boundary and small changes in `ε` move the error rate sharply. This is the
concentration quantity `MoF_Cost_04_Concentration` read off an empirical histogram.

From `ρ = 0.005` and an in-band error fraction estimated by sampling and labeling a
few dozen in-band queries, you get a confident-error rate for the band corner, and a
refusal rate for the abstention corner if instead you reject the band. You now have
both corners priced on real traffic, which is the input Proposition 7.15 needs. The
dimensional scaling result `MoF_09_DimensionalScaling` then lets you forecast how
`ρ` moves if you change the prompt interface, for instance by constraining formats
to reduce the effective dimension `d`, which the defense paper recommends for a
different reason. The single measurement feeds every downstream design choice in
this chapter.

A note on sample size, because boundary density is a small number and small numbers
are hard to estimate. If the true density is around `0.005`, a sample of one hundred
thousand queries yields about five hundred in-band observations, enough for a stable
estimate, while a sample of one thousand yields about five, which is noise. The
in-band error fraction is harder still, because it requires labeling in-band queries,
and there are few of them by construction. The practical consequence is that boundary
density measurement is data-hungry precisely where it matters most, near a thin
boundary, so the estimation budget should be concentrated on in-band sampling, for
instance by oversampling queries the probe places near the boundary and reweighting.
A density estimate reported without its sample size and its in-band count is not yet
a measurement you can build a safety case on.

**Remark 7.18a (Drift is the operational reality).** The estimate above is a
snapshot, and the quantity it estimates moves. Traffic distributions shift with the
season, the product surface, and the user population, and each shift can move `ρ`
without any change to the model. A boundary density measured once and trusted for a
year is a latent incident. The correct treatment is a control chart: recompute `ρ`
on a rolling window, alarm when it leaves a band, and re-tune `ε` or the reject
region when it does. This turns the one empirical unknown from a number you guess
once into an instrument you read continuously, which is the only honest way to run
any of the three corners at scale.

**Remark 7.18b (The probe is a premise, not a truth).** Everything above rests on
the probe's boundary being the truth boundary, and that identification is an
empirical premise the theorems never grant. A probe defines a boundary in
representation space; whether that boundary tracks semantic truth away from the
probe's fitted samples is Problem 7.23, and the empirical work in the truth-boundary
paper found probes ranging from near-perfect separation to barely above chance
across five small models, with coupling appearing cleanly only where the separation
premise actually held. So a boundary-density number is only as trustworthy as the
probe that defines the boundary, and reporting `ρ` without reporting the probe's
validation is reporting a measurement without its instrument's calibration.

# What the theorems do and do not claim

An impossibility result is easy to overclaim and easy to dismiss, and both come
from ignoring what it actually says. This section draws the line precisely, because
the whole value of a machine-checked result is that the line is sharp.

**What they claim.** A precisely stated ideal is unreachable. Faithful and
covering and calibrated at once, over a self-referential or connected domain, does
not exist, and neither does utility-preserving and complete at once over a
connected prompt space. The obstruction is structural, a consequence of
self-reference or of the topology of the space, and not a defect of any particular
model or training run. And it tightens as you approach the ideal: the closer you
push toward exact separation, the smaller the slack you are forced to accept, with
`truth_slack_must_be_positive` saying the slack cannot reach zero. Every one of
these claims is checked by the Lean kernel, and the check is the content, since the
mathematics is elementary and the risk was always in a hidden premise, which
formalization removes.

**Remark 7.18c (Structural, not a training defect).** _The obstruction does
not depend on how the model was trained, on its size, or on its architecture. It
depends only on the stated premises: self-reference, or continuity on a connected
domain, together with the three conditions. Hence no amount of training data, scale,
or architectural change removes it while those premises hold._


_Discussion._ This is what "structural" means and why it is a stronger statement
than a statistical inevitability result. A statistical argument says a model trained
under certain conditions will hallucinate at some rate, and a different training
regime might change the rate. The structural argument says that as long as the model
realizes the premises, no training regime reaches the ideal, because the ideal does
not exist. The two kinds of result are complementary. The statistical results cited
in the truth-boundary paper's related work tell you about rates under training. The
structural result tells you the target those rates approach is empty. A team that
hopes to train its way to the ideal is refuted by the structural result; a team that
wants to predict its error rate needs the statistical results and the boundary
density of this chapter. ∎

**What they do not claim.** They do not claim any particular deployed model
hallucinates often. Existence is not frequency. The coupled point exists; whether
your traffic visits it is boundary density, which the theorems do not fix
(Definition 7.16). They do not claim a specific defense is broken in practice. The
residual surface exists; whether it contains actual harm depends on whether the
boundary is shallow, which is an engineering choice, not a theorem. And they do not
claim the ideal target is the deployed model. The theorems are about an idealized
object, a total faithful calibrated verdict, or an exactly separating confidence
field, or a continuous utility-preserving complete wrapper. A deployed model
approximates that object and is not identical to it.

**Remark 7.19 (Existence is not frequency).** _The impossibility theorems are
existential. From "a coupled point exists" one cannot derive any statement of the
form "coupled points are queried with probability at least `p`" for any `p > 0`
without an additional premise about the traffic distribution._


_Proof._ The traffic distribution is a free parameter of the deployment and does
not appear in the hypotheses of the theorems. A distribution supported away from
the boundary assigns the coupled point probability zero while satisfying every
hypothesis. Hence no positive frequency lower bound follows. ∎

**Proposition 7.20 (Idealized target, not deployed model).** _The conditions
faithfulness, calibration, exact separation, and completeness are properties of an
idealized limit. A deployed model that satisfies them only approximately is not the
object the theorems refute, and its behavior is governed by the approximate results
of Chapter 6, not by the exact impossibility alone._

_Discussion._ This is why the approximate bridges matter. The exact theorem says
the ideal is empty. The approximate theorem, `two_slack_approx_coupling` and
`exact_from_approx`, says the neighborhood of the ideal is where deployed models
live and prices the slack they must carry. A critique that says "no real model is
exactly calibrated, so the theorem is vacuous" is answered by the approximate
results, which apply to the inexact models and recover the exact statement as a
limit. ∎

**Proposition 7.20a (The impossibility tightens toward the ideal).** _As a model
is pushed toward exact faithfulness and exact calibration, the guarantee it can
still satisfy tightens rather than loosens: the forced question's margin of
correctness is bounded by the slack, and shrinking the slack shrinks that bound,
with the exact contradiction of Chapter 3 as the `ε = 0` limit._

The verified content is Chapter 6's `c6_tightening` and `c6_margin_bound`, which
say precisely this: the guaranteed interval at the smaller slack sits inside the
one at the larger, and the margin at a forced question is bounded by the slack it
came from.

_Discussion._ This is the engineering meaning of the positive-slack floor of
Proposition 7.6a, restated as a claim about progress. It contradicts a natural
intuition that a better model has more room, and it says the opposite: the room
shrinks. A model far from the ideal has ample slack and feels no pressure from the
theorem, while a model near the ideal has little slack and feels the theorem
acutely. The trilemma is not a distant asymptotic curiosity that only matters in a
limit no one reaches. It matters most exactly for the best systems, which are the
ones close enough to the ideal for the floor to bind. ∎

**Remark 7.21 (The premises are where the argument belongs).** An honest
impossibility result moves the disagreement to the premises, and that is a feature.
For hallucination the premise to argue about is whether faithful-plus-calibrated
-plus-covering is really the right idealization of what you want, and whether your
representation space is really self-referential or really connected. For defense
the premise is whether your wrapper is really continuous and utility-preserving,
since a discontinuous blocklist escapes the theorem by design. These are the right
arguments to be having. The theorem does not settle them. It guarantees that once
you grant the premises, the conclusion follows, so the entire remaining question is
whether the premises hold in your case. That is exactly where a careful engineer
wants the argument to be, and it is what machine-checking the deductions buys you.

# An agenda of open problems

The development leaves a clear set of open problems, some empirical, some
mathematical, some a mix. I list them as an agenda for anyone building on this work.

**Problem 7.22 (Boundary density at scale).** Measure boundary density on real
production traffic for deployed models, across domains, and characterize its drift
over time. This is the number every cost model in this chapter depends on, and it
is essentially unmeasured in the field. A good answer is a methodology and a set of
measurements, not a single number, since Proposition 7.17 says the number is
deployment-specific.

**Problem 7.23 (Probe validity away from fitted samples).** The boundary is defined
by a truth field, usually a linear probe, and the premise that the probe agrees
with semantic truth away from its training samples is empirical, not proven. Give a
method to certify or bound that agreement, so that a measured boundary density can
be trusted as a truth boundary density rather than a probe-artifact density.

**Problem 7.24 (Optimal region placement).** Given a measured boundary density and
a cost model, compute the optimal three-region blend of Proposition 7.10, the
placement of the reject region, the band, and the trusted interior, that minimizes
total cost. This is an optimization problem with the geometry of Chapter 5 as its
constraint set, and it is not yet solved in general.

**Problem 7.25 (Dynamic boundary density under adversaries).** For the defense
reading, boundary density is not fixed by benign traffic but driven by an adversary
who steers queries toward the boundary. Combine the hitting-time geometry
(`MoF_Cost_03_HittingTime`) with an adversary model to predict the boundary density
an attacker can induce, and price the defense against it. The stochastic and
multi-turn results (`stochastic_dichotomy`, `multi_turn_history_dependent`) are the
starting points.

**Problem 7.26 (Calibration under decoupling pressure).** Training objectives that
reward accuracy do not price the confidence report, so they drift toward the
decoupling corner for free (Proposition 7.8). Design a training objective or a
regularizer that penalizes decoupling directly, and quantify the accuracy cost of
maintaining calibration. This is the constructive counterpart to the warning of
Section 3.

**Problem 7.27 (The full symmetry theorem).** The symmetry version of the boundary
result replaces coverage with an antipodal condition and needs a vector Borsuk-Ulam
statement for jointly odd axes, which is verified only in the scalar case and for
nonlinear tangents so far. Completing the full theorem would remove the coverage
premise entirely for symmetric representation spaces, which matters because it would
apply to models that never answer strictly falsely.

**Problem 7.28 (Cost asymmetry beyond the grid).** The exponential defense cost
`N^d` assumes exhaustive grid enumeration, and learning-based defenses that
generalize across the space may sidestep it. Determine whether a continuous
learned defense can beat the grid bound, or prove a matching lower bound that holds
for learned defenses, which would settle whether the cost asymmetry is fundamental
or an artifact of the enumeration model.

**Problem 7.29 (J-space and the two engines at once).** Chapter 8 asks what a
system satisfying both the diagonal hypothesis and the continuum hypothesis would
look like, a self-referential space that is also connected with continuous fields.
Characterize the boundary object such a system produces, and determine whether the
two engines give the same coupled point or two different ones. This is the most
open of the problems and the one that would unify the book's two halves.

# The chapter in one constraint

If you keep one thing from this chapter, keep the constraint and its consequence
together. The constraint is that faithful, calibrated, and covering do not coexist
over a self-referential or connected domain, and neither do utility-preserving and
complete over a connected prompt space. The consequence is that you will give up one
of the three, so give it up on purpose, price what you give up, and place the
sacrifice where it hurts least.

The engineering that follows is not exotic. Choose a corner from the domain: abstain
where a confident error dwarfs a refusal, price a confined error band where refusing
constantly is worse than erring occasionally, and weaken calibration only where you
have proven nothing downstream reads the confidence. Blend the corners across
regions so no region carries all three conditions. Then chase the one number the
theory withholds, the boundary density on your real traffic, because every cost in
the chapter is that number times something you control. Make the boundary shallow so
the unavoidable coupled point is benign, keep the signal you publish calibrated so
the systems that trust it are not betrayed, and monitor the boundary rather than
pretending you eliminated it.

None of this is defeat. A theorem that closes off the impossible ideal is a gift to
an engineer, because it ends a search that would otherwise never end and redirects
the effort to choices that can actually be made well. The trilemma does not tell you
that safe, useful AI is impossible. It tells you exactly which single perfection is
unavailable, and it leaves the whole space of good-enough systems open, which is the
space you were going to build in anyway. The contribution of the machine-checked
development is that the boundary between the impossible ideal and the achievable
neighborhood is now drawn with a precision you can trust, so the argument moves to
the premises, which is where an honest argument belongs.

# Bibliographic notes

The engineering prescription for defense, make the boundary shallow, reduce the
Lipschitz constant, reduce dimension, monitor rather than eliminate, and separate
the defense from the utility pipeline, is from the defense-impossibility paper's
prescription section, and the GPT-5-Mini shallow-boundary example is from its
experiments. The confident-error band and its positive-slack floor are the
approximate coupling results of the truth-boundary paper, verified as
`two_slack_approx_coupling` and `truth_slack_must_be_positive`. The reading of
refusal training as connectedness surgery, and of abstention as a cut that
disconnects the true region from the false one, is from that paper's discussion.
The statistical inevitability of hallucination for calibrated models is a different
mechanism from the one here, and the contrast is drawn in the truth-boundary
paper's extended discussion. The geometry that would estimate boundary density is
the companion attack-geometry development surveyed in Chapter 5.

The organization of the three trilemmata as one proof term, and the master
Utility-Control-Transparency framing with its three impossible corners, is Chapter 3
and the companion `CCHProofs` development. The two-slack approximate coupling and the
strictly positive slack floor are the results of Chapter 6, and the exact statement
they generalize is Chapter 4's coupling theorem. Readers who want the empirical
picture that motivates the boundary-density discussion should read the truth-boundary
paper's experiments, where the coupling appears cleanly in the models whose probes
separate truth well and fails to appear where the separation premise breaks, which is
the empirical shadow of the theory's insistence that its premises do the work.

# Exercises

**Exercise 7.1.** Take {lean}`c7_flip` and the two-valued negation of Chapter 1.
Explain, in terms of {lean}`lawvere` and {lean}`bool_not_fpf`, why adding the
`abstain` outcome converts the diagonal from a contradiction into a consistent
value, and identify that value. State in one sentence what this means for a model
allowed to refuse.

**Exercise 7.2.** For a high-stakes domain with `Cerr = 1000 · Cref`, and a
confident-error band policy with band mass `ρ · ε`, find the abstention rate `a`
at which the abstention cost `a · Cref` equals the band cost `ρ · ε · Cerr`. For a
boundary density `ρ = 0.01` and band half-width giving `ε` such that `ρ · ε = 0.005`,
which corner is cheaper? Redo the comparison for `Cerr = 2 · Cref`.

**Exercise 7.3.** Prove the analog of Proposition 7.8 for defense: a safety
classifier's decoupling of its reported score from actual safety does not change
its top-1 safe-or-unsafe accuracy. Then explain why this makes the decoupling
corner attractive to a team optimizing classifier accuracy, and dangerous to the
router that consumes the score.

**Exercise 7.4.** A deployment measures boundary density `ρ = 0.002` on last
quarter's traffic and ships a band policy with fixed `ε`. This quarter a new class
of borderline queries appears and `ρ` rises to `0.02`. By what factor does the
confident-error rate change, with `ε` held fixed? Design a monitor that would have
caught this before the error rate moved, and state what it measures.

**Exercise 7.5.** (Design.) You are building clinical decision support that feeds
an automated specialist-routing queue. Specify a three-region blend per
Proposition 7.10: define the reject region, the band, and the trusted interior in
terms of truth-field distance, say which of the three trilemma conditions each
region gives up, and state the one empirical quantity you must measure before you
can place the region boundaries.

**Exercise 7.6.** (Design.) Repeat Exercise 7.5 for platform-scale content
moderation. Justify why the reject region is much smaller here than in the clinical
case, in terms of the high-throughput archetype of Definition 7.13, and identify
which downstream consumer forces you to keep calibration.

**Exercise 7.7.** Explain why a discontinuous blocklist escapes the Defense
Trilemma, referring to the continuity and utility-preservation premises. Then
explain what the blocklist pays instead, and match that cost to one of the three
corners of this chapter. Is a blocklist an abstention policy in disguise? Argue
both sides.

**Exercise 7.8.** (Short essay.) The chapter claims decoupling is the most
dangerous corner because it fails invisibly and downstream. Write half a page
arguing the opposite: describe a realistic deployment in which the decoupling
corner is the correct choice, and state precisely the condition on downstream
consumers that makes it safe.

**Exercise 7.9.** Using Proposition 7.17, construct two traffic distributions over
a one-dimensional query line with a truth boundary at the origin, one with high
boundary density and one with near-zero boundary density, such that the same model
has a confident-error rate differing by a factor of a hundred. Explain why no
benchmark can determine which distribution a deployment actually faces.

**Exercise 7.10.** The measurement protocol of Section 6 histograms truth-field
distances on representative traffic. Suppose your truth field is a nonzero linear
probe. Using the hyperplane boundary result of Chapter 4, write the distance from
a query embedding to the boundary as an explicit formula, and explain why this
makes the histogram cheap to compute at deployment scale.

**Exercise 7.11.** (Harder.) The adversarial reading of boundary density
(Problem 7.25) treats an attacker as driving queries toward the boundary. Sketch
how the hitting-time quantity `MoF_Cost_03_HittingTime` bounds the number of steps
an attacker needs, and argue why reducing the Lipschitz constant of the alignment
surface raises that cost. What does this say about the tradeoff between a smooth
boundary and a monitorable one?

**Exercise 7.12.** (Short essay.) Remark 7.21 says an honest impossibility result
moves the disagreement to the premises. Pick either the hallucination or the
defense reading, name the single premise you find least defensible in your own
application, and write half a page on what evidence would make you grant or reject
it. Do not argue about the theorem; argue about the premise.

**Exercise 7.13.** (Open-ended.) Proposition 7.15 gives a default corner per
archetype but assumes the cost models of Section 2 are the right accounting.
Propose a domain where the cost models fail, meaning where the utility-maximizing
corner is not the one the proposition predicts, and identify which assumption of
the cost model your domain violates.

**Exercise 7.14.** (Open-ended, connects to Chapter 8.) Suppose a future system
satisfied both the reflectivity premise of the diagonal and the connectedness
premise of the continuum at once (Problem 7.29). Speculate on whether such a system
would have one boundary object or two, and on what a corner policy would even mean
when both engines force a coupled point. State what you would need to measure to
tell the two boundary objects apart.
