import VersoManual
import TrilemmaBook.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
set_option pp.rawOnError true

#doc (Manual) "The Geometry of Attacks" =>

The diagonal gives you one thing and refuses to give you anything else. It gives
you a bad point. It builds, out of pure self-reference, an index the system
cannot correctly name, and from that index it manufactures a contradiction. What
it never tells you is how many such points there are, how large a region around
them behaves badly, how a search would find one, or what an adversary would have
to spend to reach one. Those questions are not failures of the diagonal. They are
simply outside its language. The diagonal speaks about surjections and
fixed-point-free maps; it has no vocabulary for volume, distance, or gradient.

This chapter is about the other half of the theory, the half that does have that
vocabulary. Here the objects are not abstract systems `f : A → A → Y` but real
functions on real spaces: an _alignment deviation_ surface `f : X → ℝ` measuring
how far a behavior sits from acceptable, a threshold `τ` separating safe from
unsafe, and a metric that lets us talk about how far apart two behaviors are. The
tools are analysis and measure theory, not category theory. None of the results
here is a diagonal argument. They are the intermediate value theorem, the
Lipschitz condition, the coarea inequality in disguise, concentration of measure,
and the pigeonhole principle applied to grids. Together they answer the
quantitative questions the diagonal left on the table.

The material follows the companion `ManifoldProofs` development, a machine-checked
library of roughly four hundred results built on Mathlib. Because that library is
analytic and measure-theoretic, and because the book's own Lean package carries no
Mathlib, this chapter states everything in prose. Each theorem is stated
carefully, proved or sketched with enough rigor to be checked by hand, and tagged
with the exact name of the corresponding `MoF_*` result so you can read the formal
statement yourself. Treat the citations as the ground truth. Where the prose here
simplifies, the Lean does not.

One organizing idea runs through the whole chapter, and it is worth stating before
any theorem. _Existence is qualitative; cost is quantitative._ The impossibility
theorems of the earlier chapters say the boundary is there and cannot be removed.
The theorems here say how the boundary is shaped, how much room the unsafe region
occupies, and how the price of attack and defense scales. A deployment is not
decided by whether a bad point exists, since one always does. It is decided by how
expensive it is to live next to that point. The geometry is where the expense
lives.

# From the diagonal to the boundary

Fix a space `X` of behaviors. Think of `X` as a set of prompts, a set of
activation vectors, an embedding space, or in the cleanest case a Euclidean space
`ℝ^n`. Fix a continuous function `f : X → ℝ`, the alignment deviation, with the
reading that `f x` is large when the behavior `x` is far from acceptable and small
when `x` is aligned. Fix a real number `τ`, the safety threshold. This triple
`(X, f, τ)` is the entire setting. Everything in the chapter is a statement about
it.

**Definition 5.1 (Regions).** The _safe region_ is `{x | f x < τ}`, the _unsafe
region_ or _vulnerability basin_ is `{x | f x > τ}`, and the _boundary_ is the
level set `{x | f x = τ}`. The _failure manifold_ is the closed superlevel set
`{x | f x ≥ τ}`. These are `SafeRegion`, `UnsafeRegion`, `Boundary`, and
`FailureManifold` in `MoF_01_Foundations`.

Three facts about this partition are immediate and hold with no hypothesis beyond
continuity of `f`. Every point lies in exactly one of the three regions
(`space_partition`). The safe and unsafe regions are disjoint
(`safe_unsafe_disjoint`). The failure manifold is the disjoint union of the
boundary and the unsafe region (`failureManifold_eq_union`). None of this is deep.
It is the setup, the analytic analogue of fixing a system `f : A → A → Y` in
Chapter 1.

The bridge from the diagonal chapters to this one is the observation that a
continuous alignment surface on a connected space carries a boundary object of its
own, and that object plays the role the liar index `a₀` played there. In Chapter 1
the boundary question was the index on which a boolean verdict flipped. Here it is
a point where `f` equals `τ` exactly, a place that is neither safe nor unsafe but
sits on the knife edge between them. The diagonal produced its witness by
self-reference. The boundary here is produced by connectedness and the
intermediate value theorem, which is a completely different engine. What is
striking, and what makes this chapter a continuation rather than a new subject, is
that the two engines deliver the same kind of object: an unavoidable point of
failure. The difference is that the analytic engine delivers it with metric
content the diagonal never had.

**Remark 5.2.** It helps to keep one picture in mind throughout. Imagine `f` as a
landscape, a height function over the behavior space `X`. The safe region is the
lowland below sea level `τ`, the unsafe region is the land above it, and the
boundary is the coastline. The questions of this chapter are geographic. How much
coastline is there? How steep are the cliffs? If you drop a random point on the
map, how likely is it to land near the coast? If you start inland and walk toward
the sea, how many steps does it take? The impossibility theorems say the coastline
exists. The geometry says how to sail it.

# Decision basins and their structure

The first substantial results describe the vulnerability basin as a set. They are
soft, in the sense that they use only continuity and the order structure of `ℝ`,
but they are the foundation for everything measure-theoretic that follows.

**Theorem 5.3 (Basin openness).** _If `f` is continuous, the vulnerability basin
`{x | f x > τ}` is open, and the safe region `{x | f x < τ}` is open. The boundary
`{x | f x = τ}` and the sublevel set `{x | f x ≤ τ}` are closed._

_Proof._ The basin is the preimage `f⁻¹((τ, ∞))` of an open ray under a continuous
map, hence open. The safe region is `f⁻¹((-∞, τ))`, again a preimage of an open
ray. The boundary is `f⁻¹({τ})`, the preimage of a closed singleton, hence closed;
equivalently it is where the two conditions `f x ≤ τ` and `f x ≥ τ` both hold, an
intersection of two closed sets. ∎

This is `basin_isOpen` and `sublevel_isClosed` in `MoF_02_BasinStructure`, with
the safe and boundary versions as `safeRegion_isOpen`, `unsafeRegion_isOpen`, and
`boundary_isClosed` in `MoF_01_Foundations`. The openness of the basin has an
immediate reading that matters for safety. If a behavior is unsafe, so is every
behavior sufficiently close to it. Unsafety is not a razor-thin condition that a
tiny perturbation removes; it comes with room around it.

**Theorem 5.4 (Every unsafe point owns a ball).** _If `f` is continuous and
`f p > τ`, then there is a radius `r > 0` with the open ball `B(p, r)` contained in
the basin._

_Proof._ The basin is open and contains `p`, and in a metric space openness means
exactly that every point has a ball around it inside the set. ∎

This is `basin_contains_ball`. The qualitative version, that _some_ positive radius
exists, is all continuity buys you. The quantitative version, that the radius is at
least an explicit function of how far `f p` exceeds `τ`, needs a Lipschitz
hypothesis and is the subject of the next section. Hold the two apart in your mind.
Continuity gives you a ball of unknown size; Lipschitz continuity gives you a ball
of known size.

**Theorem 5.5 (Basins have positive measure).** _Let `μ` be any measure on `X` for
which nonempty open sets have positive measure (an `IsOpenPosMeasure`, which
includes Lebesgue measure on `ℝ^n`). If `f` is continuous and there is a point `p`
with `f p > τ`, then `μ({x | f x > τ}) > 0`._

_Proof._ The basin is open by Theorem 5.3 and nonempty by hypothesis. An open
nonempty set has positive measure by assumption on `μ`. ∎

This is `basin_measure_pos` (in `MoF_02`) and, in the form stated directly for
continuous `f`, `basin_measure_ge_ball_pos` in `MoF_Cost_02_BasinVolume`. The
result is small but it is the hinge of the whole cost story. A single unsafe point
is a measure-zero event and might be dismissed as negligible. Positive measure
cannot be dismissed. It says a positive fraction of the space is unsafe, so a
random draw has a positive chance of landing there, and no finite set of safe
examples can certify the region away. Existence upgrades to abundance the moment
you add continuity and a measure.

**Theorem 5.6 (Monotonicity in the threshold).** _If `τ₁ ≤ τ₂` then
`{x | f x > τ₂} ⊆ {x | f x > τ₁}`, and consequently
`μ({x | f x > τ₂}) ≤ μ({x | f x > τ₁})`. If `τ` sits strictly above the supremum of
`f`, the basin is empty; if `τ` sits strictly below the infimum, the basin is the
whole space._

_Proof._ Raising the threshold can only remove points from the superlevel set, so
the inclusion holds, and measure is monotone under inclusion. The extreme cases are
the observation that `f x > τ` is unsatisfiable when `τ` exceeds every value of `f`
and universally satisfied when `τ` is below every value. ∎

These are `basin_measure_monotone_threshold`, `basin_empty_above_sup`, and
`basin_full_below_inf` in `MoF_Adv_10_MeasureBounds`. The lesson for a defender is
unwelcome. You can shrink the basin by raising the threshold, meaning by declaring
more behaviors unsafe and refusing them, but the basin shrinks continuously and
never vanishes until you have refused essentially everything the model can do. A
threshold high enough to empty the basin is a threshold high enough to empty the
product.

## Connectedness and components

Is the basin one region or many? The answer depends on the shape of `f`, and the
distinction matters because an attacker who finds one component has found only that
component, while a defender who patches one has patched only that one.

**Theorem 5.7 (Components are open and countable).** _On a space where every point
has a connected neighborhood (a locally connected space, in particular `ℝ^n`), each
connected component of the basin `{x | f x > τ}` is open. If in addition the space
is second countable, there are at most countably many components._

_Proof sketch._ Components of an open set in a locally connected space are open,
since around any point of the basin sits a connected neighborhood inside the basin,
and that neighborhood lies wholly in the point's component. A collection of
disjoint nonempty open sets in a second countable space is countable, because each
must contain a distinct element of a countable base. ∎

This is `basin_connected_components_open` and `basin_components_countable` in
`MoF_Adv_01_BasinConnectedness`. When the domain is convex and `f` is, say, quasi
concave, the basin is a single connected region (`basin_connected_of_convex_domain`
records a clean sufficient condition). But nothing forces this. The file also
carries `superlevel_disconnected_example`, an explicit `f` whose basin splits into
separate pieces. Real models are the second kind. Their vulnerability basins
fragment into many components scattered through behavior space, which is exactly why
red-teaming that finds one jailbreak family says little about the others.

## A worked example: the Gaussian bump

Let `X = ℝ^n` and take `f(x) = M · exp(-‖x‖² / 2)` for a peak height `M > 0`. This
is a smooth radially symmetric bump centered at the origin, a caricature of a model
with a single localized failure mode. Fix a threshold `τ` with `0 < τ < M`.

The basin `{x | f x > τ}` is `{x | ‖x‖² < 2 ln(M/τ)}`, an open Euclidean ball of
radius `R = √(2 ln(M/τ))` centered at the origin. Every prediction of the soft
theory checks out on this example. The basin is open, as any ball is. It is
nonempty precisely because `τ < M`, so the origin itself is unsafe. It has positive
Lebesgue measure, namely the volume of a ball of radius `R`. It is connected, being
a ball. Raise `τ` toward `M` and `R` shrinks to zero continuously; the basin never
disappears until `τ` reaches `M`, matching Theorem 5.6.

The example also previews the curse of dimension. The volume of a Euclidean ball of
radius `R` in `ℝ^n` is `R^n · π^(n/2) / Γ(n/2 + 1)`. For fixed `R`, as `n` grows,
this volume first grows and then collapses toward zero, and its ratio to the volume
of the surrounding cube of side `2R` goes to zero fast. The basin, though it has
positive measure, occupies a vanishing fraction of the ambient space in high
dimension. A random draw almost never lands in it. This is the good news for
defense and the bad news too, and untangling which is the business of the cost
theory later in the chapter.

# The threshold-crossing theorem

Now the central structural result of the qualitative geometry. It says the boundary
cannot be dodged. If a path starts safe and ends unsafe, it crosses the boundary
somewhere in between. There is no teleporting from lowland to highland without
touching sea level.

**Theorem 5.8 (Threshold crossing, one dimension).** _Let `f : ℝ → ℝ` be
continuous, let `a ≤ b`, and suppose `f a < τ < f b`. Then there is a point
`c ∈ [a, b]` with `f c = τ`._

_Proof._ This is the intermediate value theorem. The interval `[a, b]` is connected,
`f` is continuous on it, and `τ` lies strictly between the values `f a` and `f b`,
so `τ` is attained. Formally one applies the two-function form of the IVT to `f`
and the constant `τ` on the preconnected set `[a, b]`. ∎

This is `path_crosses_threshold` in `MoF_03_ThresholdCrossing`. It is elementary,
and its elementariness is the point. The unavoidability of the boundary is not a
subtle theorem; it is the IVT wearing a safety costume. What takes work is stating
it in the generality the theory needs, which is arbitrary behavior spaces rather
than the real line.

**Theorem 5.9 (Threshold crossing along a path).** _Let `X` be any topological
space, `γ : ℝ → X` a continuous path, and `f : X → ℝ` continuous. If
`f(γ a) < τ < f(γ b)` with `a ≤ b`, then there is `c ∈ [a, b]` with `f(γ c) = τ`._

_Proof._ Apply Theorem 5.8 to the composite `f ∘ γ : ℝ → ℝ`, which is continuous as
a composition of continuous maps. ∎

This is `path_crosses_threshold_generic`. Read it as a statement about attacks. An
attack is a path from a safe behavior `γ a` to an unsafe one `γ b`. It might be a
sequence of prompt edits, a continuous interpolation in embedding space, or a
gradient trajectory. Whatever its form, if it is continuous and it succeeds, it
passed through the boundary. There is a moment in every successful attack where the
behavior was exactly at threshold. This is why the boundary, and not the interior
of the unsafe region, is the object a defense must control.

The theorem also quietly refutes a tempting defense strategy, the moat. A designer
might reason that if the safe and unsafe regions could be separated by a buffer, a
band of forbidden inputs wide enough that no small edit crosses it, then attacks
would be stopped at the moat's edge. Theorem 5.9 says the moat is illusory for a
continuous score. The path from safe to unsafe is continuous, so `f` takes every
intermediate value, including every value inside the supposed moat. You cannot
forbid a band of scores without forbidding behaviors that legitimately produce
those scores, and by the no-gap theorem those behaviors exist and abut the safe
region. The only genuine separator is the measure-zero level set itself, and
Theorem 5.20 will show that even that thickens to positive volume once the
defender's own uncertainty is accounted for. There is no moat, only a coastline,
and coastlines are walked, not sealed.

**Theorem 5.10 (No gap).** _Let `X` be connected and `f : X → ℝ` continuous. If
there exist a safe point (`f a < τ`) and an unsafe point (`f b > τ`), then the
boundary `{x | f x = τ}` is nonempty._

_Proof._ On a connected space the image of a continuous real-valued function is an
interval, or more precisely the two-function IVT applies over the whole space. Since
`f` takes a value below `τ` and a value above it, and the reachable values form a
connected subset of `ℝ`, the value `τ` is reached. ∎

This is `no_gap_theorem`, resting on `threshold_level_set_nonempty`. The name is the
moral. There is no gap between the safe and unsafe regions into which a defense could
retreat. A designer might hope to engineer a model whose behaviors are all either
comfortably safe or comfortably unsafe, with an empty margin between, so that a
crude classifier could separate them. Connectedness forbids it. As long as the model
does both safe and unsafe things and its behavior varies continuously, there is a
boundary, and the boundary is populated.

**Theorem 5.11 (Separation is exactly the boundary).** _The closures of the safe and
unsafe regions meet only on the boundary:
`closure(SafeRegion) ∩ closure(UnsafeRegion) ⊆ Boundary`._

_Proof sketch._ Suppose `x` lies in both closures. If `f x > τ`, then `x` is in the
open unsafe region, so a whole neighborhood of `x` is unsafe, which contradicts `x`
being a limit of safe points. Hence `f x ≤ τ`. Symmetrically, if `f x < τ`, a
neighborhood of `x` is safe, contradicting `x` being a limit of unsafe points, so
`f x ≥ τ`. Together `f x = τ`. ∎

This is `safe_unsafe_separated`. It sharpens the no-gap theorem. Not only is the
boundary nonempty, it is precisely the interface, the shared frontier where the two
regions touch. Everything an attacker exploits and everything a defender must guard
lives on this closed set.

## The boundary as a fixed point of defense

The threshold-crossing results acquire teeth when combined with a model of defense.
A defense is a continuous map `D : X → X` that transforms behaviors, meant to push
unsafe inputs back into the safe region while leaving genuinely safe inputs alone. A
_utility-preserving_ defense is one that is the identity on the safe region: it does
not disturb behavior that was fine to begin with. The master theorem of the
`ManifoldProofs` development shows such a defense always fails at the boundary.

**Theorem 5.12 (Defense fixes a boundary point).** _Let `X` be a connected Hausdorff
space, `f : X → ℝ` continuous, with both safe and unsafe points present. Let
`D : X → X` be continuous and equal to the identity on the safe region. Then there is
a boundary point `z` with `f z = τ` and `D z = z`. In particular `D` cannot make `z`
safe, since `f(D z) = f z = τ` is not below `τ`._

_Proof sketch._ The fixed-point set `{x | D x = x}` of a continuous self-map of a
Hausdorff space is closed, being the preimage of the diagonal under the continuous
map `x ↦ (D x, x)`. Since `D` is the identity on the safe region, the safe region
lies in this fixed-point set, and because the set is closed it contains the closure
of the safe region. By the no-gap argument, the safe region is not closed (it is open
and, were it also closed, connectedness would force it to be empty or everything,
both excluded), so its closure contains a boundary point `z` with `f z = τ`. That `z`
is a limit of safe points, hence fixed by `D`, hence unmoved and still exactly at
threshold. ∎

This is `master_theorem` in `MoF_MasterTheorem`, bundling the space and its data into
the `ManifoldOfFailure` structure. It is the analytic cousin of the diagonal's
impossibility. Where Chapter 1 produced a query no verdict could correctly answer,
this produces a behavior no utility-preserving defense can correct. Note what the
theorem does not claim. It does not say `D` fails everywhere or that most of the
unsafe region survives. It says one specific point, on the boundary, is fixed and
unfixed. The quantitative theorems that follow are about upgrading this single
surviving point into a region of positive measure, which is where the danger
actually lies.

## A worked example: interpolating prompts

Take `X` the space of prompt embeddings, identified with `ℝ^n`, and `f` a model's
internal unsafety score, assumed continuous in the embedding. Suppose a benign
prompt embeds at `p` with `f p = τ − 1` and a known jailbreak embeds at `q` with
`f q = τ + 1`. Consider the straight-line path `γ(t) = (1 − t) p + t q` for
`t ∈ [0, 1]`. It is continuous, starts safe, ends unsafe. Theorem 5.9 guarantees a
crossing time `t*` with `f(γ(t*)) = τ`.

The crossing point `γ(t*)` is a prompt that the model scores exactly at threshold. It
is, concretely, a marginal jailbreak: a prompt sitting on the fence, where a
vanishingly small nudge tips it unsafe. If the defense refuses everything the model
scores above `τ`, then by Theorem 5.12 the crossing point itself, and behaviors just
past it, evade the refusal or trigger it spuriously depending on which side of the
knife edge they fall. The boundary is not an abstraction here. It is a family of
real, marginal prompts, and it is exactly the family red teams learn to hunt.

# Lipschitz control of basins

Continuity tells you the basin is open and that unsafe points own balls. It does not
tell you how big those balls are. To get sizes you need to control how fast `f` can
change, and the standard control is the Lipschitz condition.

Recall that `f : X → ℝ` is _`L`-Lipschitz_ if `|f x − f y| ≤ L · dist(x, y)` for all
`x, y`. The constant `L` caps the steepness of the alignment surface. It is a modeling
assumption, but a mild and defensible one. Neural networks with bounded weights and
Lipschitz activations are Lipschitz, and the constant, though often large, is finite
and estimable. With it, the qualitative ball of Theorem 5.4 becomes a quantitative one.

**Definition 5.13 (Robustness radius).** For a point with value `f p` above threshold
`τ` and a Lipschitz constant `L > 0`, the _robustness radius_ is
`robustnessRadius(f p, τ, L) = (f p − τ) / L`. This is `robustnessRadius` in
`MoF_04_LipschitzBasin`.

**Theorem 5.14 (Lipschitz basin ball).** _Let `f` be `L`-Lipschitz with `L > 0`, and
suppose `f p > τ`. If `dist(p', p) < (f p − τ) / L`, then `f p' > τ`. Equivalently, the
open ball of radius `(f p − τ) / L` around `p` lies entirely inside the basin._

_Proof._ The Lipschitz condition bounds the drop in `f` over the step from `p` to `p'`:
`|f p' − f p| ≤ L · dist(p', p) < L · (f p − τ)/L = f p − τ`. In particular
`f p − f p' ≤ |f p' − f p| < f p − τ`, so `f p' > τ`. ∎

This is `lipschitz_basin_ball`, with the set form `basin_ball_subset` and the corollary
`perturbation_stability`. The formula rewards intuition. The radius is the margin
`f p − τ`, how deeply unsafe the point is, divided by `L`, how fast `f` can climb back
down. A behavior that is very unsafe (large margin) on a smooth model (small `L`) sits
at the center of a large ball of guaranteed unsafety. This is a statement about the
robustness of attacks, not defenses. A successful attack is not fragile. Once you have
found a point well inside the unsafe region, an entire neighborhood of nearby behaviors
is unsafe too, so small changes in phrasing or encoding do not rescue the model. The
positivity of the radius is `robustnessRadius_pos`.

**Theorem 5.15 (Deeper points have larger basins).** _If `f p₁ ≤ f p₂`, both above `τ`,
then `robustnessRadius(f p₁, τ, L) ≤ robustnessRadius(f p₂, τ, L)`._

_Proof._ The radius `(v − τ)/L` is increasing in `v` for fixed `τ` and `L > 0`. ∎

This is `robustnessRadius_monotone`. The more deviant the behavior, the more robust it
is to perturbation, which is the opposite of what a defender would want and exactly what
an attacker exploits by pushing deep rather than stopping at the first crossing.

**Theorem 5.16 (Smoother models, larger basins per peak).** _Fix a peak value `f p > τ`.
If `L₁ ≤ L₂`, both positive, then the robustness radius under `L₁` is at least that under
`L₂`._

_Proof._ The radius `(f p − τ)/L` is decreasing in `L`. ∎

This is `smoother_functions_larger_basins` in `MoF_Adv_04_ModelScale`, with the pure
one-dimensional interval version `lipschitz_basin_component_width`. There is a tension
here that the optimal-defense theory later makes precise. A smaller Lipschitz constant
means a smoother, more predictable model, which is usually considered desirable and is
often enforced by regularization. But a smoother model has _larger_ unsafe basins per
peak, since each unsafe point radiates its unsafety further. Smoothness does not remove
the danger; it spreads it. Steepness concentrates the danger into thin spikes that are
harder to hit by chance but sharper when hit.

Before leaving the Lipschitz story, a word on whether the assumption is fair. A skeptic could object that real
models are not Lipschitz with any usable constant, and that a bound of `L = 10^6` makes the robustness radius
`(f p − τ)/L` too small to matter. The objection cuts the right way but the wrong direction. A large `L` shrinks
the guaranteed unsafe ball, which sounds like relief for the defender, but by Theorem 5.17 a large `L` is exactly
what a model needs to draw sharp, narrow basins, and by the cone bound a large local growth rate is what defeats
the defense. A large Lipschitz constant does not make the model safe; it makes the failures spiky. Spiky failures
are harder to hit by random chance and just as easy to hit by gradient, since the gradient is largest precisely
where the surface is steepest. The Lipschitz constant is not a safety margin. It is a description of the terrain,
and rough terrain favors the climber who follows the slope. In practice `L` is estimated layer by layer as a
product of operator norms, and while the global product is loose, the local Lipschitz behavior near a boundary
point, which is what Theorems 5.24 and 5.35 actually use, is often far smaller and directly measurable by probing.

## The other direction: steepness forces oscillation

The Lipschitz constant also bounds how much a function can wiggle, and this gives a lower
bound on `L` for models that must do very different things at nearby inputs.

**Theorem 5.17 (Oscillation needs steepness).** _Suppose `f : [0,1] → ℝ` is `L`-Lipschitz
with `f 0 = f 1 = 0` and `f t = M` for some `t ∈ [0,1]` and `M > 0`. Then `L ≥ 2M`._

_Proof._ Apply the Lipschitz bound on both sides of the peak. From `0` to `t`:
`M = |f t − f 0| ≤ L · t`. From `t` to `1`: `M = |f t − f 1| ≤ L · (1 − t)`. Add the two:
`2M ≤ L·t + L·(1 − t) = L`. ∎

This is `higher_lipschitz_more_oscillation`. A model that must be safe at the endpoints of
an interval and grossly unsafe in the middle pays for it in Lipschitz constant, and hence
in the size of the basin around the middle. You cannot have it both ways: sharp transitions
between safe and unsafe behavior require a large `L`, and a large `L` is exactly what the
cost theory will charge for.

## A worked example: the linear ramp

Let `f(x) = ⟨w, x⟩ + b` be an affine score on `ℝ^n`, the simplest nontrivial alignment
surface, and suppose `‖w‖ = L`. This `f` is exactly `L`-Lipschitz, with the bound achieved
along the direction `w`. Fix `τ` and a point `p` with `f p = τ + m` for a margin `m > 0`.

Theorem 5.14 guarantees a ball of radius `m/L` around `p` inside the basin. This is tight,
not merely a bound. Moving from `p` in the direction `−w/‖w‖` decreases `f` at the maximal
rate `L`, so after distance exactly `m/L` you reach the boundary and any further step exits
the basin. In every other direction you leave more slowly or not at all. The robustness
ball touches the boundary at one point, the foot of the perpendicular from `p` to the
hyperplane `{f = τ}`, and stays strictly inside everywhere else. This is the geometric
content of the robustness radius made visible: the ball is inscribed in the basin, kissing
the boundary along the gradient direction. Every later, harder theorem about basin volume is
a version of inscribing balls like this one and adding up their measures.

# The coarea and cone bounds

We now have unsafe balls of known radius. The next step is to turn radii into volume, and to
do it not just for the interior of the basin but for the thin band straddling the boundary,
because that band is where marginal attacks and imperfect defenses meet. Two bounds do this
work. The coarea bound measures the band as a whole. The cone bound measures the wedge of
persistently unsafe behavior that a defense cannot flatten.

## The coarea bound

The genuine coarea formula relates the volume of a band `{τ − ε ≤ f ≤ τ}` to an integral of
`1/‖∇f‖` over the level sets inside it. That formula is not yet fully available in the
underlying library, so `ManifoldProofs` proves a self-contained substitute by inscribing a
ball, which is enough to get a clean lower bound.

**Definition 5.18 (The `ε`-band).** The band of width `ε` below the threshold is
`coareaBand(f, τ, ε) = {x | τ − ε ≤ f x ≤ τ}`. This is `coareaBand` in `MoF_17_CoareaBound`.

**Theorem 5.19 (Ball inside the band).** _Let `f` be `L`-Lipschitz with `L > 0` and `ε > 0`.
If there is a center point `c` with `f c = τ − ε/2`, then the ball `B(c, ε/(4L))` is contained
in the `ε`-band._

_Proof._ For `x ∈ B(c, ε/(4L))`, the Lipschitz bound gives
`|f x − f c| ≤ L · dist(x, c) < L · ε/(4L) = ε/4`. Since `f c = τ − ε/2`, this puts `f x` in
the open interval `(τ − 3ε/4, τ − ε/4)`, which sits strictly inside `[τ − ε, τ]`. So `x` is in
the band. ∎

This is `lipschitz_ball_subset_band`. The center is chosen at the middle of the band, `τ − ε/2`,
so that a ball of radius `ε/(4L)` cannot escape either wall of the band, because the value can
move by at most `ε/4` across the ball.

**Theorem 5.20 (Coarea volume lower bound).** _Under the hypotheses of Theorem 5.19,
`μ(coareaBand(f, τ, ε)) ≥ μ(B(c, ε/(4L)))` for any measure `μ`. In `ℝ` with Lebesgue measure this
gives the explicit bound `μ(band) ≥ ε/(2L)`. In `ℝ^n` it gives `μ(band) ≥ vol(B(c, ε/(4L)))`, a
positive quantity growing like `(ε/(4L))^n`._

_Proof._ Measure is monotone under the inclusion of Theorem 5.19. In `ℝ` the ball of radius
`ε/(4L)` is an interval of length `2 · ε/(4L) = ε/(2L)`. In `ℝ^n` the ball has the usual Euclidean
volume. ∎

This is `epsilon_band_volume_lower_bound`, with the real and Euclidean specializations
`epsilon_band_volume_lower_bound_real` and `epsilon_band_volume_lower_bound_euclidean`. The center
point `c` is not an extra assumption when the model does both safe and unsafe things: on a connected
space, if `f` dips below `τ − ε` somewhere and rises above `τ` somewhere, the IVT produces a `c` with
`f c = τ − ε/2` for free (`exists_midpoint_for_band`), and the whole argument becomes unconditional
(`epsilon_band_volume_pos_unconditional`). The band around the boundary always has positive, and
computably bounded, measure. This is the quantitative form of "the boundary is populated." It is not
a lonely level set; it is the spine of a slab of positive volume.

**Remark 5.21.** The band volume scales as `ε/L` in one dimension and worsens the defender's
position in a specific way. A defender's classifier, being imperfect, has an uncertainty band of some
width `ε` around its estimate of the threshold. Theorem 5.20 says the true behaviors falling in that
band occupy volume at least `ε/(2L)`. The wider the uncertainty and the smoother the model, the more
behavior is genuinely ambiguous. Sharpening the classifier shrinks `ε` and shrinks the ambiguous
volume linearly, which is progress, but never to zero while `ε > 0`.

## The cone bound

The coarea bound measures the band symmetrically. The cone bound measures something sharper: the
wedge of behaviors that stay unsafe _even after a defense acts on them_. This is where the geometry
directly meets impossibility, because it exhibits a positive-measure set the defense cannot save.

Model the defense as a `K`-Lipschitz map `D` that fixes a boundary point `z`, so `D z = z` and
`f z = τ`. The number `K` is the defense's own smoothness: how much it can move a point per unit
distance. The key quantity is the local growth rate of `f` leaving `z`. If `f` climbs steeply enough
away from `z`, no `K`-Lipschitz defense can drag the climbing behaviors back below `τ`.

**Definition 5.22 (Steep region).** In `ℝ`, the _steep region_ around a boundary point `z` with slope
parameter `s` is `steepRegionR(f, τ, s, z) = {x | f x > τ + s · |x − z|}`. This is `steepRegionR` in
`MoF_18_ConeBound`, with the general metric-space version `steepRegion` in `MoF_11_EpsilonRobust` and
the refined form `steepRegionRefined` in `MoF_20_RefinedPersistence`.

**Theorem 5.23 (Defense distortion bound).** _If `f` is `L`-Lipschitz, `D` is `K`-Lipschitz, and
`D z = z`, then for all `x`, `f(D x) ≥ f x − L(K+1) · dist(x, z)`._

_Proof._ First the defense moves `x` by a controlled amount. By the triangle inequality and the two
Lipschitz bounds,
`dist(D x, x) ≤ dist(D x, D z) + dist(D z, x) ≤ K · dist(x, z) + dist(x, z) = (K+1) · dist(x, z)`,
using `D z = z`. Then `f` changes by at most `L` times that:
`|f(D x) − f x| ≤ L · dist(D x, x) ≤ L(K+1) · dist(x, z)`. Drop the absolute value on the
favorable side to get `f(D x) ≥ f x − L(K+1) · dist(x, z)`. ∎

This is `defense_from_input_bound_R` (and `defense_from_input_bound` in `MoF_11`). The compound
constant `L(K+1)` is the defense's maximum reach: how far below its input value the defense can pull
the alignment score. If `f` rises faster than `L(K+1)` in some direction, the defense loses.

**Theorem 5.24 (Cone measure bound).** _Suppose `f z = τ`, `D z = z`, and `f` grows from `z` at rate
`c > L(K+1)`, meaning `f(z + t) ≥ τ + c·t` for all `t ∈ (0, δ₀)`. Then, with slope `s = L(K+1)`:_

_(1) the open interval `(z, z + δ₀)` is contained in the steep region;_

_(2) the steep region has Lebesgue measure at least `δ₀ > 0`;_

_(3) every point of the steep region stays unsafe after defense, `f(D x) > τ`._

_Proof._ For part (1), take `x = z + t` with `0 < t < δ₀`. Then `f x ≥ τ + c·t > τ + s·t = τ + s·|x − z|`,
using `c > s` and `|x − z| = t`, so `x` is in the steep region. Part (2) follows because the interval
`(z, z + δ₀)` has length `δ₀` and lies inside the steep region, so measure monotonicity gives the bound.
For part (3), let `x` be in the steep region, so `f x > τ + s·|x − z|`. Combine with the distortion bound
of Theorem 5.23: `f(D x) ≥ f x − s·dist(x, z) > τ + s·|x − z| − s·|x − z| = τ`. ∎

This is `cone_measure_bound`, assembling `cone_segment_in_steep_region`, `steep_region_contains_Ioo`,
and `steep_region_measure_pos`, with the explicit lower bound `steep_region_measure_lower_bound`. It is
the geometric heart of the defense impossibility. Chapter 1 gave one surviving query. The master theorem
gave one surviving boundary point. This gives a set of positive measure, an entire cone of behaviors,
every one of which remains unsafe after the defense has done its best. The impossibility is no longer a
measure-zero curiosity. It is a slab of failure with volume you can bound from below.

**Theorem 5.25 (Shallow boundaries can be defended).** _If instead `f` never rises faster than its own
Lipschitz constant from `z`, that is `f x ≤ f z + L · dist(x, z)` for all `x`, then for every `K ≥ 0` the
steep region is empty._

_Proof._ For any `x`, since `f z = τ`, we have `f x ≤ τ + L · dist(x, z) ≤ τ + L(K+1) · dist(x, z)`, the
last step because `K + 1 ≥ 1` and `dist ≥ 0`. So `f x` never exceeds `τ + s·dist(x, z)`, and the steep
region has no points. ∎

This is `shallow_boundary_no_persistence` in `MoF_19_OptimalDefense`. The two theorems together draw a
sharp line. Steep boundaries carry persistent, positive-measure failure that no defense removes. Shallow
boundaries do not. The dividing rate is `L(K+1)`, and whether a real model is steep or shallow at its
boundary is the single most important quantitative fact about its defensibility. The optimal-defense
theory in the cost section is about what happens when a designer tries to buy shallowness by raising `K`.

## A worked example: a corner in the score

Let `f(x) = τ + G · x` for `x ≥ 0` and `f(x) = τ + L₀ · x` for `x < 0` on `ℝ`, with `G` large and
`L₀` moderate, a boundary point at `z = 0` where the score kinks upward. The Lipschitz constant of `f` is
`L = max(G, L₀) = G`. Suppose the defense `D` is `K`-Lipschitz and fixes `0`.

If `G > L(K+1)`, then the growth rate `c = G` beats the defense reach `s = L(K+1)`, and Theorem 5.24
applies with any `δ₀ > 0`: the whole ray `(0, δ₀)` is a steep region of measure `δ₀` that survives the
defense. But here `L = G`, so `G > G(K+1)` requires `K + 1 < 1`, impossible for `K ≥ 0`. The corner is
not steep _relative to its own Lipschitz constant_, so this particular `f` is defensible in principle, in
line with Theorem 5.25. To get genuine persistence you need `f` to rise, near `z`, faster than it rises
elsewhere, so that its local slope `G` exceeds `L(K+1)` with `L` the _global_ constant governing the
defense's smoothing. That is precisely the regime the gradient chain of the next-but-one section reaches
by way of the derivative `‖∇f(z)‖`.

# Dimensional scaling and the boundary's dimension

So far the ambient dimension has been a spectator. It now takes the stage, and it changes everything. The
central fact of high-dimensional geometry, and the reason defense is hard in a way attack is not, is that
volume is cheap for attackers and ruinously expensive for defenders. This asymmetry is the curse of
dimensionality, and `MoF_09_DimensionalScaling` states it precisely.

**Theorem 5.26 (Grid explosion).** _Discretize each of `d` axes into `N` bins, giving a grid of
`N^d` cells. For `N ≥ 2`, the grid size `N^d` grows without bound as `d → ∞`. Covering every cell
requires at least `N^d` queries, and any fixed budget `B` is exceeded once `d` is large enough._

_Proof._ The grid `Fin d → Fin N` has cardinality `N^d` by counting functions. For `N ≥ 2`,
`N^d ≥ 2^d → ∞`. Covering all cells is a surjection onto the grid, and a surjection's domain has at
least the codomain's cardinality, giving the `N^d` lower bound. For any budget `B`, since `2^d`
eventually exceeds `B` and `N^d ≥ 2^d`, the grid outgrows `B`. ∎

This is `grid_card`, `grid_exponential_growth`, `queries_lower_bound_surjective`, and
`no_fixed_budget_defense`. A defender who wants to certify safety cell by cell faces `N^d` cells, and in
the dimensions relevant to language models, where `d` is in the thousands, `N^d` is beyond astronomical.
Exhaustive defense is not merely expensive; it is impossible at any budget.

**Theorem 5.27 (Coverage collapse).** _A single defense patch covering a relative radius `r < 1` in each
dimension covers a fraction `r^d` of the space, and `r^d → 0` as `d → ∞`. The number of patches needed to
cover a fixed fraction `α` grows like `(1/r)^d → ∞`._

_Proof._ The relative volume of a scaled box is the product of its side fractions, `r^d`. For `0 < r < 1`,
`r^d → 0`. Covering fraction `α` needs at least `α / r^d = α · (1/r)^d` patches, and since `1/r > 1` this
grows without bound. ∎

This is `coverage_fraction_vanishes`, `defense_patch_shrinks`, and `exponential_base`, bundled in the
`DimensionalCurse` structure. Here is the asymmetry stated plainly. Each thing the defender builds, a
patch, a rule, a filter, covers a fraction of space that shrinks exponentially with dimension. The
attacker needs to find one point. The defender needs to cover almost all of them. In high dimension the
first is easy and the second is hopeless, and the gap between them is exponential in `d`.

## The dimension of the boundary itself

The basin has full dimension `d`; it is an open set. The boundary is one dimension lower in the generic
smooth case, a hypersurface of dimension `d − 1`. Full Hausdorff-dimension machinery is beyond the current
library, so `MoF_Adv_02_BoundaryDimension` proves the achievable structural facts about the level set.

**Theorem 5.28 (Boundary structure).** _The boundary `{x | f x = τ}` is closed, and its intersection with
any compact set is compact. It is empty exactly when `f` never equals `τ`, and nonempty on a connected space
whenever `f` straddles `τ`. It is the preimage `f⁻¹({τ})`._

_Proof._ Closedness and the preimage identity are Theorem 5.3 restated. Compactness on compacta is the
intersection of a closed set with a compact set. Emptiness and nonemptiness are the trivial and IVT cases. ∎

These are `boundary_is_closed`, `boundary_is_compact_on_compact`, `boundary_empty_of_no_crossing`,
`boundary_nonempty_connected`, and `boundary_is_preimage_singleton`.

**Theorem 5.29 (Regular points are isolated in one dimension).** _For `f : ℝ → ℝ`, if `f` has a nonzero
derivative at a boundary point `z` (a regular value), then `z` is an isolated point of the level set: there
is a punctured neighborhood of `z` on which `f ≠ τ`._

_Proof sketch._ A nonzero derivative makes `f` strictly monotone near `z`, so `f` takes the value `τ`
exactly once nearby. Formally, the derivative being nonzero implies `f` is eventually different from `τ`
away from `z`, which is exactly isolation. ∎

This is `regular_value_boundary` and `boundary_locally_finite_1d`. Where the boundary is regular, it is thin
and well-behaved, a clean interface. Where the gradient degenerates, the boundary can thicken and fold, and
whether real model boundaries are regular or fractal is an open empirical question that this dimension theory
frames but does not settle. The practical upshot is that the codimension-one boundary, though small relative
to the full space, is exactly where the coarea band of Theorem 5.20 gives it positive-volume thickness once
you account for classifier uncertainty.

## Model scale

Function-class complexity, a proxy for model size, controls how intricate the basin can be.

**Theorem 5.30 (Complexity and crossings).** _A constant model has a trivial basin, either empty or the
whole space. A monotone model crosses any threshold at most once. Making the basin oscillate, with many
separated components, requires a large Lipschitz constant, quantitatively `L ≥ 2M` to reach height `M`
between two zeros._

_Proof._ The constant case is immediate. For monotonicity, if `f a = f b = τ` with `a ≤ b` and `f`
monotone, then `f` is squeezed to `τ` on all of `[a, b]`, so there is a single crossing (possibly a flat
one). The oscillation bound is Theorem 5.17. ∎

These are `constant_model_no_basin_empty`, `constant_model_no_basin_univ`, `low_complexity_few_crossings_1d`,
and `higher_lipschitz_more_oscillation`, all in `MoF_Adv_04_ModelScale`. Larger, more expressive models can
carve more intricate basins with more components and finer structure, and they pay for that intricacy in
Lipschitz constant. A bigger model is not automatically safer geometry; it is capable of a more complicated
failure landscape, which is more places for an attacker to look and more places a defender must guard.

## A worked example: random points in the cube

To feel the curse in the body, drop a uniformly random point in the cube `[0, 1]^d` and ask how far it is
from the center. In one dimension it is near the center about half the time. In high dimension almost all the
volume of the cube is near the surface and far from the center, and the pairwise distances between random
points concentrate around a single value. This concentration, examined in the next section, is why a
random-search attacker and a random-defense defender see the same geometry from opposite sides. The attacker,
sampling at random, is very likely to land in the vast peripheral bulk where, if any basin has appreciable
measure, it will be found. The defender, placing patches, watches each one cover a `r^d` sliver of that same
bulk. Same space, same concentration, opposite fortunes.

# Gradient attacks and their chaining

Random search finds the basin if it is large. Gradient attacks find it even when it is small, by following
the slope of `f` uphill. This section formalizes why gradient ascent reliably reaches the unsafe region and
then chains the local step into the global persistence result of the cone bound.

**Theorem 5.31 (An ascent direction exists).** _Let `f : ℝ^n → ℝ` (or any real Hilbert space) be
differentiable at `x` with Fréchet derivative `f'`. If `f' ≠ 0`, then there is a direction `v` and a step
size `ε > 0` with `f(x + ε·v) > f(x)`. In one dimension, if the derivative at `x` is positive, then `f`
strictly increases just to the right of `x`._

_Proof sketch._ In one dimension, a positive derivative means the difference quotient `(f(x + h) − f(x))/h`
tends to a positive limit as `h → 0⁺`, so it is eventually positive, so `f(x + h) > f(x)` for small `h > 0`.
In `n` dimensions, pick any direction `v` on which the derivative `f' v` is nonzero (one exists since
`f' ≠ 0`), flipping sign if needed so that `f' v > 0`, then restrict `f` to the line `t ↦ f(x + t·v)`, whose
one-dimensional derivative at `0` is `f' v > 0`, and apply the one-dimensional case. ∎

This is `ascent_direction_exists` and `multivariate_ascent_direction` in `MoF_10_GradientAttack`, resting on
`discrete_ascent_improvement` and the line-restriction lemma `hasFDerivAt_line_restrict`. The result is the
mathematical license for gradient-based adversarial methods. As long as the score has a nonzero gradient, and
away from critical points it does, there is always a way to nudge the input and raise the score. The
attacker never gets stuck except at a critical point, and critical points are exactly where the gradient
vanishes (`critical_point_iff_fderiv_eq_zero`).

**Theorem 5.32 (The gradient is the steepest direction).** _In a real inner product space, if `f` has
gradient `g` at `x` (so `f' v = ⟨g, v⟩` for all `v`, the Riesz representation), then among unit directions the
inner product `⟨g, v⟩` is maximized by `v = g/‖g‖`, giving directional derivative `‖g‖`._

_Proof._ By Cauchy-Schwarz, `⟨g, v⟩ ≤ ‖g‖ · ‖v‖ = ‖g‖` for unit `v`, with equality when `v` is parallel to
`g`. ∎

The Riesz identity `f' v = ⟨g, v⟩` is `fderiv_apply_eq_inner_gradient`, and the self-pairing `⟨v, v⟩ = ‖v‖²`
that underlies the Cauchy-Schwarz step is `real_inner_self_eq_norm_sq'`. This is why attacks follow the
gradient specifically and not just any ascent direction: the gradient is the direction of fastest increase,
so it reaches the boundary in the fewest steps.

## Chaining local ascent to global persistence

A single gradient step is local. The attack that matters is the whole trajectory, and the theorem that
matters connects the size of the gradient at a boundary point to the existence of a persistent, positive-
measure unsafe region. This is the content of `MoF_21_GradientChain`, which closes the gap between the
derivative and the cone bound.

**Theorem 5.33 (Near-optimal direction from the gradient norm).** _If the derivative `f'` at `z` has
operator norm `‖f'‖ > c ≥ 0`, then there is a unit vector `v` with `f' v > c`._

_Proof sketch._ By definition of the operator norm there is a vector of norm less than `1` on which `f'`
exceeds `c` in absolute value; normalize it to a unit vector, which only increases the value since we divided
by something less than `1`, and choose the sign so that `f' v` is positive. ∎

This is `near_optimal_direction`.

**Theorem 5.34 (Derivative forces local growth).** _If `f` has derivative `f'` at `z`, `f z = τ`, `v` is a
unit vector, and `f' v > c`, then there is `δ > 0` such that `f(z + t·v) > τ + c·t` for all `t ∈ (0, δ)`._

_Proof sketch._ Write `g(t) = f(z + t·v) − τ − c·t`. Its derivative at `0` is `f' v − c > 0`, and `g(0) = 0`.
A function with value zero and positive derivative at a point is strictly positive just to the right, so
`g(t) > 0`, which is the claim. ∎

This is `deriv_implies_local_growth` and its strict form `deriv_implies_strict_local_growth`. Now assemble.

**Theorem 5.35 (Gradient chain to persistence).** _Let `f` be differentiable at a boundary point `z`, with
`f z = τ`, and let the defense be `K`-Lipschitz. If the gradient norm satisfies `‖f'‖ > ℓ(K+1)` for the
relevant Lipschitz constant `ℓ`, then the steep region `{x | f x > τ + ℓ(K+1)·dist(x, z)}` is nonempty, and
in fact the persistent unsafe set `{x | f(D x) > τ}` has positive measure._

_Proof sketch._ Set `c = ℓ(K+1)`. By Theorem 5.33 the gradient norm exceeding `c` yields a unit direction `v`
with `f' v > c`. By Theorem 5.34 that direction gives local growth `f(z + t·v) > τ + c·t` for small `t > 0`,
which places the point `z + t·v` in the steep region: it grows faster than the defense's reach. So the steep
region is nonempty. The cone bound (Theorem 5.24) then upgrades a single steep point to a positive-measure
set that stays unsafe after `D`. ∎

This is `gradient_norm_implies_steep_nonempty` and `gradient_chain_persistent_unsafe`, the latter invoking
`persistent_unsafe_refined` from `MoF_20`. The chain is the complete story of a gradient attack against a
defended model. Measure the gradient at the boundary. If it beats `ℓ(K+1)`, the defense's smoothing budget,
then following that gradient reaches behaviors the defense cannot save, and not just one but a set of positive
volume. The single number `‖∇f(z)‖`, the steepness of the alignment surface at the boundary, decides whether
the model is persistently attackable. This is the transversality condition `transversality_from_deriv` of
`MoF_11` in its sharpest form.

**Remark 5.36.** Compare this to the diagonal. Chapter 1's attack was a construction: build the liar query and
you are done, with no notion of effort. The gradient attack is a process: start somewhere, follow the slope,
arrive. The diagonal's witness is exact and instantaneous but says nothing about cost. The gradient's witness
is approximate and iterative but comes with a step count, `(τ − f(start))/gain` steps to cross, which is a real
budget. The two attacks reach the same boundary. Only the second one has a price tag, and the price tag is the
subject of the rest of the chapter.

# Transferability of attacks across models

Practitioners observe that an attack tuned against one model often works against another. The geometry explains
why, and quantifies exactly how much slack the attack needs to survive the crossing. The mechanism is that
models with similar alignment surfaces have overlapping basins, and an attack with enough margin sits in the
overlap.

Say two models have alignment surfaces `f` and `g` that are _δ-close in sup norm_, meaning `|f x − g x| ≤ δ`
for all `x`. The number `δ` measures how differently the two models score the same behavior, the largest
disagreement anywhere in the space.

**Theorem 5.37 (Transfer with margin).** _If `|f x − g x| ≤ δ` everywhere and `f p > τ + δ`, then `g p > τ`._

_Proof._ From `|f p − g p| ≤ δ` we get `g p ≥ f p − δ > (τ + δ) − δ = τ`. ∎

This is `transfer_attack` in `MoF_06_Transferability`, restated as `transfer_margin_needed` in
`MoF_Cost_07_TransferCost`. The margin `δ` is exactly the toll for crossing between models. An attack that
merely clears `τ` on the source model might fail on the target, because the target could score it up to `δ`
lower. An attack that clears `τ + δ` is guaranteed to transfer. Attackers know this instinctively when they
over-optimize, pushing the attack deep into the source basin rather than stopping at the edge; the geometry
says over-optimization by `δ` is precisely what buys transfer.

**Theorem 5.38 (Basin containment).** _Under δ-closeness, `{x | f x > τ + δ} ⊆ {x | g x > τ}`. If `δ = 0` the
models agree pointwise and their basins are identical at every threshold._

_Proof._ The containment is Theorem 5.37 applied at each point. If `δ = 0` then `f = g`, so the superlevel
sets coincide. ∎

This is `basin_containment` and `identical_models_identical_basins`, with the free-transfer corollary
`zero_distance_free_transfer`. The picture is one basin shrunk slightly inside another. The `(τ + δ)`-basin of
`f` sits entirely within the `τ`-basin of `g`. Any attack landing in the inner basin transfers automatically to
the outer one. The two-sided version, `pointwise_sandwich`, says each score traps the other in a band of width
`δ`, so transfer runs in both directions with the same toll.

**Theorem 5.39 (Transfer is computationally free).** _Given a δ-closeness certificate and a source-model
success `f p > τ + δ`, the target-model success `g p > τ` follows by pure deduction, with zero additional
evaluations of the target model `g`._

_Proof._ The conclusion is Theorem 5.37, whose proof uses only the closeness bound and the source success. No
term in the proof evaluates `g` at any new point. ∎

This is `transfer_is_free` in `MoF_Cost_07`, which literally proves the transferred conclusion is definitionally
the same object as the margin theorem's conclusion, so it consumes no target queries. The cost consequence is
severe for the defender. An attacker who has paid to break one model gets every δ-close model for free, with no
further access to the targets. Model families trained on similar data, or fine-tunes of a common base, are
δ-close for small `δ`, so a single attack sweeps the family. This is why closed deployment of a model whose base
is public offers less protection than it appears.

There is a subtler consequence for defenses that are themselves models. A defense classifier is a function on the
same behavior space, and if it is δ-close to the score it is trying to guard, transfer runs against it too. An
attacker who has learned the geometry of the base score can predict where the defense classifier will misfire,
because a δ-close classifier shares the base's basins up to the margin `δ`. The defense does not get to hide behind
being a separate model. To the extent it agrees with the thing it guards, it inherits the thing's vulnerabilities,
and to the extent it disagrees, it misclassifies genuinely safe behavior. This is the transfer face of the optimal
defense dilemma of Theorem 5.51: closeness buys agreement at the price of shared failure, and distance buys
independence at the price of collateral refusals.

## Estimating the closeness

Transfer needs `δ`, and `δ` must be estimated from samples, which is where concentration enters.

**Theorem 5.40 (Empirical closeness underestimates the truth).** _If `|f xᵢ − g xᵢ| ≤ δ` at every sample point,
then the empirical maximum disagreement over a finite nonempty sample set is at most `δ`. More samples give a
larger, hence tighter, lower estimate of the true `δ`._

_Proof._ The maximum of quantities each bounded by `δ` is bounded by `δ`. Enlarging the sample set can only
raise the maximum, so it moves the estimate up toward the true value. ∎

This is `estimation_cost` and `more_samples_better_estimate`. The empirical sup-norm distance is always a lower
bound on the true one, so an attacker who samples aggressively gets a `δ` estimate that can only improve with
effort, and the estimation cost is the number of paired evaluations, not an exponential quantity. Transfer is
cheap to plan and free to execute.

## A worked example: a fine-tune and its base

Let `g` be a base model and `f` a light fine-tune, and suppose the fine-tune changed the alignment score by at
most `δ = 0.1` anywhere, a plausible figure for a small parameter update. An attacker who has found, against the
fine-tune `f`, a prompt `p` scoring `f p = τ + 0.15`, that is with margin `0.15 > δ`, is guaranteed by Theorem
5.37 that the base model also scores `g p > τ`: the attack transfers. Had the attacker stopped at margin `0.05`,
transfer would not be guaranteed, and indeed might fail. The lesson for both sides is the same number. Fine-tuning
for safety with a small `δ` leaves the base model's attacks almost entirely intact, and only attacks with margin
below `δ` are potentially neutralized by the update. Small edits move the basin by `δ` and no more.

# The cost theory

Everything so far has been about sets: which behaviors are unsafe, how they cluster, how they transfer. The cost
theory converts geometry into budgets. It answers the operational questions. What does an attacker pay to find a
failure? What does a defender pay to prevent one? How does the ratio scale? The `MoF_Cost` series builds this in
ten layers, and the punchline is a single asymmetry: attack cost stays bounded while defense cost explodes with
dimension.

The ten layers are worth naming as a stack, because each rests on the one below. Ball volume (layer one) turns a
radius into measure. Basin volume (layer two) inscribes a robustness ball and reads off a lower bound on the basin.
Hitting time (layer three) turns a measure fraction into an expected number of random trials. Concentration (layer
four) controls the error of estimating the surface from samples. Attack cost (layer five) counts the steps of a
directed climb. Defense cost (layer six) counts the patches needed to cover space. Transfer cost (layer seven)
prices porting an attack across models. The cost ratio (layer eight) divides defense by attack. Lipschitz
estimation (layer nine) bounds the sampling budget. The unified theory (layer ten) bundles the parameters and
proves the master asymmetry. Read from the bottom, it is a derivation. Read from the top, it is a single sentence:
the ratio diverges.

## Ball and basin volume

The first two layers turn radii into measure, the raw material of every later budget.

**Theorem 5.41 (Ball volume is positive and monotone).** _In `ℝ^n` with Lebesgue measure, an open ball of
positive radius has positive volume. Volume is monotone in the radius. In `ℝ` the ball of radius `r` has volume
exactly `2r`._

_Proof._ A nonempty open set has positive Lebesgue measure. Larger radius means a larger ball by inclusion, so
larger volume by monotonicity. In `ℝ` the ball is an interval of length `2r`. ∎

These are `ball_measure_pos`, `ball_measure_mono`, and `ball_measure_scale` in `MoF_Cost_01_BallVolume`.

**Theorem 5.42 (Basin volume lower bound).** _If `f` is `L`-Lipschitz and `f p > τ`, the basin `{x | f x > τ}`
contains the robustness ball of radius `(f p − τ)/L` around `p`, so its measure is at least that of the ball. If
`f` is merely continuous with an unsafe point, the basin still has strictly positive measure._

_Proof._ The containment is the Lipschitz basin ball (Theorem 5.14) restated as a subset relation, and measure
is monotone. The continuous case is Theorem 5.5. ∎

This is `robustness_ball_subset_basin`, `basin_measure_ge_ball`, and `basin_measure_ge_ball_pos` in
`MoF_Cost_02_BasinVolume`, with measurability recorded in `basin_measurableSet`. This is the volume version of
"attacks are robust." The attacker's target is not a point but a ball, and the ball's volume, at least
`(margin/L)^n` times a dimensional constant, is the probability mass a random search must hit.

## Hitting time

If the basin has probability `p` under the sampling distribution, how many random trials until a hit? The answer
is the geometric distribution, and the cost layer proves its analytic core.

**Theorem 5.43 (Random search hitting time).** _Suppose each independent trial lands in the basin with
probability `p`, `0 < p ≤ 1`. The probability of missing on all of the first `n` trials is `(1 − p)^n`, which
decreases monotonically to `0`. The probability of at least one hit, `1 − (1 − p)^n`, increases to `1`. The
expected number of trials to the first hit is `1/p`._

_Proof sketch._ The miss probability `(1 − p)^n` is a power of a number in `[0, 1)`, hence decreasing to zero.
The complementary hit probability increases to one. For the expectation, the partial geometric sums
`∑_{k<n} (1 − p)^k` are bounded above by the infinite geometric series `∑_{k≥0} (1 − p)^k = 1/p`, and this sum is
the expected trial count of the geometric distribution. ∎

This is `miss_probability_vanishes`, `hit_probability_tends_to_one`, `geometric_sum_le_inverse`, and
`tsum_geometric_eq_inv` in `MoF_Cost_03_HittingTime`. The expected hitting time `1/p` is the attacker's random-
search budget. Combine it with the basin volume: if the basin occupies a fraction `p` of the space, the attacker
expects to wait `1/p` random draws. When `p` is a constant fraction, this is cheap. The trouble for the attacker,
and the only real hope for the defender, is that in high dimension `p` can be exponentially small, which is where
gradient attacks earn their keep by replacing random search's `1/p` with a linear step count.

## Concentration and estimation

The defender estimates `f` from finite samples and classifies by the estimate. Concentration controls the error.

**Theorem 5.44 (Estimation margin).** _Suppose an estimate `f̂` satisfies `|f̂ x − f x| ≤ ε` everywhere. If
`f̂ x > τ + ε`, then truly `f x > τ`; if `f̂ x < τ − ε`, then truly `f x < τ`. The undecidable band is
`{x | |f̂ x − τ| ≤ ε}`, and it shrinks as `ε` shrinks._

_Proof._ From `|f̂ x − f x| ≤ ε`: if `f̂ x > τ + ε` then `f x ≥ f̂ x − ε > τ`, and symmetrically for the safe
side. The band characterization is a rearrangement of the absolute-value inequality. ∎

This is `estimation_error_bound_unsafe`, `estimation_error_bound_safe`, `estimation_uncertain_band`, and
`estimation_band_shrinks` in `MoF_Cost_04_Concentration`. The estimate confidently classifies points more than `ε`
from the threshold and cannot classify points within `ε` of it. That undecidable band is exactly the coarea band
of Theorem 5.20, whose volume is at least `ε/(2L)` in one dimension. Estimation error and boundary geometry are the
same phenomenon viewed twice: the band the classifier cannot resolve is the band the geometry says has positive
volume.

**Theorem 5.45 (Lipschitz interpolation from samples).** _For an `L`-Lipschitz `f`, knowing `f` at a sample `x₀`
bounds `f` nearby: `|f x − f x₀| ≤ L · dist(x, x₀)`. To hold the estimation error below `ε` everywhere in
`[0, 1]^d` you need samples no farther than `ε/L` apart, which forces on the order of `(L/ε)^d` samples._

_Proof._ The bound is the Lipschitz condition. Covering `[0, 1]^d` so that every point is within `ε/L` of a sample
requires a grid of spacing `2ε/L`, hence roughly `(L/(2ε))^d` points, exponential in `d`. ∎

This is `lipschitz_estimation_error` and `estimation_improves_with_distance` in `MoF_Cost_09_LipschitzEstimation`,
with the exponential covering count `total_estimation_budget`, and the sup-norm triangle and nearest-sample bounds
`sup_norm_triangle` and `n_samples_coverage` in `MoF_Cost_04`. The defender's estimation problem inherits the curse
directly. Certifying the whole space to accuracy `ε` costs `(L/ε)^d` samples, the same exponential wall as
exhaustive gridding. Concentration of measure, meanwhile, works against the defender's sampling: in high dimension
the samples spread thin and the nearest sample to a random point is far, so the interpolation bound `L · dist` is
loose exactly where it matters.

## Attack, defense, and transfer cost

Now the three budgets, each a corollary of the layers above.

**Theorem 5.46 (Attack cost).** _An iterative attack gaining at least `δ > 0` per step, on a score bounded in
`[0, 1]`, reaches any threshold `τ` from a start `s₀` in at most `⌈(τ − s₀)/δ⌉ + 1` steps, and can take at most
`⌈1/δ⌉` useful steps in all. On reaching `f > τ` with margin, the attacker gains a robustness ball of radius
`(f − τ)/L`._

_Proof sketch._ By induction, after `n` steps the score is at least `s₀ + n·δ`, so it exceeds `τ` once
`n ≥ (τ − s₀)/δ`. Since the score cannot exceed `1`, the total number of `δ`-gaining steps is at most `1/δ`. The
robustness ball is Theorem 5.14. ∎

This is `attack_value_after_n_steps`, `steps_to_threshold`, `attack_cost_upper_bound`, and `total_attack_cost` in
`MoF_Cost_05_AttackCost`, with the monotone-convergence backbone `attackSeq_convergent` and `finite_steps_bound`
in `MoF_05_MonotoneConvergence`. The attack budget is `1/δ`, a constant independent of dimension. This is the crux.
The attacker's cost does not grow with `d`, because the attacker follows a one-dimensional trajectory of steps and
each step gains a fixed amount, regardless of how many dimensions surround the path.

**Theorem 5.47 (Defense cost).** _A defender covering the space with patches of relative radius `r < 1` needs on
the order of `(1/r)^d` patches to cover a fixed fraction, and this grows without bound as `d → ∞`. For any budget
`B` there is a critical dimension beyond which the defense cost exceeds `B`._

_Proof._ Each patch covers fraction `r^d`, so covering fraction `α` needs `α/r^d = α·(1/r)^d` patches, which tends
to infinity since `1/r > 1`. Passing any fixed `B` is then a matter of taking `d` large. ∎

This is `patches_needed`, `defense_cost_exponential`, and `critical_dimension` in `MoF_Cost_06_DefenseCost`. The
defense budget is `(1/r)^d`, exponential in dimension. Set this beside the attacker's constant `1/δ` and the
asymmetry is stated.

**Theorem 5.48 (Transfer cost).** _Porting an attack across two δ-close models costs zero target queries once the
source attack has margin `δ`, and the closeness `δ` itself is estimated from samples at a cost that grows only with
the desired precision, not with dimension._

_Proof._ Free execution is Theorem 5.39. The estimation cost is Theorem 5.40. ∎

This is the content of `MoF_Cost_07_TransferCost`. Transfer sits on the attacker's side of the ledger, adding
essentially nothing to the attack budget while multiplying its reach across a model family.

## The cost ratio and the master theorem

The three budgets combine into one number that decides the contest.

**Definition 5.49 (Cost ratio).** The _defense-to-attack cost ratio_ is
`costRatio(N, d, δ) = N^d · δ`, the defender's `N^d` cells divided by the attacker's `1/δ` steps. This is
`costRatio` in `MoF_Cost_08_CostRatio`, and in bundled form `unifiedCostRatio` on the `CostParameters` structure of
`MoF_Cost_10_UnifiedTheory`, where it simplifies to `δ · N^d` (`unifiedCostRatio_eq`).

**Theorem 5.50 (Cost asymmetry, master theorem).** _For any fixed grid resolution `N ≥ 2` and attack gain
`δ > 0`, the cost ratio `δ · N^d` is positive, increases with `d`, and tends to infinity. For any willingness-to-pay
ratio `R > 0`, however large, there is a critical dimension `d₀` beyond which the ratio exceeds `R`. The attacker's
budget is independent of dimension; the defender's is exponential in it._

_Proof sketch._ The ratio is `δ · N^d` with `N ≥ 2`, so it is a positive constant times an exponential in `d`,
hence positive, monotone increasing, and divergent. Given `R`, divergence supplies a `d₀` past which `δ · N^d > R`.
The attack budget `1/δ` contains no `d`, so it is constant across dimension. ∎

This is `cost_ratio_tends_to_infinity`, `cost_ratio_exceeds_any_bound`, `attacker_advantage_quantified`, and the
capstone `MASTER_THEOREM_cost_asymmetry`, with dimension-independence recorded in
`attack_budget_dimension_independent` and `defenseBudget_exponential`. As a concrete anchor, `two_dimension_ratio`
computes that even at `d = 2`, `N = 25`, `δ = 0.01`, the ratio is already `6.25`, and it only climbs from there.
This theorem is the quantitative summary of the whole chapter. The boundary exists (qualitative, from the diagonal
and the IVT). The boundary is populated by a positive-measure region (coarea and cone bounds). Finding a point in
that region costs the attacker a dimension-independent budget (attack cost and hitting time). Covering it costs the
defender a dimension-exponential budget (defense cost). The ratio of the two diverges. No budget closes the gap.

## The optimal defense dilemma

A defender might try to escape by tuning the defense's own smoothness `K`. The optimal-defense theory shows this
only trades one failure mode for another.

**Theorem 5.51 (No `K` wins).** _For an alignment surface with Lipschitz constant `L` and boundary growth rate
(transversality slope) `G`, and a `K`-Lipschitz defense, exactly one of two things holds for every `K ≥ 0`: either
`G > L(K+1)`, in which case a persistent unsafe region of positive measure survives (Theorem 5.24), or
`L(K+1) ≥ G`, in which case the failure band has width at least `G·δ`. When `G > L`, the critical value
`K* = G/L − 1 > 0` is the unique point where the two modes trade off exactly, and neither horn is escapable. When
`G ≤ L`, the boundary is shallow and defensible in principle (Theorem 5.25)._

_Proof sketch._ The dichotomy `G > L(K+1)` or `L(K+1) ≥ G` is a trichotomy-free case split on a single real
comparison. Increasing `K` increases `L(K+1)` strictly (`defense_band_monotone`), so it eventually flips the first
horn into the second, and at `K = K* = G/L − 1` the two sides are equal (`optimalK_critical`). Below `K*` the steep
region is nonempty; at or above it the band width `L(K+1)·δ ≥ G·δ`. Both horns are realized for `G > L`
(`defense_dilemma_both_realizable`), and for `G ≤ L` the shallow case gives `L(K+1) ≥ L ≥ G` for all `K ≥ 0`. ∎

This is `defense_cannot_win`, `optimal_K_exists`, `defense_dilemma_both_realizable`, and
`complete_defense_characterization` in `MoF_19_OptimalDefense`. The dilemma is genuine. A gentle defense (small
`K`) leaves persistent unsafe cones. An aggressive defense (large `K`) smears the failure band wide, distorting the
model's behavior across a region of width growing linearly in `K`. Between the two extremes sits `K*`, and at `K*`
the defender has minimized the total damage but not eliminated it. The only way out is `G ≤ L`, a boundary that
never rises faster than the model's global smoothness, and Theorem 5.35 says that condition is exactly
`‖∇f(z)‖ ≤ L` at every boundary point, a demand that the boundary have no spikes at all.

## A worked example: the cost ratio in a real regime

Put numbers to it. Suppose a language model's behavior space, for the purpose of a particular attack, is well
described by `d = 20` effective dimensions, with a modest grid resolution `N = 10` and an attack that gains
`δ = 0.05` per step. The attacker's budget is about `1/δ = 20` steps. The defender's cell count is `N^d = 10^20`.
The cost ratio is `δ · N^d = 0.05 · 10^20 = 5 · 10^18`. The attacker pays twenty steps; the defender pays five
quintillion cells. Now double the effective dimension to `d = 40`. The attacker still pays twenty steps. The
defender pays `10^40`. Nothing the defender does to `N`, `r`, or `K` touches the exponential in `d`, and the
attacker's budget never sees `d` at all. This is not a pessimistic model chosen to make a point. It is the generic
behavior of the cost ratio, proved to diverge for every fixed `N ≥ 2` and `δ > 0` in Theorem 5.50.

The one honest place a defender can push back is the word "effective." The exponent is not the raw parameter count
but the dimension of the manifold the attack actually explores, and if that manifold is low-dimensional the ratio
is manageable. This is the real research question hiding under the theorem: how large is the effective dimension of
the space of behaviors an attacker can reach with realistic edits? If it is small, say a handful, the defender has a
chance, because `N^d` for small `d` is a finite budget. If it is large, the defender has already lost, because no
budget crosses the exponential. The cost theory does not measure the effective dimension for you; it tells you that
this one number, and not the model's size or the defender's cleverness, decides the contest. Everything else in the
budget, `N`, `δ`, `r`, `K`, enters polynomially or as a constant. Only `d` enters the exponent, and only `d` is
worth arguing about.

# Concentration of measure, the two faces of high dimension

The cost theory kept referring to a fraction `p`, the probability mass of the basin, and treated it as a knob
that could be small or large. High-dimensional geometry does not leave `p` free. It concentrates. Distances,
norms, and the values of well-behaved functions all cluster around single values as the dimension grows, and this
clustering is the deepest reason the attacker and the defender experience the same space so differently. This
section makes the concentration precise and draws out its two faces.

Start with the crudest volume bound, which needs no smoothness at all, only nonnegativity and integrability of the
alignment surface.

**Theorem 5.52 (Markov bound on the basin).** _Let `f ≥ 0` be integrable against a measure `μ`. Then for any
`ε > 0`, `ε · μ({x | f x ≥ ε}) ≤ ∫ f dμ`. Equivalently, `μ({x | f x ≥ ε}) ≤ (1/ε) ∫ f dμ`._

_Proof._ On the set `{f ≥ ε}` the integrand is at least `ε`, so
`∫ f dμ ≥ ∫_{f ≥ ε} f dμ ≥ ε · μ({f ≥ ε})`. Divide by `ε`. ∎

This is `markov_real_basin` (with the extended-real form `markov_ennreal_basin`) in `MoF_Adv_10_MeasureBounds`. It
is Markov's inequality read as a statement about basins: the measure of the region where the alignment score is at
least `ε` is controlled by the average score divided by `ε`. A model whose average deviation is small cannot have a
large high-deviation basin. This sounds like comfort for the defender, and at a fixed threshold it is. But it also
sets a floor the defender cannot easily lower, because the average `∫ f dμ` is a property of the whole model, not
of any local patch, and driving it down means changing the model everywhere at once.

The Markov bound is one-sided and loose. The sharp phenomenon in high dimension is two-sided and tight, and it is
about Lipschitz functions specifically.

**The concentration phenomenon.** On the unit sphere in `ℝ^n`, or under a standard Gaussian on `ℝ^n`, an
`L`-Lipschitz function `f` deviates from its median `m` by more than `t` with probability at most about
`2 · exp(-c · t² / L²)` for a universal constant `c`. As `n` grows, the constant in the exponent works in the
attacker's favor through the geometry, but the shape is the key: a Lipschitz function is nearly constant across
almost all of a high-dimensional space. This is the Lévy-Milman-Talagrand concentration of measure, and while its
full form lives beyond the current formal library, its consequences are exactly the cost asymmetries the library
does prove. It is worth seeing why concentration and the curse are the same fact.

Consider the alignment surface `f`. If `f` is `L`-Lipschitz, concentration says its values pile up around the
median `m`. Suppose the threshold `τ` sits above `m`, so that most behaviors are safe. Then the basin `{f > τ}` is
the far tail of a concentrated distribution, and its measure `p` is exponentially small in `(τ − m)² / L²`. This is
good for the defender in the sense that a random behavior is almost never unsafe. It is catastrophic for the
defender in the sense that Theorem 5.5 still guarantees `p > 0`, so the tail is nonempty, and the hitting-time
result (Theorem 5.43) says random search needs `1/p` draws, which is huge, but the gradient chain (Theorem 5.35)
says a directed attacker skips the `1/p` wait entirely by climbing the gradient straight to the tail. Concentration
hides the basin from random draws and does nothing to hide it from gradients. The attacker who knows this never
samples at random.

**Theorem 5.53 (Positive-measure failure band, full defense).** _Let `X` be a connected Hausdorff metric space with
a positive-on-opens measure `μ`. Let `f` be `L`-Lipschitz and continuous with `L > 0`, let `D` be a `K`-Lipschitz
continuous defense that fixes the safe region, and suppose the boundary is transverse in the sense that `f` grows
from some fixed boundary point faster than `L(K+1)`. Then the set of behaviors that remain unsafe after defense,
`{x | f(D x) > τ}`, has strictly positive measure._

_Proof sketch._ The transversality hypothesis places a point in the steep region (Theorem 5.24, part 1). The
distortion bound (Theorem 5.23) shows every steep point stays unsafe after `D` (Theorem 5.24, part 3). The steep
region is open and nonempty, so it has positive measure, and it sits inside the persistent unsafe set, which
therefore also has positive measure. ∎

This is `epsilon_robust_impossibility`, `positive_measure_failure_band`, and `persistent_unsafe_region` in
`MoF_11_EpsilonRobust`, the results the cone bound and gradient chain feed into. It is the strongest form of the
defense impossibility in this chapter. The master theorem (Theorem 5.12) gave one surviving boundary point. The
cone bound (Theorem 5.24) gave a surviving interval in one dimension. This gives a surviving set of positive
measure in full generality, under honest Lipschitz hypotheses on both the model and the defense. The impossibility
is not a boundary artifact of measure zero. It is a region an adversary can enter.

**Remark 5.54 (The two faces).** Concentration has a face turned toward the attacker and a face turned toward the
defender, and they are the same geometry. Toward the defender it says: your samples spread thin, the nearest sample
to a random point is far (distance concentrates around a large value), so your interpolation bound `L · dist` from
Theorem 5.45 is loose everywhere, and you cannot certify the space without exponentially many samples. Toward the
attacker it says: the space is mostly one big undifferentiated bulk where a Lipschitz score is nearly constant, so a
gradient points reliably toward the rare tail, and once in the tail the robustness ball (Theorem 5.14) is a
generous target. The defender sees a space too big to cover. The attacker sees a space too smooth to hide the exit.
Both are reading the same concentration inequality.

## A worked example: the Gaussian annulus

Draw `x` from a standard Gaussian on `ℝ^n`. The squared norm `‖x‖²` is a sum of `n` independent squared standard
normals, with mean `n` and standard deviation `√(2n)`. So `‖x‖` concentrates sharply around `√n`, within a window
of width on the order of `1`, which is a vanishing fraction of `√n`. Almost all the Gaussian mass sits in a thin
annulus at radius `√n`. The center, where the density is highest, is almost empty of mass, because it has almost no
volume.

This single picture explains the whole chapter in miniature. Suppose the alignment surface is the smooth radial
function `f(x) = ‖x‖`, which is `1`-Lipschitz, and the threshold is `τ = √n + 3`. The basin `{‖x‖ > √n + 3}` is the
outside of the annulus, and its Gaussian mass is tiny, on the order of `exp(-c · 9)`, independent of `n` because the
window width does not grow. Random search for the basin costs `1/p`, a large fixed number. But `f` has gradient
`x/‖x‖` of norm exactly `1` everywhere off the origin, so a gradient attacker starting anywhere walks outward at
unit speed and reaches `τ` in about `3` steps regardless of `n`. The defender who wants to patch the basin must
cover a thin shell in `ℝ^n`, whose covering number is exponential in `n`. Same basin, three numbers: attacker cost
constant, defender cost exponential, random-search cost large but irrelevant because the attacker does not use
random search. That is Theorem 5.50 wearing Gaussian clothes.

# Iterated and discrete attacks

Two loose ends remain, and both matter for real deployments. Attacks are rarely single shots; they accumulate over
a conversation or a campaign. And behavior spaces are often discrete, made of tokens rather than points in `ℝ^n`,
so the continuum arguments need a discrete counterpart. The `ManifoldProofs` development treats both, and the
results reconnect this chapter to the diagonal.

## Iterated attacks

Model a multi-turn interaction as a sequence of alignment surfaces `f_t` and defenses `D_t`, one per turn, with the
attacker free to probe repeatedly. The relevant quantity is the running maximum of the scores achieved, since the
attacker only needs to succeed once and can keep the best result.

**Theorem 5.55 (The attacker's running edge).** _The running maximum of the attacker's scores over turns is
monotone nondecreasing: it never falls as turns accumulate. Under a capacity-parity model where the defense has a
fixed number of correction slots and the attacker has one more configuration than there are slots, the pigeonhole
principle forces the defense to collapse two distinct attacks to the same output, so at least one attack is not
individually corrected. Over `T` turns of probing the defense reveals at least `T` classifications, and one more
attack than the defense can absorb overwhelms it._

_Proof sketch._ The running maximum `sup_{s ≤ t} score_s` is a supremum over a growing finite set, hence
nondecreasing in `t` (`running_max_monotone`). The pigeonhole step is the capacity argument: a defense with
`n_unsafe` free slots handling `n_unsafe + 1` distinct configurations cannot separate them all
(`one_more_attack_overwhelms`), and iterated over an attack surface of size `2^d` against total defense capacity
`2^d` the attacker retains a permanent margin (`attacker_permanent_edge`). Each probe yields a classification, so
`T` turns leak at least `T` bits of boundary information (`defense_leaks_per_turn`). ∎

These are `running_max_monotone`, `one_more_attack_overwhelms`, `attacker_permanent_edge`, `defense_leaks_per_turn`,
and the capstone `multi_turn_impossibility` and `boundary_points_accumulate` in `MoF_13_MultiTurn`. The picture is
of an attacker with a ratchet. Each turn can only improve the best result achieved so far, each probe extracts
information about where the boundary lies, and the boundary points accumulate turn over turn. A defense that holds
for one turn need not hold for a hundred, and the theory says it will not: the attacker's edge is permanent under
parity, and iteration converts a small per-turn leak into a boundary the attacker eventually maps. This is the
formal shadow of the practical fact that long conversations erode guardrails.

## The discrete boundary

When the behavior space is a finite chain of tokens rather than a continuum, the intermediate value theorem is
replaced by a discrete crossing lemma, and the master theorem by a discrete fixed-point argument.

**Theorem 5.56 (Discrete crossing and the discrete trilemma).** _Let `f` be defined on a finite chain
`0, 1, …, n+1` with `f 0 < τ` and `f(n+1) ≥ τ`. Then there is an adjacent pair `i, i+1` with `f i < τ` and
`f(i+1) ≥ τ`: the score crosses the threshold across a single step. If a defense `D` fixes every safe point of the
chain, it fixes such a crossing point, and cannot make it safe. More abstractly, for any `f`, threshold `τ`, defense
`D` fixing the safe region, and any unsafe point `u`, either `D` leaves `u` unsafe, or `D` moves `u` and thereby
fails to be the identity where it needed to be. A verdict that is both complete (decides every point) and injective
(never conflates two points) cannot exist on a space rich enough to encode its own decisions._

_Proof sketch._ The crossing lemma is the discrete IVT: take the largest index `i` with `f i < τ`; since
`f(n+1) ≥ τ` this `i` is at most `n`, and by maximality `f(i+1) ≥ τ` (`discrete_ivt`). The defense-fixes-crossing
claim is the discrete master theorem (`discrete_defense_boundary_fixed`). The case split on `u` is
`discrete_trilemma`. The completeness-versus-injectivity impossibility is
`injectivity_forces_incompleteness` and `completeness_forces_noninjectivity`. ∎

These are in `MoF_12_Discrete`. The last clause is where the geometry rejoins the diagonal. The discrete trilemma is
a counting argument, pigeonhole rather than connectedness, but it delivers the same conclusion the diagonal did in
Chapter 1: a verdict that tries to be both complete and consistent on a self-encoding domain breaks. Here the two
engines, analytic and diagonal, are visibly the same shape. The continuum route reaches the boundary by
connectedness and the IVT; the discrete route reaches it by pigeonhole; the self-referential route reaches it by
diagonalization. Three proofs, one boundary.

**Remark 5.57.** The discrete results are the bridge back to the book's spine. Chapter 1 built a query no boolean
verdict answers, using self-reference. `MoF_12`'s `discrete_trilemma` builds an unsafe point no utility-preserving
defense corrects, using order and counting. They are not the same theorem, but they are instances of one pattern:
a system asked to classify a domain it is embedded in must leave a witness uncovered. The geometry chapters spent
their length measuring that witness, giving it volume, distance, and cost. The discrete trilemma reminds us that
the witness was there from the first page, and that the measuring, not the existence, is what this half of the book
added.

# The two halves, joined

It is worth stepping back to see how this chapter sits against the diagonal chapters, because the book's thesis
lives in the join.

The diagonal proves existence and nothing more. There is a query no verdict answers, an index no naming captures, a
behavior no defense corrects. These are theorems about what cannot be, and they are indifferent to quantity, cost,
and dimension. Chapter 1's three-line proof would be unchanged if the space were finite or infinite, small or vast.
That indifference is its strength and its limit. It reaches conclusions no amount of engineering can overturn, and
it reaches nothing else.

This chapter proves the quantitative shape of the same failure. The boundary the diagonal guarantees to exist is
here shown to have positive-measure thickness (coarea bound), to carry a persistent unsafe cone against any defense
(cone bound), to be reachable by a dimension-independent attack budget (attack cost and hitting time), and to be
coverable only at dimension-exponential defender cost (defense cost, cost ratio). Where the diagonal says "a bad
point exists," the geometry says "a region of bad points exists, it is cheap to enter and expensive to seal, and
the gap grows without bound in dimension."

The two halves are not rivals. They are the qualitative and quantitative faces of one fact. The impossibility
theorems tell you that you cannot win. The cost theory tells you how badly you lose, and it turns out you lose by an
exponential margin that no budget closes. A practitioner who has absorbed only the diagonal might hope that the bad
point is rare, hard to find, or easy to patch. The geometry closes each of those hopes in turn. A practitioner who
has absorbed only the cost theory might think the problem is merely hard, a matter of enough compute. The diagonal
closes that hope: the boundary is not hard to remove, it is impossible to remove. Read together, they say the
danger is both certain and quantitatively severe, and that is the honest picture of what deploying a capable model
next to its own failure boundary actually means.

# Historical and bibliographic notes

The intermediate value theorem underlying the threshold-crossing results is Bolzano's, and its use to force a
boundary between qualitatively different regimes is as old as analysis. The reading of that boundary as an
unavoidable attack surface for learned systems is recent and is the organizing idea of the `ManifoldProofs`
development. The curse of dimensionality has many independent origins; the covering-number form used here, that
maintaining accuracy `ε` for an `L`-Lipschitz function on `[0, 1]^d` costs on the order of `(L/ε)^d` samples, is
standard in nonparametric statistics and approximation theory. Concentration of measure in high dimension, the
phenomenon that random points cluster and Lipschitz functions vary little, is due in its modern form to Lévy,
Milman, and Talagrand, and its adversarial reading, that concentration helps the attacker and hurts the defender,
is the contribution of the cost layers. The gradient-attack formalization abstracts the practice of methods such as
FGSM and projected gradient descent into their mathematical skeleton: a nonzero derivative always affords an ascent
step. The coarea inequality proper, relating band volume to level-set integrals of `1/‖∇f‖`, is Federer's; the
ball-inscription substitute used here is a self-contained lower bound that avoids the parts of geometric measure
theory not yet formalized. All theorem names cited in this chapter refer to the machine-checked statements in the
companion Lean library, and where the prose and the Lean differ, the Lean is authoritative.

# Exercises

**Exercise 5.1.** Verify directly that for the Gaussian bump `f(x) = M · exp(-‖x‖²/2)` on `ℝ^n` with `0 < τ < M`,
the basin `{x | f x > τ}` is the ball of radius `√(2 ln(M/τ))`. Confirm the three soft predictions (openness,
positive measure, connectedness) against Theorems 5.3, 5.5, and 5.7, and identify which `MoF_*` result each uses.

**Exercise 5.2.** Show that Theorem 5.4 (every unsafe point owns a ball) gives no lower bound on the radius using
continuity alone, by exhibiting a continuous but non-Lipschitz `f : ℝ → ℝ` and an unsafe point whose guaranteed
ball can be made arbitrarily small. Then show that adding a Lipschitz hypothesis pins the radius to `(f p − τ)/L`
via `lipschitz_basin_ball`.

**Exercise 5.3.** Prove the no-gap theorem (Theorem 5.10) fails on a disconnected space by constructing an `f` on
`X = [0, 1] ∪ [2, 3]` that is below `τ` on the first interval and above `τ` on the second, with empty boundary.
Explain in one sentence why connectedness is the exact hypothesis `no_gap_theorem` requires.

**Exercise 5.4.** In the affine example `f(x) = ⟨w, x⟩ + b` with `‖w‖ = L`, verify that the robustness ball of
Theorem 5.14 is tight: it touches the boundary hyperplane at exactly one point and lies strictly inside the basin
everywhere else. Compute that point in terms of `p`, `w`, and the margin.

**Exercise 5.5.** Using `higher_lipschitz_more_oscillation` (Theorem 5.17), show that a model required to be safe
(`f = 0`) at two inputs a unit apart and grossly unsafe (`f = M`) at their midpoint must have Lipschitz constant at
least `2M`. Then use `smoother_functions_larger_basins` to argue that lowering `L` to below `2M` is impossible
without removing the unsafe spike, and interpret this as a no-free-lunch statement for smoothing.

**Exercise 5.6.** Derive the one-dimensional coarea bound `μ(band) ≥ ε/(2L)` (Theorem 5.20) from the ball-in-band
containment (Theorem 5.19) and the length formula for intervals. Then generalize the computation to `ℝ^n` and
express the bound in terms of the volume of a Euclidean ball of radius `ε/(4L)`.

**Exercise 5.7.** For the cone bound (Theorem 5.24), suppose `f` grows from a boundary point `z` at rate `c` and the
defense has reach `s = L(K+1)`. Show that the surviving steep region on `(z, z + δ₀)` has measure exactly `δ₀` and
that every point of it satisfies `f(D x) > τ` by at least `(c − s) · (x − z)`. Interpret the gap `(c − s)` as the
defender's shortfall.

**Exercise 5.8.** Prove the shallow-boundary escape (Theorem 5.25) and then show its converse direction: if the
steep region is nonempty for some `K`, then `f` rises faster than `L` in some direction from `z`. Match your
argument to `persistence_implies_steep_direction` in `MoF_19`.

**Exercise 5.9.** Compute the grid cost `N^d` and the coverage fraction `r^d` for `N = 4`, `r = 1/4`, `d = 10`, and
`d = 30`. Verify numerically that a fixed defense budget of `10^6` patches is exhausted between these two
dimensions, and identify the critical dimension `d₀` predicted by `no_fixed_budget_defense`.

**Exercise 5.10.** Using `regular_value_boundary` (Theorem 5.29), show that a one-dimensional alignment surface with
nonvanishing derivative has an isolated (locally singleton) boundary. Then construct an `f` with a degenerate
critical point on its boundary whose level set `{f = τ}` contains an interval, showing that regularity is necessary
for isolation.

**Exercise 5.11.** From `ascent_direction_exists` (Theorem 5.31), prove that gradient ascent on a differentiable `f`
never halts except at a critical point, and connect this to `critical_point_iff_fderiv_eq_zero`. Then use Theorem
5.32 to show that among all unit-step attacks, the gradient step maximizes the immediate gain in `f`.

**Exercise 5.12.** Trace the full gradient chain (Theorem 5.35) on the affine surface `f(x) = ⟨w, x⟩` with
`‖w‖ = G`, against a `K`-Lipschitz defense. Determine exactly when `G > L(K+1)` fails and succeeds for `L = ‖w‖`,
and reconcile your answer with the worked corner example of Section 6 (why affine surfaces alone cannot be
persistently unsafe against their own Lipschitz constant).

**Exercise 5.13.** For transfer (Theorem 5.37), suppose two models are `δ`-close with `δ = 0.2`. An attacker holds a
source-model success with margin `m`. For which `m` is transfer guaranteed, and for which `m` might it fail?
Construct an explicit pair `f, g` with `|f − g| ≤ δ` and a point where transfer fails for `m < δ`, showing the
margin condition of `transfer_attack` is sharp.

**Exercise 5.14.** Using the hitting-time result (Theorem 5.43), compute the expected number of random trials to hit
a basin of probability `p = 10^-6`, and compare it to the step count of a gradient attack that gains `δ = 0.05` per
step from a start `s₀ = τ − 1`. Explain, in terms of `1/p` versus `(τ − s₀)/δ`, why gradient attacks dominate random
search when the basin is small.

**Exercise 5.15.** Assemble the master cost asymmetry (Theorem 5.50) from its pieces: attack budget `1/δ` (constant),
defense budget `N^d` (exponential), and the ratio `δ · N^d`. Prove the ratio exceeds any `R > 0` for large enough
`d`, matching `MASTER_THEOREM_cost_asymmetry`, and state precisely which quantity's independence from `d` is the
source of the asymmetry.

**Exercise 5.16.** (Harder.) Combine the optimal-defense dilemma (Theorem 5.51) with the coarea bound (Theorem 5.20)
to show that at the critical `K* = G/L − 1`, the failure band has width at least `G·δ` and volume at least
proportional to `G·δ/L` in one dimension. Then argue that no choice of `K` simultaneously drives both the persistent
cone measure and the band volume to zero when `G > L`, and interpret this as the quantitative form of the master
theorem's single surviving boundary point.

**Exercise 5.17.** (Open-ended.) The cost theory measures the attacker's budget in gradient steps and the defender's
in grid cells, two different units. Propose a common currency (for instance, model evaluations, or wall-clock
compute) in which both budgets can be expressed, and rederive the cost ratio in that currency. Does the asymmetry
survive the change of units? Identify which theorem of this chapter would need restating and which would carry over
unchanged.

**Exercise 5.18.** (Open-ended.) Every quantitative result here assumes a metric and a measure on behavior space. For
a discrete space of token sequences, neither is canonical. Speculate on what plays the role of the Lipschitz constant
`L`, the ball, and the coarea band in a discrete setting, and consult `MoF_12_Discrete` for one formalized answer.
Which of the cost-ratio conclusions do you expect to survive discretization, and which depend essentially on the
continuum?

**Exercise 5.19.** From the Markov basin bound (Theorem 5.52), derive an upper bound on the basin measure
`μ({f ≥ τ})` in terms of the average score `∫ f dμ` and `τ`, and contrast it with the lower bound from the coarea
band (Theorem 5.20). For the Gaussian annulus example with `f(x) = ‖x‖` under a standard Gaussian, estimate both
bounds and explain why the gradient attack ignores the smallness of the Markov upper bound. Relate the annulus
picture to why random search costs `1/p` while the gradient attack costs a constant.

**Exercise 5.20.** Using the running-maximum monotonicity and the pigeonhole step of Theorem 5.55, show that a
defense with `n` correction slots facing `n + 1` distinct attacks must leave at least one uncorrected, and that
over `T` turns the attacker's best score is nondecreasing. Then state the discrete crossing lemma (Theorem 5.56) as
a discrete intermediate value theorem and prove it by taking the largest safe index. Finally, explain in one
paragraph, without symbols, why the discrete trilemma and the diagonal of Chapter 1 are two proofs of one fact.
