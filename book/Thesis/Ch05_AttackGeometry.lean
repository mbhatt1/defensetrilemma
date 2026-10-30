import VersoManual
import Thesis.Ch01_Diagonal
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Geometry of Attacks" =>

The diagonal gives one thing and refuses the rest. It gives a bad point. It
never says how many there are, how large a region behaves badly, how a search
finds one, or what an adversary spends. Those questions are outside its
language: it speaks of surjections and fixed-point-free maps, not volume,
distance, or gradient.

Here the objects are real functions on real spaces: an _alignment deviation_ `f : X → ℝ`,
a threshold `τ`, and a metric. The tools are analysis and measure theory. No
result here is a diagonal argument; they are the intermediate value theorem, the
Lipschitz condition, a coarea inequality, concentration of measure, and
pigeonhole on grids.

The material follows the companion `ManifoldProofs` development, roughly four
hundred machine-checked results on Mathlib. Because that library is analytic and
the book's own package carries no Mathlib, this chapter states everything in
prose, tagged with the exact `MoF_*` name. Treat the citations as ground truth:
where the prose simplifies, the Lean does not.

One idea runs throughout. _Existence is qualitative; cost is quantitative._ The
earlier impossibility theorems say the boundary is there. These say how it is
shaped, how much room the unsafe region occupies, and how the price of attack
and defense scales. A deployment is not decided by whether a bad point exists,
since one always does, but by how expensive it is to live next to it.

# From the diagonal to the boundary

Fix a space `X` of behaviors, a continuous `f : X → ℝ` large when behavior is
far from acceptable, and a threshold `τ`. This triple is the entire setting.

*Definition 5.1 (Regions).* The _safe region_ is `{f < τ}`, the _vulnerability basin_
`{f > τ}`, the _boundary_ `{f = τ}`, the _failure manifold_ `{f ≥ τ}`. These are
`SafeRegion`, `UnsafeRegion`, `Boundary`, `FailureManifold` in
`MoF_01_Foundations`, with `space_partition`, `safe_unsafe_disjoint`, and
`failureManifold_eq_union` the immediate facts.

In Chapter 1 the boundary question was the index where a boolean verdict
flipped. Here it is a point where `f = τ`, neither safe nor unsafe. The diagonal
produced its witness by self-reference; this one comes from connectedness. Both
deliver an unavoidable point of failure, and the analytic one delivers it with
metric content.

*Remark 5.2.* Keep one picture: `f` is a landscape, the safe region the lowland below
sea level `τ`, the boundary the coastline. The questions here are geographic.
How much coastline? How steep the cliffs? Drop a random point: how likely near
the coast? The impossibility theorems say the coastline exists; the geometry
says how to sail it.

# Decision basins

*Theorem 5.3 (Basin openness).* _For continuous `f`, `{f > τ}` and `{f < τ}` are open;
`{f = τ}` and `{f ≤ τ}` are closed._

_Proof._ Preimages of open rays are open; the boundary is the preimage of a closed
singleton. ∎

This is `basin_isOpen` and `sublevel_isClosed` in `MoF_02_BasinStructure`, with
`safeRegion_isOpen`, `unsafeRegion_isOpen`, `boundary_isClosed` in `MoF_01`.
Unsafety is not razor-thin: it comes with room around it.

*Theorem 5.4 (Every unsafe point owns a ball).* _If `f p > τ` then some `r > 0` has
`B(p, r)` inside the basin._

_Proof._ The basin is open and contains `p`. ∎

`basin_contains_ball`. Continuity gives a ball of unknown size; Lipschitz
continuity, below, gives one of known size.

*Theorem 5.5 (Basins have positive measure).* _For any measure giving nonempty opens
positive mass, if some `f p > τ` then `μ{f > τ} > 0`._

_Proof._ The basin is open and nonempty. ∎

`basin_measure_pos`, with `basin_measure_ge_ball_pos` in
`MoF_Cost_02_BasinVolume`. This is the hinge of the cost story. A single unsafe
point is measure-zero and dismissible; positive measure is not. A random draw
has positive chance of landing there, and no finite set of safe examples
certifies the region away.

*Theorem 5.6 (Monotonicity in the threshold).* _If `τ₁ ≤ τ₂` then `{f > τ₂} ⊆ {f > τ₁}`
and the measures are ordered. Above the supremum the basin is empty; below the
infimum it is everything._

_Proof._ Raising the threshold removes points; measure is monotone. ∎

`basin_measure_monotone_threshold`, `basin_empty_above_sup`,
`basin_full_below_inf` in `MoF_Adv_10_MeasureBounds`. You can shrink the basin
by refusing more behaviors, but it shrinks continuously and never vanishes until
you have refused essentially everything. A threshold high enough to empty the
basin empties the product.

*Theorem 5.7 (Components are open and countable).* _On a locally connected space each
component of the basin is open; if second countable, there are countably many._

_Proof sketch._ Components of an open set in a locally connected space are open, and a
disjoint family of nonempty opens in a second countable space is countable. ∎

`basin_connected_components_open`, `basin_components_countable` in
`MoF_Adv_01_BasinConnectedness`, with `basin_connected_of_convex_domain` a
sufficient condition for one piece and `superlevel_disconnected_example` an `f`
whose basin splits. Real models are the second kind, which is why red-teaming
that finds one jailbreak family says little about the others.

_Worked example: the Gaussian bump._ On `ℝ^n` let `f(x) = M · exp(-‖x‖²/2)` with
`0 < τ < M`. The basin is the open ball of radius `√(2 ln(M/τ))`: open,
nonempty, positive measure, connected, shrinking continuously as `τ → M`. It
also previews the curse, since the ball's volume is a vanishing fraction of the
surrounding cube in high dimension, so a random draw almost never lands in it.

# The threshold-crossing theorem

*Theorem 5.8 (Threshold crossing, one dimension).* _For continuous `f : ℝ → ℝ` with
`f a < τ < f b`, some `c ∈ [a,b]` has `f c = τ`._

_Proof._ The IVT on a connected interval. ∎

`path_crosses_threshold` in `MoF_03_ThresholdCrossing`. Its elementariness is
the point: unavoidability of the boundary is the IVT in a safety costume.

*Theorem 5.9 (Crossing along a path).* _For continuous `γ` and `f` with
`f(γ a) < τ < f(γ b)`, some `c` has `f(γ c) = τ`._

_Proof._ Theorem 5.8 on the composite. ∎

`path_crosses_threshold_generic`. An attack is a path from safe to unsafe,
whether prompt edits, an embedding interpolation, or a gradient trajectory. If
it is continuous and succeeds, it passed through the boundary. There is a moment
in every successful attack when the behavior was exactly at threshold, which is
why the boundary, not the interior, is what a defense must control.

This also refutes the moat. For a continuous score, `f` takes every intermediate
value, so you cannot forbid a band of scores without forbidding behaviors that
legitimately produce them. The only genuine separator is the measure-zero level
set, and Theorem 5.20 shows even that thickens once the defender's uncertainty
is counted. There is no moat, only a coastline.

*Theorem 5.10 (No gap).* _On connected `X`, if a safe and an unsafe point exist then
`{f = τ}` is nonempty._

_Proof._ The reachable values form a connected subset of `ℝ` containing values on both
sides. ∎

`no_gap_theorem`, on `threshold_level_set_nonempty`. A designer might hope for a
model whose behaviors are all comfortably safe or comfortably unsafe with an
empty margin, so a crude classifier could separate them. Connectedness forbids
it.

*Theorem 5.11 (Separation is exactly the boundary).*
_`closure(Safe) ∩ closure(Unsafe) ⊆ Boundary`._

_Proof sketch._ If `f x > τ` a whole neighborhood is unsafe, contradicting `x` being a
limit of safe points; symmetrically below. ∎

`safe_unsafe_separated`. The boundary is the shared frontier where the regions
touch, and everything an attacker exploits and a defender guards lives on this
closed set.

*Theorem 5.12 (Defense fixes a boundary point).* _Let `X` be connected Hausdorff with
safe and unsafe points present, and `D` continuous and the identity on the safe
region. Then some boundary point `z` has `D z = z`, so `D` cannot make `z`
safe._

_Proof sketch._ The fixed-point set of a continuous self-map of a Hausdorff space is
closed, being the preimage of the diagonal, and contains the safe region hence
its closure. The safe region is open and not closed, since connectedness would
force it empty or everything, so its closure contains a boundary point, which is
a limit of safe points and therefore fixed. ∎

`master_theorem` in `MoF_MasterTheorem`, over the `ManifoldOfFailure` structure.
It does not say `D` fails everywhere, only that one boundary point is fixed and
unfixed. Upgrading that point to a region of positive measure is the work of the
quantitative theorems.

_Worked example: interpolating prompts._ A benign prompt at `f p = τ - 1` and a
jailbreak at `f q = τ + 1` are joined by a continuous path, so Theorem 5.9 gives
a prompt scored exactly at threshold: a marginal jailbreak where a vanishing
nudge tips it unsafe. That family is exactly what red teams hunt.

# Lipschitz control

`f` is _`L`-Lipschitz_ when `|f x - f y| ≤ L · dist(x,y)`. Networks with bounded
weights and Lipschitz activations are Lipschitz, with a constant that is finite
and estimable.

*Definition 5.13 (Robustness radius).* `robustnessRadius(f p, τ, L) = (f p - τ)/L`, in
`MoF_04_LipschitzBasin`.

*Theorem 5.14 (Lipschitz basin ball).* _If `f` is `L`-Lipschitz with `f p > τ`, the ball
of radius `(f p - τ)/L` around `p` lies inside the basin._

_Proof._ `|f p' - f p| ≤ L · dist < f p - τ`. ∎

`lipschitz_basin_ball`, with `basin_ball_subset`, `perturbation_stability`, and
`robustnessRadius_pos`. The radius is the margin divided by how fast `f` can
climb back down. This is a statement about the robustness of _attacks_: once
well inside the unsafe region an entire neighborhood is unsafe, so small changes
in phrasing do not rescue the model.

*Theorem 5.15 (Deeper points have larger basins).* _If `f p₁ ≤ f p₂`, both above `τ`,
their radii are ordered the same way._

_Proof._ `(v - τ)/L` increases in `v`. ∎

`robustnessRadius_monotone`. The more deviant the behavior, the more robust to
perturbation, which attackers exploit by pushing deep rather than stopping at
the first crossing.

*Theorem 5.16 (Smoother models, larger basins per peak).* _A smaller Lipschitz constant
gives a larger radius at fixed peak value._

_Proof._ `(f p - τ)/L` decreases in `L`. ∎

`smoother_functions_larger_basins` in `MoF_Adv_04_ModelScale`, with
`lipschitz_basin_component_width`. Smoothness is usually considered desirable
and is often enforced by regularization, but a smoother model has larger unsafe
basins per peak. Smoothness does not remove the danger; it spreads it, while
steepness concentrates it into thin spikes, harder to hit by chance and sharper
when hit.

Is the Lipschitz assumption fair? A large `L` shrinks the guaranteed ball, which
sounds like relief, but a large `L` is what a model needs to draw sharp narrow
basins, and a large local growth rate is what defeats the defense. A large
constant does not make a model safe; it makes the failures spiky, and spiky
failures are just as easy to hit by gradient, since the gradient is largest
where the surface is steepest.

*Theorem 5.17 (Oscillation needs steepness).* _If `f : [0,1] → ℝ` is `L`-Lipschitz with
`f 0 = f 1 = 0` and `f t = M > 0`, then `L ≥ 2M`._

_Proof._ `M ≤ L·t` and `M ≤ L·(1-t)`; add. ∎

`higher_lipschitz_more_oscillation`. Sharp transitions require a large `L`, and
a large `L` is what the cost theory charges for.

_Worked example: the linear ramp._ For `f(x) = ⟨w,x⟩ + b` with `‖w‖ = L` and `f p = τ + m`,
the guaranteed ball of radius `m/L` is tight: moving along `-w/‖w‖` decreases
`f` at maximal rate, so the ball is inscribed in the basin, kissing the boundary
at the foot of the perpendicular. Every later theorem about basin volume is a
version of inscribing balls like this.

# The coarea and cone bounds

*Definition 5.18 (The `ε`-band).* `coareaBand(f, τ, ε) = {τ - ε ≤ f ≤ τ}`, in
`MoF_17_CoareaBound`.

*Theorem 5.19 (Ball inside the band).* _If `f` is `L`-Lipschitz and some `c` has
`f c = τ - ε/2`, then `B(c, ε/(4L))` lies in the band._

_Proof._ Across the ball the value moves by less than `ε/4`. ∎

`lipschitz_ball_subset_band`; the centre sits mid-band so the ball cannot escape
either wall.

*Theorem 5.20 (Coarea volume lower bound).* _`μ(band) ≥ μ(B(c, ε/(4L)))`; in `ℝ` this is
`ε/(2L)`, and in `ℝ^n` it grows like `(ε/(4L))^n`._

_Proof._ Monotonicity under Theorem 5.19. ∎

`epsilon_band_volume_lower_bound`, with real and Euclidean specializations. The
centre is free on a connected space by the IVT (`exists_midpoint_for_band`),
making the argument unconditional (`epsilon_band_volume_pos_unconditional`). The
band always has positive, computably bounded measure: the boundary is not a
lonely level set but the spine of a slab.

*Remark 5.21.* A defender's classifier has an uncertainty band of width `ε`, and the true
behaviors falling in it occupy volume at least `ε/(2L)`. Sharpening shrinks it
linearly, which is progress, but never to zero while `ε > 0`.

*Definition 5.22 (Steep region).* `steepRegionR(f, τ, s, z) = {x | f x > τ + s·|x - z|}`,
in `MoF_18_ConeBound`, with `steepRegion` in `MoF_11_EpsilonRobust` and
`steepRegionRefined` in `MoF_20_RefinedPersistence`.

*Theorem 5.23 (Defense distortion bound).* _If `f` is `L`-Lipschitz, `D` is
`K`-Lipschitz, and `D z = z`, then `f(D x) ≥ f x - L(K+1)·dist(x,z)`._

_Proof._ `dist(D x, x) ≤ (K+1)·dist(x,z)`, and `f` changes by at most `L` times that. ∎

`defense_from_input_bound_R`. The compound `L(K+1)` is the defense's maximum
reach: how far below its input value it can pull the score. If `f` rises faster
in some direction, the defense loses.

*Theorem 5.24 (Cone measure bound).* _If `f z = τ`, `D z = z`, and `f(z + t) ≥ τ + c·t`
on `(0, δ₀)` with `c > L(K+1) =: s`, then that interval lies in the steep
region, the steep region has measure at least `δ₀`, and every steep point stays
unsafe after defense._

_Proof._ `f x ≥ τ + c·t > τ + s·t` gives the inclusion and the measure; Theorem 5.23 then
gives `f(D x) > τ + s|x-z| - s|x-z| = τ`. ∎

`cone_measure_bound`, assembling `cone_segment_in_steep_region`,
`steep_region_contains_Ioo`, `steep_region_measure_pos`, and
`steep_region_measure_lower_bound`. Chapter 1 gave one surviving query, the
master theorem one surviving boundary point; this gives an entire cone of
positive measure that remains unsafe after the defense has done its best.

*Theorem 5.25 (Shallow boundaries can be defended).* _If `f x ≤ f z + L·dist(x,z)`, the
steep region is empty for every `K ≥ 0`._

_Proof._ `f x ≤ τ + L·dist ≤ τ + L(K+1)·dist`. ∎

`shallow_boundary_no_persistence` in `MoF_19_OptimalDefense`. The two theorems
draw a sharp line: steep boundaries carry persistent positive-measure failure no
defense removes, shallow ones do not, and whether a real model is steep or
shallow at its boundary is the most important quantitative fact about its
defensibility.

_Worked example: a corner in the score._ With `f(x) = τ + G·x` for `x ≥ 0`, so
`L = G`, persistence needs `K + 1 < 1`, impossible. The corner is not steep
_relative to its own Lipschitz constant_. Genuine persistence needs `f` to rise
near `z` faster than elsewhere, which is the regime the gradient chain reaches
through `‖∇f(z)‖`.

# Dimensional scaling

*Theorem 5.26 (Grid explosion).* _Discretizing `d` axes into `N` bins gives `N^d` cells,
unbounded for `N ≥ 2`; covering needs at least `N^d` queries and exceeds any
fixed budget._

_Proof._ The grid has cardinality `N^d ≥ 2^d`, and covering is a surjection onto it. ∎

`grid_card`, `grid_exponential_growth`, `queries_lower_bound_surjective`,
`no_fixed_budget_defense`. Exhaustive defense is not expensive; it is impossible
at any budget.

*Theorem 5.27 (Coverage collapse).* _A patch of relative radius `r < 1` covers fraction
`r^d → 0`, and covering a fixed fraction needs `(1/r)^d → ∞` patches._

_Proof._ Relative volume is the product of side fractions. ∎

`coverage_fraction_vanishes`, `defense_patch_shrinks`, `exponential_base`,
bundled as `DimensionalCurse`. Each thing the defender builds covers a fraction
shrinking exponentially with dimension. The attacker needs one point; the
defender needs almost all.

*Theorem 5.28 (Boundary structure).* _The boundary is closed, compact on compacta, empty
exactly when `f` never equals `τ`, nonempty on a connected space when `f`
straddles `τ`, and equal to `f⁻¹({τ})`._

_Proof._ Theorem 5.3 plus the IVT cases. ∎

`boundary_is_closed`, `boundary_is_compact_on_compact`,
`boundary_empty_of_no_crossing`, `boundary_nonempty_connected`,
`boundary_is_preimage_singleton`.

*Theorem 5.29 (Regular points are isolated in one dimension).* _With nonzero derivative
at a boundary point, some punctured neighborhood has `f ≠ τ`._

_Proof sketch._ A nonzero derivative makes `f` strictly monotone near `z`. ∎

`regular_value_boundary`, `boundary_locally_finite_1d`. Where regular, the
boundary is thin and well-behaved; where the gradient degenerates it can thicken
and fold, and whether real boundaries are regular or fractal is an open
empirical question.

*Theorem 5.30 (Complexity and crossings).* _A constant model has a trivial basin, a
monotone model crosses at most once, and oscillation with many components
requires `L ≥ 2M` to reach height `M`._

_Proof._ The monotone case squeezes `f` to `τ` between crossings; the rest is
Theorem 5.17. ∎

`constant_model_no_basin_empty`, `constant_model_no_basin_univ`,
`low_complexity_few_crossings_1d`, `higher_lipschitz_more_oscillation`. A bigger
model is not automatically safer geometry; it is capable of a more complicated
failure landscape.

_Worked example: random points in the cube._ In high dimension almost all volume
is near the surface and distances concentrate. The attacker sampling at random
lands in the peripheral bulk where an appreciable basin is found; the defender
watches each patch cover an `r^d` sliver of that same bulk.

# Gradient attacks

*Theorem 5.31 (An ascent direction exists).* _If `f` is differentiable at `x` with
`f' ≠ 0`, some direction and step raise `f`._

_Proof sketch._ Pick `v` with `f' v > 0` and restrict to the line. ∎

`ascent_direction_exists`, `multivariate_ascent_direction` in
`MoF_10_GradientAttack`, on `discrete_ascent_improvement` and
`hasFDerivAt_line_restrict`. This is the licence for gradient-based adversarial
methods: away from critical points there is always a way to raise the score, and
critical points are where the gradient vanishes
(`critical_point_iff_fderiv_eq_zero`).

*Theorem 5.32 (The gradient is steepest).* _Among unit directions `⟨g, v⟩` is maximized
at `g/‖g‖`, giving directional derivative `‖g‖`._

_Proof._ Cauchy-Schwarz. ∎

With `fderiv_apply_eq_inner_gradient` and `real_inner_self_eq_norm_sq'`. This is
why attacks follow the gradient: it reaches the boundary in the fewest steps.

*Theorem 5.33 (Near-optimal direction).* _If `‖f'‖ > c` at `z`, some unit `v` has
`f' v > c`._

_Proof sketch._ Normalize a vector of norm below `1` on which `f'` exceeds `c`. ∎

`near_optimal_direction`.

*Theorem 5.34 (Derivative forces local growth).* _If `f z = τ` and `f' v > c` for a unit
`v`, then `f(z + tv) > τ + c·t` for small `t > 0`._

_Proof sketch._ `g(t) = f(z + tv) - τ - ct` has `g(0) = 0` and positive derivative. ∎

`deriv_implies_local_growth`, with `deriv_implies_strict_local_growth`.

*Theorem 5.35 (Gradient chain to persistence).* _If `f` is differentiable at a boundary
point with `‖f'‖ > ℓ(K+1)`, the steep region is nonempty and `{f(D x) > τ}` has
positive measure._

_Proof sketch._ Theorem 5.33 gives a direction beating `ℓ(K+1)`, Theorem 5.34 turns it
into local growth placing a point in the steep region, and Theorem 5.24 upgrades
that to a positive-measure surviving set. ∎

`gradient_norm_implies_steep_nonempty`, `gradient_chain_persistent_unsafe`,
invoking `persistent_unsafe_refined`. Measure the gradient at the boundary; if
it beats the defense's smoothing budget, following it reaches behaviors the
defense cannot save, not one but a set of positive volume. The single number
`‖∇f(z)‖` decides whether the model is persistently attackable. This is
`transversality_from_deriv` in its sharpest form.

*Remark 5.36.* Chapter 1's attack was a construction with no notion of effort. The
gradient attack is a process with a step count, `(τ - f(start))/gain`, which is
a real budget. Both reach the same boundary; only the second has a price tag.

# Transferability

Say `f` and `g` are _δ-close_ when `|f x - g x| ≤ δ` everywhere.

*Theorem 5.37 (Transfer with margin).* _If `f` and `g` are δ-close and `f p > τ + δ`,
then `g p > τ`._

_Proof._ `g p ≥ f p - δ > τ`. ∎

`transfer_attack` in `MoF_06_Transferability`, restated as
`transfer_margin_needed`. The margin is the toll for crossing between models: an
attack merely clearing `τ` on the source may fail on the target, one clearing `τ + δ`
transfers. Attackers know this when they over-optimize, and over-optimization by
`δ` is precisely what buys transfer.

*Theorem 5.38 (Basin containment).* _`{f > τ + δ} ⊆ {g > τ}`, with equality of basins at
`δ = 0`._

_Proof._ Theorem 5.37 pointwise. ∎

`basin_containment`, `identical_models_identical_basins`,
`zero_distance_free_transfer`, with the two-sided `pointwise_sandwich`.

*Theorem 5.39 (Transfer is computationally free).* _Given δ-closeness and a source
success with margin `δ`, the target success follows with zero target
evaluations._

_Proof._ No term in Theorem 5.37's proof evaluates `g` at a new point. ∎

`transfer_is_free` in `MoF_Cost_07`. An attacker who breaks one model gets every
δ-close model free. Model families trained on similar data, or fine-tunes of a
common base, are δ-close for small `δ`, so one attack sweeps the family, and
closed deployment of a model whose base is public offers less protection than it
appears.

A defense classifier is a function on the same space, so to the extent it agrees
with what it guards it inherits its vulnerabilities, and to the extent it
disagrees it misclassifies safe behavior. Closeness buys agreement at the price
of shared failure; distance buys independence at the price of collateral
refusals.

*Theorem 5.40 (Empirical closeness underestimates).* _An empirical maximum disagreement
is at most the true `δ`, and more samples raise it._

_Proof._ A maximum of quantities bounded by `δ` is bounded by `δ`. ∎

`estimation_cost`, `more_samples_better_estimate`. The estimation cost is paired
evaluations, not an exponential quantity: transfer is cheap to plan and free to
execute.

_Worked example: a fine-tune and its base._ If a light fine-tune changed the
score by at most `δ = 0.1`, an attack with margin `0.15` transfers to the base
and one with margin `0.05` need not. Safety fine-tuning with small `δ` leaves
the base model's attacks almost entirely intact.

# The cost theory

The `MoF_Cost` series builds budgets in ten layers, and the punchline is one
asymmetry: attack cost stays bounded while defense cost explodes with dimension.

*Theorem 5.41 (Ball volume).* _An open ball of positive radius has positive volume,
monotone in the radius; in `ℝ` it is `2r`._

_Proof._ Nonempty opens have positive Lebesgue measure. ∎

`ball_measure_pos`, `ball_measure_mono`, `ball_measure_scale` in
`MoF_Cost_01_BallVolume`.

*Theorem 5.42 (Basin volume lower bound).* _The basin contains the robustness ball, so
its measure is at least the ball's; for merely continuous `f` it is still
positive._

_Proof._ Theorem 5.14 as a subset relation, plus Theorem 5.5. ∎

`robustness_ball_subset_basin`, `basin_measure_ge_ball`,
`basin_measure_ge_ball_pos`, with `basin_measurableSet`. The attacker's target
is a ball of volume at least `(margin/L)^n` times a dimensional constant.

*Theorem 5.43 (Random search hitting time).* _With per-trial hit probability `p`, the miss
probability `(1-p)^n` decreases to zero and the expected number of trials is
`1/p`._

_Proof sketch._ Powers of a number below one vanish; the geometric series sums to
`1/p`. ∎

`miss_probability_vanishes`, `hit_probability_tends_to_one`,
`geometric_sum_le_inverse`, `tsum_geometric_eq_inv` in
`MoF_Cost_03_HittingTime`. When `p` is a constant fraction this is cheap; the
defender's only real hope is that `p` is exponentially small in high dimension,
which is where gradient attacks earn their keep by replacing `1/p` with a linear
step count.

*Theorem 5.44 (Estimation margin).* _If `|f̂ - f| ≤ ε`, then `f̂ x > τ + ε` implies
`f x > τ` and `f̂ x < τ - ε` implies `f x < τ`; the undecidable band is `{|f̂ - τ| ≤ ε}`._

_Proof._ Rearranging the absolute-value inequality. ∎

`estimation_error_bound_unsafe`, `estimation_error_bound_safe`,
`estimation_uncertain_band`, `estimation_band_shrinks` in
`MoF_Cost_04_Concentration`. That band is exactly the coarea band: the band the
classifier cannot resolve is the band the geometry says has positive volume.

*Theorem 5.45 (Lipschitz interpolation).* _Holding the error below `ε` throughout
`[0,1]^d` needs samples no farther than `ε/L` apart, hence on the order of
`(L/ε)^d`._

_Proof._ The Lipschitz condition plus a covering count. ∎

`lipschitz_estimation_error`, `estimation_improves_with_distance`,
`total_estimation_budget` in `MoF_Cost_09_LipschitzEstimation`, with
`sup_norm_triangle` and `n_samples_coverage`. The defender's estimation problem
inherits the curse directly, and concentration works against it: samples spread
thin, so the interpolation bound is loose exactly where it matters.

*Theorem 5.46 (Attack cost).* _An attack gaining `δ` per step on a score in `[0,1]`
reaches `τ` from `s₀` in at most `⌈(τ - s₀)/δ⌉ + 1` steps and takes at most
`⌈1/δ⌉` useful steps._

_Proof sketch._ After `n` steps the score is at least `s₀ + nδ`, and it cannot exceed
`1`. ∎

`attack_value_after_n_steps`, `steps_to_threshold`, `attack_cost_upper_bound`,
`total_attack_cost` in `MoF_Cost_05_AttackCost`, with `attackSeq_convergent` and
`finite_steps_bound`. The budget is `1/δ`, independent of dimension, because the
attacker follows a one-dimensional trajectory and each step gains a fixed amount
regardless of how many dimensions surround the path.

*Theorem 5.47 (Defense cost).* _Covering with patches of relative radius `r < 1` needs on
the order of `(1/r)^d` patches; any budget has a critical dimension._

_Proof._ Fraction `α` needs `α·(1/r)^d` patches. ∎

`patches_needed`, `defense_cost_exponential`, `critical_dimension` in
`MoF_Cost_06_DefenseCost`.

*Theorem 5.48 (Transfer cost).* _Porting an attack across δ-close models costs zero target
queries, and estimating `δ` grows with precision, not dimension._

_Proof._ Theorems 5.39 and 5.40. ∎

`MoF_Cost_07_TransferCost`. Transfer adds essentially nothing to the attack
budget while multiplying its reach across a family.

*Definition 5.49 (Cost ratio).* `costRatio(N, d, δ) = N^d · δ`, in `MoF_Cost_08_CostRatio`,
bundled as `unifiedCostRatio` on `CostParameters` in
`MoF_Cost_10_UnifiedTheory`, with `unifiedCostRatio_eq`.

*Theorem 5.50 (Cost asymmetry, master theorem).* _For fixed `N ≥ 2` and `δ > 0` the ratio
is positive, increasing, and divergent in `d`, exceeding any `R` beyond a
critical dimension. The attacker's budget is dimension-independent; the
defender's is exponential._

_Proof sketch._ A positive constant times an exponential in `d`; the attack budget `1/δ`
contains no `d`. ∎

`cost_ratio_tends_to_infinity`, `cost_ratio_exceeds_any_bound`,
`attacker_advantage_quantified`, `MASTER_THEOREM_cost_asymmetry`, with
`attack_budget_dimension_independent` and `defenseBudget_exponential`. As a
concrete anchor, `two_dimension_ratio` gives `6.25` already at `d = 2`, `N = 25`,
`δ = 0.01`.

This is the chapter's quantitative summary. The boundary exists, is populated by
a positive-measure region, is found at a dimension-independent cost, and is
covered only at a dimension-exponential one. The ratio diverges and no budget
closes the gap.

*Theorem 5.51 (No `K` wins).* _Either `G > L(K+1)` and a persistent unsafe region of
positive measure survives, or `L(K+1) ≥ G` and the failure band has width at
least `G·δ`. For `G > L` the critical `K* = G/L - 1` is where the modes trade
off exactly and neither horn is escapable; for `G ≤ L` the boundary is shallow
and defensible._

_Proof sketch._ A case split on one real comparison. Increasing `K` strictly increases
`L(K+1)` (`defense_band_monotone`), flipping the first horn into the second with
equality at `K*` (`optimalK_critical`), and both horns are realized for `G > L`
(`defense_dilemma_both_realizable`). ∎

`defense_cannot_win`, `optimal_K_exists`, `complete_defense_characterization` in
`MoF_19_OptimalDefense`. A gentle defense leaves persistent cones; an aggressive
one smears the failure band wide, distorting behavior over a region growing
linearly in `K`. At `K*` the defender has minimized total damage but not
eliminated it.

_Worked example: the cost ratio._ With `d = 20`, `N = 10`, `δ = 0.05`, the
attacker pays about twenty steps and the defender `10^20` cells. Double the
dimension and the attacker still pays twenty steps while the defender pays
`10^40`. Nothing the defender does to `N`, `r`, or `K` touches the exponential
in `d`.

The one honest pushback is the word "effective": the exponent is the dimension
of the manifold the attack actually explores, and if that is low the ratio is
manageable. The cost theory does not measure it for you; it tells you that this
one number, not model size or defender cleverness, decides the contest.

# Concentration of measure

*Theorem 5.52 (Markov bound on the basin).* _For integrable `f ≥ 0`,
`μ{f ≥ ε} ≤ (1/ε)∫f dμ`._

_Proof._ The integrand is at least `ε` on `{f ≥ ε}`. ∎

`markov_real_basin` in `MoF_Adv_10_MeasureBounds`. A model whose average
deviation is small cannot have a large high-deviation basin, which sounds like
comfort but sets a floor, because the average is a property of the whole model
and lowering it means changing the model everywhere at once.

_The concentration phenomenon._ On the sphere or under a Gaussian in `ℝ^n`, an
`L`-Lipschitz `f` deviates from its median by more than `t` with probability at
most about `2exp(-ct²/L²)`: it is nearly constant across almost all of a
high-dimensional space. This is Lévy-Milman-Talagrand concentration, whose
consequences are exactly the cost asymmetries the library proves.

Concentration and the curse are the same fact. With `τ` above the median the
basin is the far tail, exponentially small in `(τ - m)²/L²` — good for the
defender in that a random behavior is almost never unsafe, catastrophic in that
Theorem 5.5 still guarantees the tail is nonempty, and the gradient chain skips
the `1/p` wait by climbing straight to it. Concentration hides the basin from
random draws and does nothing to hide it from gradients.

*Theorem 5.53 (Positive-measure failure band).* _On a connected Hausdorff metric space
with a positive-on-opens measure, `L`-Lipschitz `f`, a `K`-Lipschitz defense
fixing the safe region, and a transverse boundary point, the set `{f(D x) > τ}`
has strictly positive measure._

_Proof sketch._ Transversality places a point in the steep region, distortion shows steep
points stay unsafe, and the steep region is open and nonempty. ∎

`epsilon_robust_impossibility`, `positive_measure_failure_band`,
`persistent_unsafe_region` in `MoF_11_EpsilonRobust`. This is the strongest form
of the defense impossibility here, giving a surviving set of positive measure in
full generality under honest Lipschitz hypotheses on both model and defense.

*Remark 5.54 (The two faces).* Toward the defender, concentration says samples spread thin
and the nearest sample is far, so the interpolation bound is loose everywhere.
Toward the attacker it says the space is one undifferentiated bulk where a
Lipschitz score is nearly constant, so a gradient points reliably toward the
rare tail. The defender sees a space too big to cover; the attacker sees one too
smooth to hide the exit.

_Worked example: the Gaussian annulus._ Under a standard Gaussian, `‖x‖`
concentrates around `√n` in a window of width about `1`, so almost all mass sits
in a thin annulus. Take `f(x) = ‖x‖`, `1`-Lipschitz, and `τ = √n + 3`. The
basin's mass is on the order of `exp(-9c)`, independent of `n`, so random search
costs a large fixed number.

# Iterated and discrete attacks

*Theorem 5.55 (The attacker's running edge).* _The running maximum of scores is monotone
nondecreasing. Under capacity parity, a defense with a fixed number of
correction slots facing one more configuration must collapse two attacks to one
output. Over `T` turns the defense reveals at least `T` classifications._

_Proof sketch._ A supremum over a growing set is nondecreasing
(`running_max_monotone`); the rest is pigeonhole (`one_more_attack_overwhelms`)
iterated to a permanent margin (`attacker_permanent_edge`), with each probe
leaking a classification (`defense_leaks_per_turn`). ∎

In `MoF_13_MultiTurn`, with `multi_turn_impossibility` and
`boundary_points_accumulate`. The attacker has a ratchet: each turn can only
improve the best result, each probe extracts boundary information, and boundary
points accumulate. A defense holding for one turn need not hold for a hundred,
which is the formal shadow of long conversations eroding guardrails.

*Theorem 5.56 (Discrete crossing and the discrete trilemma).* _On a finite chain with
`f 0 < τ` and `f(n+1) ≥ τ` there is an adjacent straddling pair. A defense
fixing every safe point fixes such a crossing. More abstractly, for any unsafe
`u`, either `D` leaves `u` unsafe or `D` fails to be the identity where needed,
and a verdict both complete and injective cannot exist on a space rich enough to
encode its own decisions._

_Proof sketch._ Take the largest index with `f i < τ` (`discrete_ivt`); the rest is
`discrete_defense_boundary_fixed`, `discrete_trilemma`,
`injectivity_forces_incompleteness`, `completeness_forces_noninjectivity`. ∎

In `MoF_12_Discrete`. The last clause is where the geometry rejoins the
diagonal: pigeonhole rather than connectedness, but the same conclusion. The
continuum route reaches the boundary by connectedness, the discrete route by
counting, the self-referential route by diagonalization. Three proofs, one
boundary.

*Remark 5.57.* Chapter 1 built a query no boolean verdict answers by self-reference;
`discrete_trilemma` builds an unsafe point no utility-preserving defense
corrects, by order and counting. Both are instances of one pattern: a system
asked to classify a domain it is embedded in must leave a witness uncovered.
This chapter spent its length measuring that witness.

# The two halves, joined

The diagonal proves existence and nothing more, indifferent to quantity, cost,
and dimension. That indifference is its strength and its limit.

This chapter proves the quantitative shape of the same failure: the boundary has
positive-measure thickness, carries a persistent unsafe cone against any
defense, is reachable at a dimension-independent cost, and is coverable only at
a dimension-exponential one. Where the diagonal says a bad point exists, the
geometry says a region of bad points exists, cheap to enter and expensive to
seal, with the gap growing without bound.

A practitioner who absorbed only the diagonal might hope the bad point is rare,
hard to find, or easy to patch; the geometry closes each hope. One who absorbed
only the cost theory might think the problem is merely hard; the diagonal closes
that, since the boundary is not hard to remove but impossible to remove.

# Historical notes

The IVT underlying the crossing results is Bolzano's, and reading the boundary
as an unavoidable attack surface is the organizing idea of `ManifoldProofs`. The
covering-number form of the curse is standard in nonparametric statistics.
Concentration of measure is due in modern form to Lévy, Milman, and Talagrand,
and its adversarial reading is the contribution of the cost layers.
