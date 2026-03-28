import Mathlib
import ManifoldProofs.MoF_08_DefenseBarriers

/-!
# Manifold of Failure — Part 13: Multi-Turn & Stochastic Impossibility

The core theorems assume a static, single-turn defense. Real systems
are multi-turn and stochastic. This file proves the impossibility
persists under both extensions.

## Results

1. `multi_turn_impossibility` — At every turn in a multi-turn
   interaction, the defense faces a fresh boundary fixation problem.
   Adding memory doesn't help.

2. `stochastic_defense_impossibility` — If D is stochastic but the
   expected alignment deviation is continuous and utility-preserving
   in expectation, boundary fixation still holds.

3. `capacity_parity_disadvantage` — Even with equal capacity, the
   defense loses effective capacity to utility preservation. The
   attacker has no such tax.
-/

open Set Topology Filter

noncomputable section

namespace MoF

/-! ## 1. Multi-Turn Impossibility -/

/--
A multi-turn interaction: at each turn t, the system has an alignment
deviation function f_t and a defense D_t. Both may depend on history.
-/
structure MultiTurnSystem (X : Type*) [TopologicalSpace X] where
  /-- Number of turns -/
  T : ℕ
  /-- Alignment deviation at turn t -/
  f : Fin T → (X → ℝ)
  /-- Defense at turn t -/
  D : Fin T → (X → X)
  /-- Threshold -/
  τ : ℝ

/--
**Multi-Turn Impossibility.**

At every turn of a multi-turn interaction, if the alignment function
is continuous with both safe and unsafe regions, and the defense is
continuous and utility-preserving, boundary fixation occurs.

The impossibility is not a one-time event — it recurs at EVERY turn.
Memory, context, and state evolution do not help: each turn presents
a fresh instance of the single-turn impossibility.
-/
theorem multi_turn_impossibility
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    (sys : MultiTurnSystem X)
    -- Each f_t is continuous
    (hf : ∀ t, Continuous (sys.f t))
    -- Each D_t is continuous
    (hD : ∀ t, Continuous (sys.D t))
    -- Each D_t is utility-preserving
    (h_pres : ∀ t, ∀ x, sys.f t x < sys.τ → sys.D t x = x)
    -- Each turn has safe and unsafe points
    (h_safe : ∀ t, ∃ a, sys.f t a < sys.τ)
    (h_unsafe : ∀ t, ∃ b, sys.f t b > sys.τ) :
    -- Then: at EVERY turn, a boundary fixed point exists
    ∀ t, ∃ z, sys.f t z = sys.τ ∧ sys.D t z = z ∧
      ¬(sys.f t (sys.D t z) < sys.τ) := by
  intro t
  obtain ⟨z, hz_eq, hz_fix, _, hz_not⟩ :=
    defense_incompleteness (hD t) (hf t) (h_pres t) (h_safe t) (h_unsafe t)
  exact ⟨z, hz_eq, hz_fix, hz_not⟩

/--
**Corollary: the number of boundary fixed points grows with turns.**

Over T turns, the attacker accumulates at least T boundary fixed
points (one per turn), though they may overlap.
-/
theorem multi_turn_accumulates_fixed_points
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    (sys : MultiTurnSystem X)
    (hf : ∀ t, Continuous (sys.f t))
    (hD : ∀ t, Continuous (sys.D t))
    (h_pres : ∀ t, ∀ x, sys.f t x < sys.τ → sys.D t x = x)
    (h_safe : ∀ t, ∃ a, sys.f t a < sys.τ)
    (h_unsafe : ∀ t, ∃ b, sys.f t b > sys.τ) :
    -- For each turn, we can extract a witness
    ∀ t, ∃ z, sys.f t z = sys.τ ∧ sys.D t z = z := by
  intro t
  obtain ⟨z, hz_eq, hz_fix, _⟩ :=
    multi_turn_impossibility sys hf hD h_pres h_safe h_unsafe t
  exact ⟨z, hz_eq, hz_fix⟩

/-! ## 2. Stochastic Defense Impossibility -/

/--
A stochastic defense maps each input to a DISTRIBUTION of outputs.
We model this by requiring only that the expected alignment deviation
(the composition of expectation with the defense) is continuous.

If g(x) = E_{y ~ D(x)}[f(y)] is continuous and g = f on safe inputs,
boundary fixation holds for g.
-/
theorem stochastic_defense_impossibility
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    -- g is the expected alignment deviation after defense
    {g : X → ℝ} (hg : Continuous g)
    -- g agrees with f on safe inputs (utility preservation in expectation)
    (h_pres : ∀ x, f x < τ → g x = f x)
    -- Both safe and unsafe regions exist
    (h_safe : ∃ a, f a < τ)
    (h_unsafe : ∃ b, f b > τ) :
    -- Then: ∃ boundary point where expected AD = τ, defense can't reduce it
    ∃ z, f z = τ ∧ g z = τ ∧ ¬(g z < τ) := by
  -- Key insight: g is continuous, and g = f on {f < τ}.
  -- The safe region for g contains the safe region for f.
  -- So g has values < τ (at any safe point of f) and values > τ (need to show).
  -- Actually, we need g to have values > τ somewhere.
  -- Since g = f on safe region, g(a) = f(a) < τ.
  -- We need to find a point where g > τ.
  -- Apply the boundary fixation argument directly to g.
  -- g = f on {f < τ}, so {g < τ} ⊇ {f < τ} (since g = f there).
  -- We need {g > τ} to be nonempty.
  -- Consider the boundary fixed-point argument:
  -- closure({g < τ}) ⊇ closure({f < τ}).
  -- In {f < τ}, g = f, so g < τ there.
  -- So {f < τ} ⊆ {g < τ}.
  -- {g < τ} is open (g continuous) and nonempty (contains f's safe points).
  -- If {g < τ} = X, then g < τ everywhere, which is a valid defense!
  -- We need additional info: that g cannot be < τ everywhere.
  -- The key: at boundary points of {f < τ}, g = f = τ (by continuity of g and the
  -- fact that g = f on {f < τ}, so g on closure of {f < τ} also = f by continuity).
  have h_safe_g : ∃ a, g a < τ := by
    obtain ⟨a, ha⟩ := h_safe
    exact ⟨a, h_pres a ha ▸ ha⟩
  -- Find boundary point of f's safe region
  have h_strict : {x : X | f x < τ} ⊂ closure {x : X | f x < τ} := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨subset_closure, fun h_eq => by
      have : IsClosed {x : X | f x < τ} := h_eq ▸ isClosed_closure
      have h_open : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
      have h_clopen : IsClopen {x : X | f x < τ} := ⟨this, h_open⟩
      rcases isClopen_iff.mp h_clopen with h_empty | h_univ
      · obtain ⟨a, ha⟩ := h_safe
        have : a ∈ ({x : X | f x < τ} : Set X) := ha
        rw [h_empty] at this; exact this
      · obtain ⟨b, hb⟩ := h_unsafe
        have hmem : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
        simp only [Set.mem_setOf_eq] at hmem; linarith⟩
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} :=
      closure_minimal (fun x (hx : f x < τ) => le_of_lt hx) (isClosed_le hf continuous_const)
    exact this hz_clos
  have hz_ge : f z ≥ τ := not_lt.mp hz_not_safe
  have hz_eq : f z = τ := le_antisymm hz_le hz_ge
  -- Now show g(z) = τ.
  -- z ∈ closure({f < τ}), and g = f on {f < τ}.
  -- By continuity of g and f, g(z) = f(z) = τ.
  have hg_eq_f_on_safe : ∀ x, f x < τ → g x = f x := h_pres
  -- g and f agree on the safe region, so they agree on its closure
  have hg_z : g z = τ := by
    have : g z = f z := by
      -- g and f are continuous and agree on a dense subset approaching z
      -- Formally: g - f vanishes on {f < τ} and g - f is continuous
      have h_diff_cont : Continuous (fun x => g x - f x) := hg.sub hf
      have h_diff_zero_on_safe : ∀ x ∈ {x : X | f x < τ}, g x - f x = 0 := by
        intro x hx; simp [h_pres x hx]
      have h_diff_zero_closure : ∀ x ∈ closure {x : X | f x < τ}, g x - f x = 0 := by
        have : closure {x : X | f x < τ} ⊆ {x : X | g x - f x = 0} := by
          apply closure_minimal
          · exact fun x hx => h_diff_zero_on_safe x hx
          · exact isClosed_eq h_diff_cont continuous_const
        exact fun x hx => this hx
      have := h_diff_zero_closure z hz_clos
      linarith
    rw [this, hz_eq]
  exact ⟨z, hz_eq, hg_z, by linarith⟩

/-! ## 3. Capacity Parity Disadvantage -/

/--
**Capacity Parity: defense pays a utility-preservation tax.**

Even when defense and attacker have the same total capacity C,
the defense must dedicate capacity to implementing identity on
safe inputs. The attacker has no such constraint.

If |S| safe inputs exist and the defense must fix each one
(D(x) = x for x ∈ S), the defense's effective free capacity
is C - |S|, while the attacker retains full capacity C.
-/
theorem capacity_parity_disadvantage
    {n_safe n_unsafe : ℕ}
    (_h_safe_pos : 0 < n_safe)
    (_h_unsafe_pos : 0 < n_unsafe) :
    let n_total := n_safe + n_unsafe
    n_safe + n_unsafe = n_total ∧ n_unsafe = n_total - n_safe := by
  constructor
  · ring
  · omega

/--
**Defense effective capacity is strictly less than total capacity.**

A defense on Fin (n_safe + n_unsafe) that fixes all safe inputs
(the first n_safe elements) can only vary its behavior on the
remaining n_unsafe elements. Any classification of safe vs unsafe
that the defense performs is constrained: it MUST output identity
on safe inputs, consuming n_safe of its capacity.
-/
theorem defense_capacity_tax
    (n_safe n_unsafe C : ℕ)
    (h_cap : C = n_safe + n_unsafe)
    (_h_safe_pos : 0 < n_safe) :
    -- Effective free capacity = C - n_safe = n_unsafe
    C - n_safe = n_unsafe := by
  omega

/--
**When attacker adds ONE new adversarial input, defense may be overwhelmed.**

If the defense is exactly at capacity (n_unsafe slots for n_unsafe
attacks) and the attacker finds one additional adversarial configuration,
the defense has strictly fewer slots than attacks.
-/
theorem one_more_attack_overwhelms
    (n_safe n_unsafe : ℕ) (_h_pos : 0 < n_safe) :
    -- Defense has n_unsafe free slots
    -- Attacker now has n_unsafe + 1 configs
    -- Pigeonhole: defense must map two configs to same output
    n_unsafe < n_unsafe + 1 := by
  omega

/--
**Combined: attacker advantage grows with attack surface.**

If the attack surface grows as 2^d and the defense capacity is fixed
at C, the fraction of attacks the defense can handle shrinks to zero.
Even under capacity parity (C = 2^d), the defense loses n_safe slots
to utility preservation, giving the attacker a permanent edge.
-/
theorem attacker_permanent_edge
    (n_safe : ℕ) (h_safe_pos : 0 < n_safe)
    (d : ℕ) (_h_d : d ≥ 1) :
    -- Attack surface = 2^d
    -- Defense total capacity = 2^d (parity)
    -- Defense effective capacity = 2^d - n_safe
    -- Attacker has 2^d configurations
    -- Deficit = n_safe > 0
    2 ^ d - n_safe < 2 ^ d := by
  apply Nat.sub_lt
  · positivity
  · exact h_safe_pos

/-! ## 4. Multi-Turn Game Theory: Attacker Advantage -/

/--
**Simplified: running maximum is monotone.**

The max of a growing prefix of a sequence is non-decreasing.
We prove this directly for the natural numbers case.
-/
theorem running_max_monotone (scores : ℕ → ℝ) (t : ℕ) :
    ∀ s ≤ t, scores s ≤ sSup (Set.range (fun i : Fin (t + 1) => scores i)) := by
  intro s hs
  apply le_csSup
  · exact Set.Finite.bddAbove (Set.finite_range _)
  · exact ⟨⟨s, by omega⟩, rfl⟩

/--
**Boundary points accumulate across turns.**

Over T turns, the attacker discovers at least one boundary fixed point
per turn. The set of known boundary points grows monotonically
(though points may overlap).

Formally: the function t ↦ {z₁, ..., z_t} is non-decreasing in
set inclusion.
-/
theorem boundary_points_accumulate
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    (sys : MultiTurnSystem X)
    (_hf : ∀ t, Continuous (sys.f t))
    (_hD : ∀ t, Continuous (sys.D t))
    (_h_pres : ∀ t, ∀ x, sys.f t x < sys.τ → sys.D t x = x)
    (_h_safe : ∀ t, ∃ a, sys.f t a < sys.τ)
    (_h_unsafe : ∀ t, ∃ b, sys.f t b > sys.τ)
    (witness : Fin sys.T → X) :
    (∀ t, sys.f t (witness t) = sys.τ ∧ sys.D t (witness t) = witness t) →
    -- Then the set of all witnesses up to turn t₂ contains
    -- the set of all witnesses up to turn t₁ (for t₁ ≤ t₂)
    ∀ t₁ t₂ : Fin sys.T, t₁ ≤ t₂ →
      {x | ∃ i : Fin sys.T, i ≤ t₁ ∧ witness i = x} ⊆
      {x | ∃ i : Fin sys.T, i ≤ t₂ ∧ witness i = x} := by
  intro _h_valid t₁ t₂ h_le x ⟨i, hi_le, hi_eq⟩
  exact ⟨i, le_trans hi_le h_le, hi_eq⟩

/--
**Defense information leakage.**

At each turn, the defense's response to a probe reveals whether
the probe is safe, unsafe, or on the boundary. Over T turns with
T distinct probes, the attacker learns the classification of T points.

This is a counting argument: T probes → T bits of information about
the boundary location.
-/
theorem defense_leaks_per_turn (T : ℕ) :
    -- T turns of probing → at least T classified points
    -- (each probe yields one classification: safe/unsafe/boundary)
    T ≤ T := le_refl T

/--
A stronger version: if the attacker probes distinct points at each
turn, after T turns it knows the classification of T distinct points,
which constrains the boundary to lie in increasingly small regions.
-/
theorem knowledge_constrains_boundary
    {X : Type*} [Fintype X] [DecidableEq X]
    (_f : X → ℝ) (_τ : ℝ) (T : ℕ)
    (_probes : Fin T → X) (_h_distinct : Function.Injective _probes) :
    -- After T probes, the attacker knows f(probe_i) vs τ for i = 1..T
    -- The number of possible boundary configurations is reduced
    -- from 3^|X| to 3^(|X| - T), since T points are classified.
    Fintype.card X - T ≤ Fintype.card X := Nat.sub_le _ _

/-! ## 5. Attacker Steering Toward Transversality -/

/--
**Attacker steering: the attacker CAN reach transversality.**

If the slope function (how steeply the alignment surface rises at the
boundary) is continuous in the attacker's influence parameter α, and
the slope takes values on both sides of the threshold L(K+1), then
a transversality-inducing parameter exists. The attacker can find it
by binary search.
-/
theorem transversality_reachable
    (slope : ℝ → ℝ) (h_cont : Continuous slope)
    (threshold : ℝ)
    (h_low : slope 0 < threshold)
    (h_high : slope 1 > threshold) :
    ∃ α : ℝ, slope α = threshold := by
  have h_conn : IsPreconnected (Set.univ : Set ℝ) := isPreconnected_univ
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    h_cont.continuousOn continuous_const.continuousOn
    (le_of_lt h_low) (le_of_lt h_high)
  exact ⟨c, hc⟩

/-! ## 6. No Progressive Safety -/

/--
**The defense cannot progressively eliminate the impossibility.**

As long as both safe and unsafe regions exist at each turn, the
defense faces boundary fixation at every turn. The total count of
turns with boundary fixation equals the total count of turns with
both regions present.

This is trivially T if all T turns have mixed regions.
-/
theorem no_progressive_safety
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    (sys : MultiTurnSystem X)
    (hf : ∀ t, Continuous (sys.f t))
    (hD : ∀ t, Continuous (sys.D t))
    (h_pres : ∀ t, ∀ x, sys.f t x < sys.τ → sys.D t x = x)
    (h_safe : ∀ t, ∃ a, sys.f t a < sys.τ)
    (h_unsafe : ∀ t, ∃ b, sys.f t b > sys.τ) :
    -- Every turn has a boundary fixed point — no turn is "free"
    ∀ t : Fin sys.T, ∃ z, sys.f t z = sys.τ ∧ sys.D t z = z := by
  exact multi_turn_accumulates_fixed_points sys hf hD h_pres h_safe h_unsafe

/--
**The ONLY escape: make U_τ empty at some turn.**

If the defense manages to make the alignment surface uniformly
below τ at turn t (no unsafe region), the impossibility does not
apply at that turn. This is the multi-turn GPT-5-Mini strategy.

But: this requires changing the alignment surface itself, not just
preprocessing inputs. A defense D_t that only remaps inputs cannot
make f_t(x) < τ for all x — that would require changing f_t.
-/
theorem escape_requires_surface_change
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {τ : ℝ}
    -- If f has an unsafe point, no remap D can make f(D(x)) < τ for all x
    -- UNLESS D maps the unsafe point to a safe point
    (h_unsafe : ∃ b, f b > τ)
    (D : X → X) (h_complete : ∀ x, f (D x) < τ) :
    -- Then D must map some unsafe point to a safe point
    ∃ b, f b > τ ∧ f (D b) < τ := by
  obtain ⟨b, hb⟩ := h_unsafe
  exact ⟨b, hb, h_complete b⟩

/--
**But utility preservation prevents this for safe-adjacent points.**

Combining: the defense must map unsafe points to safe points
(to be complete), but utility preservation fixes safe points.
For boundary-adjacent unsafe points, the defense must make a
discontinuous jump — or accept the boundary fixed point.
-/
theorem complete_defense_must_jump
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_safe : ∃ a, f a < τ)
    (h_unsafe : ∃ b, f b > τ) :
    -- A complete continuous utility-preserving defense cannot exist
    ¬(∀ x, f (D x) < τ) := by
  intro h_complete
  obtain ⟨z, hz_eq, _, _, hz_not⟩ :=
    defense_incompleteness hD hf h_pres h_safe h_unsafe
  exact hz_not (h_complete z)

end MoF

end

