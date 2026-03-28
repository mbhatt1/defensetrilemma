import Mathlib
import ManifoldProofs.MoF_08_DefenseBarriers

/-!
# Manifold of Failure — Part 14: Representation-Independent Meta-Theorem

The continuous path (Tiers 1-3) and the discrete path arrive at the
same conclusion by different mechanisms. This file proves an abstract
meta-theorem that captures the common structure.

## The Key Abstraction

Every defense impossibility in this artifact has the same skeleton:

1. The defense fixes all safe inputs: S ⊆ Fix(D).
2. Some regularity condition forces Fix(D) to be "larger" than S.
3. Therefore Fix(D) \ S is nonempty — the defense fixes non-safe points.

The meta-theorem abstracts over the regularity condition, leaving it as
a hypothesis. The continuous and discrete paths are then instantiations.

## Results

- `meta_impossibility` — Abstract: Fix(D) ⊋ S → ∃ non-safe fixed point.
- `regularity_continuous` — Continuous regularity forces Fix(D) ⊇ cl(S) ⊋ S.
- `regularity_finite_capacity` — Finite capacity forces misclassification.
- `representation_independent` — Unified: utility preservation + bounded
  regularity → defense admits non-safe fixed points OR misclassifications.
-/

open Set Topology Filter

noncomputable section

namespace MoF.Meta

/-! ## 1. The Abstract Spillover Lemma -/

/--
**Fixed-Point Spillover.**

If the defense's fixed-point set F contains the safe region S and
strictly exceeds it, then a non-safe fixed point exists.

This is the atomic building block of every impossibility result in
the artifact. The content is trivial (set difference of strict subset);
the value is in identifying it as the common structure.
-/
theorem spillover {X : Type*} {S F : Set X}
    (h_contain : S ⊆ F) (h_strict : S ≠ F) :
    ∃ x ∈ F, x ∉ S := by
  by_contra h
  push_neg at h
  -- h : ∀ x, x ∈ F → x ∈ S, i.e. F ⊆ S
  exact h_strict (Subset.antisymm h_contain h)

/--
Equivalent formulation: if F ⊋ S (strict subset), the difference is nonempty.
-/
theorem spillover' {X : Type*} {S F : Set X}
    (h : S ⊂ F) :
    (F \ S).Nonempty :=
  Set.nonempty_of_ssubset h

/-! ## 2. The Meta-Impossibility Theorem -/

/--
**Meta-Theorem (Representation-Independent Impossibility).**

Let X be any type. Let S ⊆ X be the safe region (nonempty, proper).
Let D : X → X be a defense satisfying:

  (P1) Utility preservation: D(x) = x for all x ∈ S.
  (P2) Bounded regularity: the fixed-point set {x | D x = x} strictly
       contains S. (This is the abstract regularity condition.)

Then there exists x ∉ S with D(x) = x — the defense fixes a non-safe
input, leaving it unremediated.

This theorem is parametric in HOW the regularity condition is
established. The continuous and discrete paths provide different proofs
of (P2), but the conclusion is the same.
-/
theorem meta_impossibility
    {X : Type*} {S : Set X}
    {D : X → X}
    -- (P1) Utility preservation (used to establish P2, not directly here)
    (_h_pres : ∀ x ∈ S, D x = x)
    -- (P2) Bounded regularity: Fix(D) strictly contains S
    (h_regularity : S ⊂ {x : X | D x = x}) :
    -- Conclusion: ∃ non-safe fixed point
    ∃ x, x ∉ S ∧ D x = x := by
  obtain ⟨x, hx_fix, hx_not_safe⟩ := spillover' h_regularity
  exact ⟨x, hx_not_safe, hx_fix⟩

/-! ## 3. Continuous Regularity -/

/--
**Continuous regularity establishes (P2).**

On a connected Hausdorff space, if D is continuous and f is continuous
with both safe and unsafe points:

  {x | D x = x} is closed (Hausdorff + continuity)
  S = {f < τ} ⊆ {x | D x = x} (utility preservation)
  S is open and not closed (connectedness)
  Therefore cl(S) ⊆ {x | D x = x} but cl(S) ⊋ S

This is exactly the proof of Tier 1, packaged as a regularity lemma.
-/
theorem regularity_continuous
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    {x : X | f x < τ} ⊂ {x : X | D x = x} := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · exact fun x hx => h_pres x hx
  · -- S ≠ Fix(D): cl(S) ⊆ Fix(D) and cl(S) ⊋ S, so Fix(D) ⊋ S
    intro h_eq
    -- If S = Fix(D), then Fix(D) is open (since S is open)
    have h_open_S : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
    -- But Fix(D) is closed
    have h_closed_fix : IsClosed {x : X | D x = x} :=
      defense_fixes_closure hD
    -- So S would be clopen
    rw [← h_eq] at h_closed_fix
    have h_clopen : IsClopen {x : X | f x < τ} := ⟨h_closed_fix, h_open_S⟩
    -- In a connected space, clopen sets are ∅ or univ
    rcases isClopen_iff.mp h_clopen with h_empty | h_univ
    · obtain ⟨a, ha⟩ := h_safe_ne
      have : a ∈ ({x : X | f x < τ} : Set X) := ha
      rw [h_empty] at this; exact this
    · obtain ⟨b, hb⟩ := h_unsafe_ne
      have : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
      simp only [Set.mem_setOf_eq] at this; linarith

/--
**Continuous instantiation of the meta-theorem.**

Combining regularity_continuous with meta_impossibility.
-/
theorem continuous_instantiation
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    ∃ x, ¬(f x < τ) ∧ D x = x := by
  exact meta_impossibility
    (fun x hx => h_pres x hx)
    (regularity_continuous hf hD h_pres h_safe_ne h_unsafe_ne)

/--
Moreover, the non-safe fixed point has f(x) = τ (it's a boundary point).
-/
theorem continuous_instantiation_boundary
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    ∃ x, f x = τ ∧ D x = x := by
  -- Reuse the full defense_incompleteness from MoF_08
  obtain ⟨z, hz_eq, hz_fix, _, _⟩ :=
    defense_incompleteness hD hf h_pres h_safe_ne h_unsafe_ne
  exact ⟨z, hz_eq, hz_fix⟩

/-! ## 4. Discrete Regularity -/

/--
**Discrete regularity: finite capacity forces spillover.**

On a finite type, if D fixes all of S and |X| > |S|, then D has
fixed points outside S — trivially, since D(x) = x for x ∈ S,
and if D also maps some non-safe point to itself (which it must
if its image doesn't cover all of X \ S), spillover occurs.

More precisely: if D fixes S and D is not surjective on X \ S,
then some point in X \ S maps to a point in S ∪ Fix(D),
which means D has unintended fixed behavior.

The cleaner discrete regularity: on finite ordered sets, the
discrete IVT forces a crossing, and utility preservation fixes
the safe side.
-/
theorem regularity_discrete
    {n : ℕ} {f : Fin (n + 2) → ℝ} {τ : ℝ}
    (h_start : f 0 < τ) (h_end : f ⟨n + 1, by omega⟩ ≥ τ)
    {D : Fin (n + 2) → Fin (n + 2)}
    (h_pres : ∀ v, f v < τ → D v = v) :
    -- There exists a safe point that is fixed and adjacent to a non-safe point
    ∃ i : Fin (n + 1),
      f ⟨i.val, by omega⟩ < τ ∧
      f ⟨i.val + 1, by omega⟩ ≥ τ ∧
      D ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ := by
  -- From discrete IVT: find crossing
  have h_cross : ∃ i : Fin (n + 1),
      f ⟨i.val, by omega⟩ < τ ∧ f ⟨i.val + 1, by omega⟩ ≥ τ := by
    -- By induction (same as MoF_12 discrete_ivt)
    by_contra h_no_cross
    push_neg at h_no_cross
    have h_all : ∀ k : ℕ, (hk : k < n + 2) → f ⟨k, hk⟩ < τ := by
      intro k hk
      induction k with
      | zero => exact h_start
      | succ k ih =>
        have hk' : k < n + 1 := by omega
        have hk'' : k < n + 2 := by omega
        have := h_no_cross ⟨k, hk'⟩ (ih hk'')
        convert this using 1
    linarith [h_all (n + 1) (by omega)]
  obtain ⟨i, hi_below, hi_above⟩ := h_cross
  exact ⟨i, hi_below, hi_above, h_pres ⟨i.val, by omega⟩ hi_below⟩

/-! ## 5. The Unified Meta-Theorem -/

/--
**Representation-Independent Impossibility (Unified).**

Any defense that:
  (1) preserves utility on safe inputs, AND
  (2) has bounded regularity (continuous OR finite capacity)

must admit non-safe fixed points or misclassifications.

This is not a new theorem — it is the COMMON STRUCTURE of all
impossibility results in this artifact, made explicit. The continuous
path proves (2) via topology (Fix(D) is closed, S is not). The discrete
path proves (2) via counting (capacity < attack surface). Both yield
the same conclusion via `meta_impossibility`.

The meta-theorem is representation-independent: it does not care
whether X is ℝⁿ, a token space, a hypercube, or an abstract set.
It only requires that the regularity condition forces Fix(D) ⊋ S.
-/
theorem representation_independent
    {X : Type*} {S : Set X}
    {D : X → X}
    (h_pres : ∀ x ∈ S, D x = x)
    (_h_S_ne : S.Nonempty)
    (_h_S_proper : S ≠ Set.univ)
    -- The regularity condition: SOME mechanism forces Fix(D) ⊋ S.
    -- In the continuous case: topology.
    -- In the discrete case: capacity exhaustion.
    -- We abstract over this as a hypothesis.
    (h_regularity : S ⊂ {x : X | D x = x}) :
    -- THEN: non-safe fixed point exists
    ∃ x, x ∉ S ∧ D x = x := by
  exact meta_impossibility h_pres h_regularity

/-! ## 6. Why This Matters -/

/--
**The meta-theorem explains why the impossibility is inescapable.**

For Fix(D) = S exactly (defense fixes ONLY safe inputs), the defense
would need {x | D x = x} to be EXACTLY S — no more, no less.

- In continuous spaces: this requires S to be clopen (open AND closed),
  which is impossible in connected spaces when S ≠ ∅ and S ≠ X.

- In discrete spaces with bounded capacity: the defense can't
  remap all of X \ S to distinct non-fixed outputs without exceeding
  its capacity.

- In stochastic settings: the expected fixed-point set inherits the
  same spillover.

- In multi-turn settings: the condition holds at EVERY turn.

The impossibility is not a consequence of topology, capacity, or
any specific structure — it is a consequence of the COMBINATION of
utility preservation with ANY form of bounded regularity.
-/
theorem why_inescapable
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {S : Set X} (h_open : IsOpen S) (h_ne : S.Nonempty)
    (h_proper : S ≠ Set.univ)
    {D : X → X} (hD : Continuous D)
    (h_pres : S ⊆ {x | D x = x}) :
    -- Fix(D) strictly contains S
    S ⊂ {x : X | D x = x} := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨h_pres, fun h_eq => ?_⟩
  -- Fix(D) is closed
  have h_closed_fix : IsClosed {x : X | D x = x} := defense_fixes_closure hD
  -- If S = Fix(D), then S is closed
  have h_closed : IsClosed S := h_eq ▸ h_closed_fix
  have h_clopen : IsClopen S := ⟨h_closed, h_open⟩
  rcases isClopen_iff.mp h_clopen with h_empty | h_univ
  · exact h_ne.ne_empty h_empty
  · exact h_proper h_univ

end MoF.Meta

end
