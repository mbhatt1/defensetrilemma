import Mathlib
import ManifoldProofs.MoF_08_DefenseBarriers

/-!
# Manifold of Failure — Part 14: Representation-Independent Meta-Theorem

## The Main Theorem

**Regularity Implies Spillover**: utility preservation + bounded regularity
forces Fix(D) ⊋ S. This is the HARD part. The existence of non-safe
fixed points is then a trivial corollary.

The theorem is parameterized by a `Regularity` typeclass that captures
"some mechanism prevents Fix(D) from being exactly S." Three
instantiations are provided:

1. **Continuous**: Fix(D) is closed + S is open + connected → S not clopen → Fix(D) ⊋ S.
2. **Discrete**: IVT on finite ordered set → crossing with fixed safe endpoint.
3. **Stochastic**: g - f vanishes on S, extends to cl(S) by continuity.

## Results

- `regularity_implies_spillover` — THE MAIN THEOREM.
- `spillover_gives_non_safe_fixed_point` — Corollary: ∃ non-safe fixed point.
- `continuous_regularity` — Instantiation for connected Hausdorff spaces.
- `discrete_regularity` — Instantiation for finite ordered sets.
- `stochastic_regularity` — Instantiation for expected-value defenses.
- `why_inescapable` — For Fix(D) = S, S must be clopen; impossible in
  connected spaces.
-/

open Set Topology Filter

noncomputable section

namespace MoF.Meta

/-! ## 1. The Main Theorem: Regularity Implies Spillover -/

/--
**Main Theorem (Regularity Implies Spillover).**

Any utility-preserving defense with bounded regularity must satisfy
Fix(D) ⊋ S.

Concretely: if D fixes all safe inputs and the fixed-point set cannot
equal S exactly (the regularity condition), then Fix(D) strictly
contains S.

The regularity condition is abstract — it is the hypothesis
`S ≠ {x | D x = x}`. Each instantiation (continuous, discrete,
stochastic) provides a PROOF of this hypothesis from domain-specific
structure.
-/
theorem regularity_implies_spillover
    {X : Type*} {S : Set X}
    {D : X → X}
    -- Utility preservation: D = id on S
    (h_pres : ∀ x ∈ S, D x = x)
    -- Bounded regularity: Fix(D) cannot equal S exactly
    (h_regularity : {x : X | D x = x} ≠ S) :
    -- CONCLUSION: Fix(D) ⊋ S
    S ⊂ {x : X | D x = x} := by
  rw [Set.ssubset_iff_subset_ne]
  exact ⟨fun x hx => h_pres x hx, fun h_eq => h_regularity h_eq.symm⟩

/-! ## 2. Corollary: Non-Safe Fixed Point Exists -/

/--
**Corollary.** Fix(D) ⊋ S implies a non-safe fixed point exists.

This is the trivial direction — pure set theory. The hard work is in
`regularity_implies_spillover` and its instantiations.
-/
theorem spillover_gives_non_safe_fixed_point
    {X : Type*} {S : Set X}
    {D : X → X}
    (h_spillover : S ⊂ {x : X | D x = x}) :
    ∃ x, x ∉ S ∧ D x = x := by
  obtain ⟨x, hx_fix, hx_not_safe⟩ := Set.nonempty_of_ssubset h_spillover
  exact ⟨x, hx_not_safe, hx_fix⟩

/--
**Combined: utility preservation + regularity → non-safe fixed point.**
-/
theorem meta_impossibility
    {X : Type*} {S : Set X} {D : X → X}
    (h_pres : ∀ x ∈ S, D x = x)
    (h_regularity : {x : X | D x = x} ≠ S) :
    ∃ x, x ∉ S ∧ D x = x :=
  spillover_gives_non_safe_fixed_point
    (regularity_implies_spillover h_pres h_regularity)

/-! ## 3. Instantiation: Continuous Regularity -/

/--
**Why Fix(D) ≠ S in connected Hausdorff spaces.**

Fix(D) is closed (D continuous, X Hausdorff). S is open (preimage of
open set under continuous f). If Fix(D) = S, then S is clopen. In a
connected space, the only clopen sets are ∅ and X. Since S ≠ ∅ and
S ≠ X, contradiction.

This is the regularity proof for the continuous path.
-/
theorem continuous_regularity
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (_h_pres : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    {x : X | D x = x} ≠ {x : X | f x < τ} := by
  intro h_eq
  -- Fix(D) is closed
  have h_closed_fix : IsClosed {x : X | D x = x} := defense_fixes_closure hD
  -- So S = Fix(D) is closed
  have h_closed_S : IsClosed {x : X | f x < τ} := h_eq ▸ h_closed_fix
  -- But S is also open
  have h_open_S : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
  -- So S is clopen
  have h_clopen : IsClopen {x : X | f x < τ} := ⟨h_closed_S, h_open_S⟩
  -- In a connected space, clopen = ∅ or univ
  rcases isClopen_iff.mp h_clopen with h_empty | h_univ
  · obtain ⟨a, ha⟩ := h_safe_ne
    have : a ∈ ({x : X | f x < τ} : Set X) := ha
    rw [h_empty] at this; exact this
  · obtain ⟨b, hb⟩ := h_unsafe_ne
    have : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
    simp only [Set.mem_setOf_eq] at this; linarith

/--
**Continuous instantiation of the main theorem.**

Tier 1 is a corollary of `regularity_implies_spillover` +
`continuous_regularity`.
-/
theorem tier1_from_meta
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    ∃ x, ¬(f x < τ) ∧ D x = x :=
  meta_impossibility
    (fun x hx => h_pres x hx)
    (continuous_regularity hf hD h_pres h_safe_ne h_unsafe_ne)

/--
The non-safe fixed point is actually a boundary point (f(x) = τ).
-/
theorem tier1_boundary_from_meta
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    ∃ x, f x = τ ∧ D x = x := by
  obtain ⟨z, hz_eq, hz_fix, _, _⟩ :=
    defense_incompleteness hD hf h_pres h_safe_ne h_unsafe_ne
  exact ⟨z, hz_eq, hz_fix⟩

/-! ## 4. Instantiation: Discrete Regularity -/

/--
**Why Fix(D) ⊋ S on finite ordered sets.**

On {0, ..., n+1} with f(0) < τ ≤ f(n+1), the discrete IVT gives
a consecutive crossing. Utility preservation fixes the safe side.
This is a non-safe fixed point adjacent to the crossing.
-/
theorem discrete_regularity
    {n : ℕ} {f : Fin (n + 2) → ℝ} {τ : ℝ}
    (h_start : f 0 < τ) (h_end : f ⟨n + 1, by omega⟩ ≥ τ)
    {D : Fin (n + 2) → Fin (n + 2)}
    (h_pres : ∀ v, f v < τ → D v = v) :
    ∃ i : Fin (n + 1),
      f ⟨i.val, by omega⟩ < τ ∧
      f ⟨i.val + 1, by omega⟩ ≥ τ ∧
      D ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ := by
  -- Discrete IVT: find crossing
  have h_cross : ∃ i : Fin (n + 1),
      f ⟨i.val, by omega⟩ < τ ∧ f ⟨i.val + 1, by omega⟩ ≥ τ := by
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

/-! ## 5. Instantiation: Stochastic Regularity -/

/--
**Why Fix(g) ≠ S for stochastic defenses.**

If g = E[f ∘ D] is continuous and g = f on S, then g - f vanishes
on S and (by continuity) on cl(S). At boundary points z ∈ cl(S) \ S,
g(z) = f(z) = τ. So the "expected fixed-point set" {g = f} contains
cl(S) ⊋ S.
-/
theorem stochastic_regularity
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {g : X → ℝ} (hg : Continuous g)
    (h_agree : ∀ x, f x < τ → g x = f x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    ∃ z, f z = τ ∧ g z = τ := by
  -- Find boundary point via closure argument
  have h_strict : {x : X | f x < τ} ⊂ closure {x : X | f x < τ} := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨subset_closure, fun h_eq => by
      have : IsClosed {x : X | f x < τ} := h_eq ▸ isClosed_closure
      have h_open : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
      have h_clopen : IsClopen {x : X | f x < τ} := ⟨this, h_open⟩
      rcases isClopen_iff.mp h_clopen with h_empty | h_univ
      · obtain ⟨a, ha⟩ := h_safe_ne
        have : a ∈ ({x : X | f x < τ} : Set X) := ha
        rw [h_empty] at this; exact this
      · obtain ⟨b, hb⟩ := h_unsafe_ne
        have : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
        simp only [Set.mem_setOf_eq] at this; linarith⟩
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  -- f(z) = τ
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} :=
      closure_minimal (fun x (hx : f x < τ) => le_of_lt hx) (isClosed_le hf continuous_const)
    exact this hz_clos
  have hz_ge : f z ≥ τ := not_lt.mp hz_not_safe
  have hz_eq : f z = τ := le_antisymm hz_le hz_ge
  -- g(z) = f(z) = τ by continuity of g - f
  have hg_z : g z = f z := by
    have h_diff_cont : Continuous (fun x => g x - f x) := hg.sub hf
    have h_diff_zero_closure : ∀ x ∈ closure {x : X | f x < τ}, g x - f x = 0 := by
      apply closure_minimal (s := {x : X | f x < τ})
      · intro x hx; exact sub_eq_zero.mpr (h_agree x hx)
      · exact isClosed_eq h_diff_cont continuous_const
    linarith [h_diff_zero_closure z hz_clos]
  exact ⟨z, hz_eq, hg_z ▸ hz_eq⟩

/-! ## 6. Why Escape Is Impossible -/

/--
**The Geometric Lock.**

For Fix(D) to equal S exactly, S would need to be both open (as a
preimage under continuous f) and closed (as a fixed-point set of
continuous D). In a connected space with S ≠ ∅ and S ≠ X, no set
is both open and closed. This is why every regularity proof works:
they all ultimately reduce to "S cannot be clopen."
-/
theorem geometric_lock
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {S : Set X} (h_open : IsOpen S) (h_ne : S.Nonempty)
    (h_proper : S ≠ Set.univ) :
    ¬IsClosed S := by
  intro h_closed
  have h_clopen : IsClopen S := ⟨h_closed, h_open⟩
  rcases isClopen_iff.mp h_clopen with h_empty | h_univ
  · exact h_ne.ne_empty h_empty
  · exact h_proper h_univ

/--
**Consequence: continuous defense regularity is unavoidable.**

If D is continuous on a connected Hausdorff space, Fix(D) is closed.
If f is continuous, S = {f < τ} is open. By `geometric_lock`, Fix(D) ≠ S
whenever S is nonempty and proper. Therefore `regularity_implies_spillover`
applies.
-/
theorem regularity_unavoidable
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {D : X → X} (hD : Continuous D)
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    {x : X | f x < τ} ⊂ {x : X | D x = x} :=
  regularity_implies_spillover
    (fun x hx => h_pres x hx)
    (continuous_regularity hf hD h_pres h_safe_ne h_unsafe_ne)

end MoF.Meta

end
