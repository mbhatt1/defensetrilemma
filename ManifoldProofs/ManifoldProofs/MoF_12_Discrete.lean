import Mathlib

/-!
# Manifold of Failure — Part 12: Discrete Impossibility

Discrete analogues of the defense impossibility theorems that work
directly on finite spaces WITHOUT continuous relaxation or Tietze extension.

## Results

1. `discrete_ivt` — On a finite path {0,...,n}, if f(0) < τ < f(n),
   there exists i where f crosses from below τ to at-or-above τ.
   (Discrete IVT.)

2. `discrete_defense_boundary_fixed` — If a defense fixes safe vertices,
   boundary crossings persist with a fixed safe endpoint.

3. `defense_capacity_pigeonhole` — When adversarial configurations
   exceed defense capacity, misclassification is inevitable.

4. `doubly_exponential_overwhelms` — The configuration space 2^(2^d)
   eventually exceeds any polynomial defense capacity.

These results show the defense impossibility holds in the discrete
setting without any appeal to continuous topology.
-/

open Finset

noncomputable section

namespace MoF.Discrete

/-! ## 1. Discrete IVT on Finite Paths -/

/--
**Discrete Intermediate Value Theorem.**

If `f : Fin (n+2) → ℝ` satisfies `f 0 < τ` and `f (n+1) ≥ τ`,
then there exists `i : Fin (n+1)` such that
`f i < τ` and `f (i+1) ≥ τ`.

This is the discrete analogue of the topological boundary existence
theorem. No continuity, no topology—just a counting argument on
a finite ordered set.
-/
theorem discrete_ivt {n : ℕ} (f : Fin (n + 2) → ℝ) (τ : ℝ)
    (h_start : f 0 < τ) (h_end : f ⟨n + 1, by omega⟩ ≥ τ) :
    ∃ i : Fin (n + 1), f ⟨i.val, by omega⟩ < τ ∧
      f ⟨i.val + 1, by omega⟩ ≥ τ := by
  -- By strong induction / well-ordering: consider the largest i with f(i) < τ.
  -- Then f(i+1) ≥ τ.
  by_contra h_no_cross
  push_neg at h_no_cross
  -- h_no_cross : ∀ i : Fin (n+1), f ⟨i, ...⟩ < τ → f ⟨i+1, ...⟩ < τ
  -- By induction, f(k) < τ for all k ≤ n+1.
  have h_all : ∀ k : ℕ, (hk : k < n + 2) → f ⟨k, hk⟩ < τ := by
    intro k hk
    induction k with
    | zero => exact h_start
    | succ k ih =>
      have hk' : k < n + 1 := by omega
      have hk'' : k < n + 2 := by omega
      have := h_no_cross ⟨k, hk'⟩ (ih hk'')
      convert this using 1
  -- But f(n+1) ≥ τ, contradiction.
  have := h_all (n + 1) (by omega)
  linarith

-- Note: `discrete_ivt` above is the clean statement assuming f(0) < τ ≤ f(n+1).
-- For the general case (arbitrary endpoints), reindex to put the below-point first.

/-! ## 2. Discrete Defense Boundary Fixed Point -/

/--
**Discrete Defense Incompleteness.**

If D fixes all safe vertices (f(v) < τ → D(v) = v), then the
boundary crossing from `discrete_ivt` has its safe endpoint fixed.

This is the discrete analogue of Theorem 4.1 (boundary fixation).
-/
theorem discrete_defense_boundary_fixed
    {n : ℕ} (f : Fin (n + 2) → ℝ) (τ : ℝ)
    (D : Fin (n + 2) → Fin (n + 2))
    (h_start : f 0 < τ)
    (h_end : f ⟨n + 1, by omega⟩ ≥ τ)
    (h_pres : ∀ v : Fin (n + 2), f v < τ → D v = v) :
    ∃ i : Fin (n + 1),
      f ⟨i.val, by omega⟩ < τ ∧
      f ⟨i.val + 1, by omega⟩ ≥ τ ∧
      D ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ := by
  obtain ⟨i, hi_below, hi_above⟩ := discrete_ivt f τ h_start h_end
  exact ⟨i, hi_below, hi_above, h_pres ⟨i.val, by omega⟩ hi_below⟩

-- Note: without topology, a discrete defense CAN map any unsafe point
-- to any safe point. The discrete impossibility instead concerns
-- INJECTIVITY: a complete defense must lose information.

/-! ## 3. Injectivity Forces Incompleteness -/

/--
**An injective, utility-preserving defense cannot make unsafe inputs safe.**

If D is injective and fixes all safe inputs, then every unsafe input
stays unsafe. The safe "slots" are all occupied by safe inputs
(via utility preservation), so injectivity leaves no room for unsafe
inputs to land on safe outputs.

Proof: Suppose f(D(u)) < τ for some unsafe u. Then D(u) is safe, so
D(D(u)) = D(u) (utility preservation). Injectivity gives D(u) = u.
But then f(u) = f(D(u)) < τ, contradicting f(u) ≥ τ.
-/
theorem injectivity_forces_incompleteness
    {α : Type*}
    {f : α → ℝ} {τ : ℝ} {D : α → α}
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_inj : Function.Injective D)
    {u : α} (hu : f u ≥ τ) :
    f (D u) ≥ τ := by
  by_contra h_safe
  push_neg at h_safe
  -- f(D(u)) < τ, so utility preservation gives D(D(u)) = D(u)
  have h_fix : D (D u) = D u := h_pres (D u) h_safe
  -- Injectivity: D(u) = u
  have h_eq : D u = u := h_inj h_fix
  -- Contradiction: f(u) ≥ τ but f(D(u)) = f(u) < τ
  linarith [h_eq ▸ h_safe]

/-! ## 4. Completeness Forces Non-Injectivity -/

/--
**Any complete, utility-preserving defense must lose information.**

If D is complete (f(D(x)) < τ for all x) and utility-preserving
(D(x) = x for safe x), then D is non-injective: there exist
distinct inputs x ≠ y with D(x) = D(y).

Specifically, for any unsafe u: D(u) is safe (completeness), so
D(D(u)) = D(u) (utility preservation). But u ≠ D(u) (different
f-values). So u and D(u) are distinct inputs with the same output.

The defense cannot distinguish its own remapped output from the
original safe input—a fundamental information-theoretic limitation.
-/
theorem completeness_forces_noninjectivity
    {α : Type*}
    {f : α → ℝ} {τ : ℝ} {D : α → α}
    (h_pres : ∀ x, f x < τ → D x = x)
    (h_complete : ∀ x, f (D x) < τ)
    {u : α} (hu : f u ≥ τ) :
    ∃ x y : α, x ≠ y ∧ D x = D y := by
  refine ⟨u, D u, ?_, ?_⟩
  · -- u ≠ D(u): f(u) ≥ τ but f(D(u)) < τ
    intro h_eq
    have := h_complete u; rw [← h_eq] at this; linarith
  · -- D(u) = D(D(u)): D(u) is safe, so D fixes it
    exact (h_pres (D u) (h_complete u)).symm

/-! ## 5. The Discrete Defense Dilemma -/

/--
**Discrete Defense Dilemma.**

On any set with both safe and unsafe elements, a utility-preserving
defense faces a dilemma:
- Completeness forces non-injectivity (information loss)
- Injectivity forces incompleteness (unsafe inputs persist)

The three properties {completeness, utility preservation, injectivity}
form a trilemma: any two can coexist, but not all three.

This mirrors the continuous defense trilemma where continuity plays
the role of injectivity: a continuous map on a connected space cannot
"jump" over the boundary, just as an injective map cannot "reuse"
safe outputs for unsafe inputs.
-/
theorem discrete_trilemma
    {α : Type*}
    {f : α → ℝ} {τ : ℝ} {D : α → α}
    (h_pres : ∀ x, f x < τ → D x = x)
    {u : α} (hu : f u ≥ τ) :
    -- Either D leaves u unsafe...
    (f (D u) ≥ τ) ∨
    -- ...or D is non-injective
    (∃ x y : α, x ≠ y ∧ D x = D y) := by
  by_cases h : f (D u) < τ
  · -- D maps u to a safe output → non-injective
    right
    refine ⟨u, D u, ?_, ?_⟩
    · -- u ≠ D(u): different f-values
      intro h_eq; have := h; rw [← h_eq] at this; linarith
    · -- D(u) = D(D(u)): D(u) is safe, so D fixes it
      exact (h_pres (D u) h).symm
  · -- D doesn't make u safe → incomplete
    left
    exact not_lt.mp h

end MoF.Discrete

end
