import Mathlib

/-!
# Manifold of Failure — Part 16: Relaxed Utility Preservation

The strict utility preservation assumption (`D(x) = x` for safe `x`) is
stronger than necessary. A practical defense might rewrite a safe prompt
into a semantically different but equally safe prompt (e.g., normalizing
input format). This file proves that the impossibility results survive
three progressively weaker assumptions:

1. **Score-preserving** (`f(D(x)) = f(x)` on safe inputs): the defense
   may rewrite prompts arbitrarily, but preserves alignment deviation
   scores. Boundary fixation holds: `f(D(z)) = τ`.

2. **ε-score-preserving** (`|f(D(x)) - f(x)| ≤ ε` on safe inputs): the
   defense approximately preserves scores. Near-boundary fixation holds:
   `f(D(z)) ≥ τ - ε`.

3. **Safe-preserving** (`D(S_τ) ⊆ S_τ`): this is too weak — a constant
   map to a fixed safe point escapes, proving the constraint is necessary.

## Key insight

The proofs do NOT use `D(x) = x` on safe inputs. Instead they work with
`h = f ∘ D - f`, showing that if `h` vanishes (or is bounded) on the
safe region, it vanishes (or is bounded) on the closure — which contains
boundary points.
-/

open Set Topology Filter

noncomputable section

namespace MoF

/-! ## 1. Score-preserving defense: f(D(x)) = f(x) on safe inputs -/

/--
If `f ∘ D = f` on `{f < τ}`, then `f ∘ D = f` on `closure {f < τ}`.
This is because `{x | f(D(x)) = f(x)}` is closed (preimage of the
diagonal under continuous functions) and contains `{f < τ}`.
-/
theorem score_preserving_extends_to_closure
    {X : Type*} [TopologicalSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f)
    {τ : ℝ}
    (h_score : ∀ x, f x < τ → f (D x) = f x) :
    ∀ z, z ∈ closure {x : X | f x < τ} → f (D z) = f z := by
  -- The set {x | f(D(x)) = f(x)} is closed
  have h_closed : IsClosed {x : X | f (D x) = f x} := by
    have : {x : X | f (D x) = f x} = (fun x => (f (D x), f x)) ⁻¹' (Set.diagonal ℝ) := by
      ext x; simp [Set.mem_diagonal_iff]
    rw [this]
    exact isClosed_diagonal.preimage (by fun_prop)
  -- {f < τ} ⊆ {f ∘ D = f}
  have h_sub : {x : X | f x < τ} ⊆ {x : X | f (D x) = f x} :=
    fun x hx => h_score x hx
  -- closure {f < τ} ⊆ {f ∘ D = f}
  intro z hz
  exact h_closed.closure_subset_iff.mpr h_sub hz

/--
**Score-Preserving Boundary Fixation.**

On a connected T2 space, if `f` is continuous with both safe and unsafe
points, and `D` is continuous with `f(D(x)) = f(x)` for all safe `x`,
then there exists a boundary point `z` with `f(z) = τ` and `f(D(z)) = τ`.

The defense does not need to satisfy `D(x) = x` — it can rewrite safe
prompts arbitrarily, as long as the alignment deviation score is preserved.
-/
theorem score_preserving_boundary_fixation
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    (h_score : ∀ x, f x < τ → f (D x) = f x)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ∃ z : X, f z = τ ∧ f (D z) = τ ∧ ¬ (f (D z) < τ) := by
  -- Reuse the boundary existence result from MoF_08's argument
  -- closure {f < τ} strictly contains {f < τ} in a connected space
  have h_not_closed : ¬ IsClosed {x : X | f x < τ} := by
    intro h_closed
    have h_open : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
    have h_clopen : IsClopen {x : X | f x < τ} := ⟨h_closed, h_open⟩
    rcases isClopen_iff.mp h_clopen with h_empty | h_univ
    · obtain ⟨a, ha⟩ := h_safe_ne
      have : a ∈ ({x : X | f x < τ} : Set X) := ha
      rw [h_empty] at this; exact this
    · obtain ⟨b, hb⟩ := h_unsafe_ne
      have : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
      simp only [Set.mem_setOf_eq] at this; linarith
  -- There exists z in closure \ interior
  have h_strict : {x : X | f x < τ} ⊂ closure {x : X | f x < τ} := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨subset_closure, fun h_eq => h_not_closed (h_eq ▸ isClosed_closure)⟩
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  -- z has f(z) = τ
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} := by
      apply closure_minimal
      · intro x (hx : f x < τ); exact le_of_lt hx
      · exact isClosed_le hf continuous_const
    exact this hz_clos
  simp only [Set.mem_setOf_eq] at hz_not_safe
  have hz_ge : f z ≥ τ := not_lt.mp hz_not_safe
  have hz_eq : f z = τ := le_antisymm hz_le hz_ge
  -- f(D(z)) = f(z) = τ by score preservation on closure
  have hDz : f (D z) = f z :=
    score_preserving_extends_to_closure hD hf h_score z hz_clos
  rw [hz_eq] at hDz
  exact ⟨z, hz_eq, hDz, by linarith⟩

/--
Corollary: a score-preserving defense cannot be complete.
-/
theorem score_preserving_defense_incomplete
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    (h_score : ∀ x, f x < τ → f (D x) = f x)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ¬ (∀ x, f (D x) < τ) := by
  obtain ⟨z, _, hDz_eq, _⟩ := score_preserving_boundary_fixation hD hf h_score h_safe_ne h_unsafe_ne
  intro h_all
  linarith [h_all z]


/-! ## 2. ε-score-preserving defense: |f(D(x)) - f(x)| ≤ ε on safe inputs -/

/--
If `|f(D(x)) - f(x)| ≤ ε` on `{f < τ}`, then `f(D(z)) - f(z) ≥ -ε`
on `closure {f < τ}`.

The proof uses that `{x | f(D(x)) - f(x) ≥ -ε}` is closed and contains
`{f < τ}`.
-/
theorem eps_score_preserving_extends_to_closure
    {X : Type*} [TopologicalSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f)
    {τ : ℝ} {ε : ℝ}
    (h_eps_score : ∀ x, f x < τ → |f (D x) - f x| ≤ ε) :
    ∀ z, z ∈ closure {x : X | f x < τ} → f (D z) ≥ f z - ε := by
  -- {x | f(D(x)) - f(x) ≥ -ε} is closed
  have h_closed : IsClosed {x : X | f (D x) - f x ≥ -ε} := by
    have : {x : X | f (D x) - f x ≥ -ε} = (fun x => f (D x) - f x) ⁻¹' Set.Ici (-ε) := by
      ext x; simp [Set.mem_Ici]
    rw [this]
    exact isClosed_Ici.preimage ((hf.comp hD).sub hf)
  -- {f < τ} ⊆ {f(D(x)) - f(x) ≥ -ε}
  have h_sub : {x : X | f x < τ} ⊆ {x : X | f (D x) - f x ≥ -ε} := by
    intro x hx
    simp only [Set.mem_setOf_eq]
    have := h_eps_score x hx
    linarith [abs_le.mp this]
  -- closure ⊆ closed set
  intro z hz
  have : z ∈ {x : X | f (D x) - f x ≥ -ε} :=
    h_closed.closure_subset_iff.mpr h_sub hz
  simp only [Set.mem_setOf_eq] at this
  linarith

/--
**ε-Relaxed Boundary Fixation.**

On a connected T2 space, if `f` is continuous with both safe and unsafe
points, and `D` is continuous with `|f(D(x)) - f(x)| ≤ ε` for all safe
`x`, then there exists a boundary point `z` with `f(z) = τ` and
`f(D(z)) ≥ τ - ε`.

The defense can push boundary points at most `ε` below threshold. For
`ε = 0`, this recovers the exact score-preserving result.
-/
theorem eps_relaxed_boundary_fixation
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    {ε : ℝ} (_hε : 0 ≤ ε)
    (h_eps_score : ∀ x, f x < τ → |f (D x) - f x| ≤ ε)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ∃ z : X, f z = τ ∧ f (D z) ≥ τ - ε := by
  -- Same boundary point existence as before
  have h_not_closed : ¬ IsClosed {x : X | f x < τ} := by
    intro h_closed
    have h_open : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
    have h_clopen : IsClopen {x : X | f x < τ} := ⟨h_closed, h_open⟩
    rcases isClopen_iff.mp h_clopen with h_empty | h_univ
    · obtain ⟨a, ha⟩ := h_safe_ne
      have : a ∈ ({x : X | f x < τ} : Set X) := ha
      rw [h_empty] at this; exact this
    · obtain ⟨b, hb⟩ := h_unsafe_ne
      have : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
      simp only [Set.mem_setOf_eq] at this; linarith
  have h_strict : {x : X | f x < τ} ⊂ closure {x : X | f x < τ} := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨subset_closure, fun h_eq => h_not_closed (h_eq ▸ isClosed_closure)⟩
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} := by
      apply closure_minimal
      · intro x (hx : f x < τ); exact le_of_lt hx
      · exact isClosed_le hf continuous_const
    exact this hz_clos
  simp only [Set.mem_setOf_eq] at hz_not_safe
  have hz_ge : f z ≥ τ := not_lt.mp hz_not_safe
  have hz_eq : f z = τ := le_antisymm hz_le hz_ge
  -- Apply the ε bound
  have hbound := eps_score_preserving_extends_to_closure hD hf h_eps_score z hz_clos
  rw [hz_eq] at hbound
  exact ⟨z, hz_eq, hbound⟩


/-! ## 3. Safe-preserving (D(S_τ) ⊆ S_τ) is too weak — counterexample -/

/--
A constant defense mapping everything to a fixed safe point is continuous,
maps safe inputs to safe inputs, and is complete — showing that
`D(S_τ) ⊆ S_τ` alone does not imply boundary fixation.
-/
theorem safe_preserving_admits_complete_defense
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {τ : ℝ}
    {x₀ : X} (hx₀ : f x₀ < τ) :
    let D := fun (_ : X) => x₀
    (Continuous D) ∧
    (∀ x, f x < τ → f (D x) < τ) ∧
    (∀ x, f (D x) < τ) := by
  refine ⟨continuous_const, fun _ _ => hx₀, fun _ => hx₀⟩


/-! ## 4. Strict utility preservation implies score preservation -/

/--
Strict utility preservation (`D(x) = x` on safe inputs) implies
score preservation, so the relaxed theorems generalize the original.
-/
theorem strict_implies_score_preserving
    {X : Type*} {D : X → X} {f : X → ℝ} {τ : ℝ}
    (h_strict : ∀ x, f x < τ → D x = x) :
    ∀ x, f x < τ → f (D x) = f x :=
  fun x hx => by rw [h_strict x hx]

/--
Strict utility preservation implies ε-score preservation for any ε ≥ 0.
-/
theorem strict_implies_eps_score_preserving
    {X : Type*} {D : X → X} {f : X → ℝ} {τ : ℝ}
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_strict : ∀ x, f x < τ → D x = x) :
    ∀ x, f x < τ → |f (D x) - f x| ≤ ε :=
  fun x hx => by rw [h_strict x hx]; simp only [sub_self, abs_zero]; exact hε


/-! ## 5. Summary theorem -/

/--
**Relaxed Defense Impossibility — Master Theorem.**

The impossibility holds under three levels of utility preservation:

- **Strict** (`D(x) = x`): `f(D(z)) = τ` (original MoF_08 result).
- **Score-preserving** (`f(D(x)) = f(x)`): `f(D(z)) = τ`.
- **ε-score-preserving** (`|f(D(x)) - f(x)| ≤ ε`): `f(D(z)) ≥ τ - ε`.

Only the degenerate `D(S_τ) ⊆ S_τ` (no score constraint) escapes,
at the cost of destroying all semantic content.
-/
theorem relaxed_defense_impossibility
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_eps_score : ∀ x, f x < τ → |f (D x) - f x| ≤ ε)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ∃ z : X, f z = τ ∧ f (D z) ≥ τ - ε := by
  exact eps_relaxed_boundary_fixation hD hf hε h_eps_score h_safe_ne h_unsafe_ne

end MoF
