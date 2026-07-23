import Mathlib

/-!
# Hallucination Trilemma — Part 9: Discrete Impossibility

Discrete analogues of the Hallucination Trilemma. These results work directly
on **finite** question sets without any topology, mirroring the structure of
`MoF_12_Discrete` for the prompt-injection trilemma.

## Setup

* `Q` — a (possibly finite) type of questions
* `A` — a type of answers
* `M : Q → A × ℝ` — a model: `(M q).1` is the answer, `(M q).2` the confidence
* `δ : Q × A → ℝ` — truth-distance: `δ ≤ 0` means the answer is correct,
  `δ > 0` means it is wrong, `δ = 0` is the boundary

## Results

1. `DiscreteFaithful`, `DiscreteCovering`, `DiscreteStrictCalibrated` —
   discrete versions of the trilemma conditions, with no continuity.

2. `strictCal_conf_trichotomy` — under strict calibration, every question
   falls into exactly one of three buckets: `(conf > 1/2, δ < 0)`,
   `(conf = 1/2, δ = 0)`, or `(conf < 1/2, δ > 0)`.

3. `discrete_partition` — for finite `Q`, the three buckets partition `Q`
   and their cardinalities sum to `Fintype.card Q`.

4. `discrete_trilemma_decisive_impossible` — if the model is *decisive*
   (never on the fence: `(M q).2 ≠ 1/2` for all `q`), strict calibration
   forces `δ ≠ 0` everywhere — there is no boundary question.

5. `discrete_two_partition` — under decisiveness, covering, and strict
   calibration, both `TrueQs` and `FalseQs` are non-empty.

6. `discrete_sign_change` — discrete IVT: any path `Fin (n+1) → ℝ` going
   from a strictly-negative start to a strictly-positive end has an
   adjacent pair `(i, i+1)` with `g i.castSucc < 0` and `g i.succ ≥ 0`.

7. `discrete_hallucination` — applied to the truth-distance along a path
   of questions: a finite path of questions starting in the true-region
   and ending in the false-region must contain a sign-change edge.

These results show the trilemma's geometric obstruction has a discrete
shadow: even without continuity, a model that ranges over both "true" and
"false" regions along a discrete path must, at some adjacency, leave the
true region — and a continuous extension of such a model would necessarily
cross `δ = 0` by IVT, breaking decisiveness.

All proofs are `sorry`-free.
-/

open Finset

noncomputable section

namespace HoF

/-! ## 1. Discrete versions of the trilemma conditions -/

/--
**DiscreteFaithful.** Whenever the model is confident (`conf > 1/2`),
its answer is correct (`δ ≤ 0`). No continuity is assumed.
-/
def DiscreteFaithful {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ q, (M q).2 > 1/2 → δ (q, (M q).1) ≤ 0

/--
**DiscreteCovering.** The model genuinely answers some questions correctly
(`δ < 0`) and some incorrectly (`δ > 0`).
-/
def DiscreteCovering {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  (∃ q, δ (q, (M q).1) < 0) ∧ (∃ q, δ (q, (M q).1) > 0)

/--
**DiscreteStrictCalibrated.** Confidence sign matches truth-distance sign,
strictly: `conf > 1/2 ↔ δ < 0` and `conf < 1/2 ↔ δ > 0`.
-/
def DiscreteStrictCalibrated {Q A : Type*}
    (M : Q → A × ℝ) (δ : Q × A → ℝ) : Prop :=
  ∀ q,
    ((M q).2 > 1/2 ↔ δ (q, (M q).1) < 0) ∧
    ((M q).2 < 1/2 ↔ δ (q, (M q).1) > 0)

/-! ## 2. Trichotomy of confidence under strict calibration -/

/--
**Sign trichotomy under strict calibration.** Every question falls into
one of three exclusive buckets according to the joint sign of confidence
and truth-distance.
-/
theorem strictCal_conf_trichotomy
    {Q A : Type*} (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (hCal : DiscreteStrictCalibrated M δ) (q : Q) :
    ((M q).2 > 1/2 ∧ δ (q, (M q).1) < 0) ∨
    ((M q).2 = 1/2 ∧ δ (q, (M q).1) = 0) ∨
    ((M q).2 < 1/2 ∧ δ (q, (M q).1) > 0) := by
  rcases lt_trichotomy (M q).2 (1/2) with hlt | heq | hgt
  · -- conf < 1/2 ⇒ δ > 0
    right; right
    exact ⟨hlt, (hCal q).2.mp hlt⟩
  · -- conf = 1/2 ⇒ δ = 0 (using both directions of strict cal)
    right; left
    refine ⟨heq, ?_⟩
    -- Show δ ≮ 0 and δ ≯ 0, hence δ = 0.
    have h1 : ¬ δ (q, (M q).1) < 0 := by
      intro hδ
      have : (M q).2 > 1/2 := (hCal q).1.mpr hδ
      linarith
    have h2 : ¬ δ (q, (M q).1) > 0 := by
      intro hδ
      have : (M q).2 < 1/2 := (hCal q).2.mpr hδ
      linarith
    rcases lt_trichotomy (δ (q, (M q).1)) 0 with hd | hd | hd
    · exact absurd hd h1
    · exact hd
    · exact absurd hd h2
  · -- conf > 1/2 ⇒ δ < 0
    left
    exact ⟨hgt, (hCal q).1.mp hgt⟩

/-! ## 3. Discrete capacity partition -/

/-- The set of questions the model answers correctly (strictly inside truth). -/
def TrueQs {Q A : Type*} [Fintype Q] [DecidableEq Q]
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    [DecidablePred fun q => δ (q, (M q).1) < 0] : Finset Q :=
  Finset.univ.filter (fun q => δ (q, (M q).1) < 0)

/-- The set of boundary questions: exactly on the truth-set boundary. -/
def BoundaryQs {Q A : Type*} [Fintype Q] [DecidableEq Q]
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    [DecidablePred fun q => δ (q, (M q).1) = 0] : Finset Q :=
  Finset.univ.filter (fun q => δ (q, (M q).1) = 0)

/-- The set of questions the model answers incorrectly. -/
def FalseQs {Q A : Type*} [Fintype Q] [DecidableEq Q]
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    [DecidablePred fun q => δ (q, (M q).1) > 0] : Finset Q :=
  Finset.univ.filter (fun q => δ (q, (M q).1) > 0)

/--
**Discrete capacity exhaustion.** For finite `Q`, `TrueQs ∪ BoundaryQs ∪ FalseQs`
covers all of `Q` exactly: the cardinalities sum to `Fintype.card Q`.

The proof is just `lt_trichotomy` applied at each `q`, plus disjointness
since the predicates are mutually exclusive.
-/
theorem discrete_partition
    {Q A : Type*} [Fintype Q] [DecidableEq Q]
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    [DecidablePred fun q => δ (q, (M q).1) < 0]
    [DecidablePred fun q => δ (q, (M q).1) = 0]
    [DecidablePred fun q => δ (q, (M q).1) > 0] :
    (TrueQs M δ).card + (BoundaryQs M δ).card + (FalseQs M δ).card =
      Fintype.card Q := by
  -- Use disjoint unions over the trichotomy of δ.
  have hTB : Disjoint (TrueQs M δ) (BoundaryQs M δ) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [TrueQs, BoundaryQs, Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
    linarith
  have hTF : Disjoint (TrueQs M δ) (FalseQs M δ) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [TrueQs, FalseQs, Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
    linarith
  have hBF : Disjoint (BoundaryQs M δ) (FalseQs M δ) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [BoundaryQs, FalseQs, Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
    linarith
  have hUnion :
      (TrueQs M δ) ∪ (BoundaryQs M δ) ∪ (FalseQs M δ) = (Finset.univ : Finset Q) := by
    apply Finset.eq_univ_iff_forall.mpr
    intro q
    simp only [Finset.mem_union, TrueQs, BoundaryQs, FalseQs,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_trichotomy (δ (q, (M q).1)) 0 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  -- Now compute cardinalities via disjoint unions.
  have hTB_disj : Disjoint (TrueQs M δ ∪ BoundaryQs M δ) (FalseQs M δ) :=
    Finset.disjoint_union_left.mpr ⟨hTF, hBF⟩
  have h1 : ((TrueQs M δ ∪ BoundaryQs M δ) ∪ FalseQs M δ).card =
            (TrueQs M δ ∪ BoundaryQs M δ).card + (FalseQs M δ).card :=
    Finset.card_union_of_disjoint hTB_disj
  have h2 : (TrueQs M δ ∪ BoundaryQs M δ).card =
            (TrueQs M δ).card + (BoundaryQs M δ).card :=
    Finset.card_union_of_disjoint hTB
  have h3 : ((TrueQs M δ ∪ BoundaryQs M δ) ∪ FalseQs M δ).card =
            Fintype.card Q := by
    rw [hUnion]
    exact Finset.card_univ
  -- Combine
  have : (TrueQs M δ).card + (BoundaryQs M δ).card + (FalseQs M δ).card =
         ((TrueQs M δ ∪ BoundaryQs M δ) ∪ FalseQs M δ).card := by
    rw [h1, h2]
  rw [this, h3]

/-! ## 4. Decisive models force `δ ≠ 0` everywhere -/

/--
**Discrete trilemma — decisive case.** If the model is "decisive"
(no question receives confidence exactly `1/2`) and strict calibration
holds, then no question lies on the truth-boundary.

This is the cleanest discrete shadow of the trilemma's geometric
obstruction. There is no contradiction in the discrete setting itself,
but a continuous extension of `M` over a connected `Q` would, by IVT,
hit `(M q).2 = 1/2` somewhere — and strict calibration would then
demand `δ = 0` at that question, violating the conclusion below.
-/
theorem discrete_trilemma_decisive_impossible
    {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    (_hF : DiscreteFaithful M δ)
    (_hC : DiscreteCovering M δ)
    (hCal : DiscreteStrictCalibrated M δ)
    (hDecisive : ∀ q, (M q).2 ≠ 1/2) :
    ∀ q, δ (q, (M q).1) ≠ 0 := by
  intro q hq
  -- From strict calibration trichotomy, δ = 0 forces conf = 1/2.
  rcases strictCal_conf_trichotomy M δ hCal q with
    ⟨_, hδ⟩ | ⟨hc, _⟩ | ⟨_, hδ⟩
  · linarith
  · exact hDecisive q hc
  · linarith

/-! ## 5. Decisive + Covering ⇒ both true and false sets non-empty -/

/--
**Discrete two-partition.** Under decisiveness, covering, and strict
calibration, both `TrueQs` and `FalseQs` are non-empty (and `BoundaryQs`
is empty by `discrete_trilemma_decisive_impossible`).
-/
theorem discrete_two_partition
    {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (M : Q → A × ℝ) (δ : Q × A → ℝ)
    [DecidablePred fun q => δ (q, (M q).1) < 0]
    [DecidablePred fun q => δ (q, (M q).1) > 0]
    (_hCal : DiscreteStrictCalibrated M δ)
    (hC : DiscreteCovering M δ)
    (_hDecisive : ∀ q, (M q).2 ≠ 1/2) :
    (TrueQs M δ).Nonempty ∧ (FalseQs M δ).Nonempty := by
  refine ⟨?_, ?_⟩
  · obtain ⟨qt, hqt⟩ := hC.1
    refine ⟨qt, ?_⟩
    simp only [TrueQs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hqt
  · obtain ⟨qf, hqf⟩ := hC.2
    refine ⟨qf, ?_⟩
    simp only [FalseQs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hqf

/-! ## 6. Discrete IVT (sign-change theorem) -/

/--
**Discrete IVT (sign-change form).** If `g : Fin (n+1) → ℝ` is strictly
negative at index `0` and strictly positive at index `n`, then there is
some adjacent pair `(i.castSucc, i.succ)` with `g` strictly negative on
the left and non-negative on the right.

Proof: pick the smallest index where `g` becomes non-negative. Since
`g 0 < 0`, this index is positive, and the predecessor still has `g < 0`.
-/
theorem discrete_sign_change
    {n : ℕ} (g : Fin (n + 1) → ℝ)
    (h_start : g 0 < 0) (h_end : g (Fin.last n) > 0) :
    ∃ i : Fin n, g i.castSucc < 0 ∧ g i.succ ≥ 0 := by
  -- Reduce to MoF-style discrete IVT proof: assume no sign change, derive that
  -- g is negative everywhere up to `Fin.last n`, contradicting `h_end`.
  by_contra h_no
  push_neg at h_no
  -- h_no : ∀ i : Fin n, g i.castSucc < 0 → g i.succ < 0
  -- Show by induction on k that g ⟨k, _⟩ < 0 for all k ≤ n.
  have h_all : ∀ k : ℕ, (hk : k < n + 1) → g ⟨k, hk⟩ < 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      -- g ⟨0, _⟩ = g 0
      have : (⟨0, by omega⟩ : Fin (n + 1)) = (0 : Fin (n + 1)) := rfl
      simpa [this] using h_start
    | succ k ih =>
      intro hk
      have hk' : k < n + 1 := by omega
      have hk_n : k < n := by omega
      have ih' : g ⟨k, hk'⟩ < 0 := ih hk'
      -- Apply h_no at index ⟨k, hk_n⟩ : Fin n.
      have hcs : (⟨k, hk_n⟩ : Fin n).castSucc = ⟨k, hk'⟩ := by
        apply Fin.ext; rfl
      have hsu : (⟨k, hk_n⟩ : Fin n).succ = ⟨k + 1, hk⟩ := by
        apply Fin.ext; rfl
      have h_left : g (⟨k, hk_n⟩ : Fin n).castSucc < 0 := by rw [hcs]; exact ih'
      have h_right : g (⟨k, hk_n⟩ : Fin n).succ < 0 := h_no ⟨k, hk_n⟩ h_left
      rw [hsu] at h_right
      exact h_right
  -- Specialize at k = n: contradicts h_end.
  have hn : g ⟨n, by omega⟩ < 0 := h_all n (by omega)
  have hlast : (Fin.last n : Fin (n + 1)) = ⟨n, by omega⟩ := rfl
  rw [hlast] at h_end
  linarith

/-! ## 7. Discrete hallucination: sign change of `δ` along a path -/

/--
**Discrete hallucination.** Apply `discrete_sign_change` to the truth-
distance evaluated along a finite path of questions. If the model is in
the truth-region at index `0` and outside it at index `n`, some adjacent
edge `(i.castSucc, i.succ)` witnesses the boundary jump.

Without continuity, the jump need not pass through `δ = 0` exactly; but
under strict calibration, this would correspond to a confidence drop
across `1/2` between two adjacent questions — the discrete shadow of the
continuous trilemma's IVT obstruction.
-/
theorem discrete_hallucination
    {A : Type*} {n : ℕ}
    (M : Fin (n + 1) → A × ℝ) (δ : Fin (n + 1) × A → ℝ)
    (h_start : δ (0, (M 0).1) < 0)
    (h_end : δ (Fin.last n, (M (Fin.last n)).1) > 0) :
    ∃ i : Fin n, δ (i.castSucc, (M i.castSucc).1) < 0 ∧
                 δ (i.succ, (M i.succ).1) ≥ 0 := by
  exact discrete_sign_change (fun q => δ (q, (M q).1)) h_start h_end

/-! ## 8. Summary

The discrete trilemma decomposes into three honest results:

* `strictCal_conf_trichotomy` and `discrete_partition` show that strict
  calibration partitions any finite question set into three buckets by
  joint sign of confidence and truth-distance.

* `discrete_trilemma_decisive_impossible` shows that *decisive* models
  (no `1/2` confidence) cannot have any boundary questions, and
  `discrete_two_partition` confirms both true- and false-buckets are
  non-empty under covering.

* `discrete_sign_change` and `discrete_hallucination` are the discrete
  IVT shadow of the trilemma. A finite path of questions from a
  truth-region question to a false-region question must contain an
  adjacency at which `δ` flips sign. A continuous extension of such a
  model would, by IVT, hit `δ = 0` exactly — and strict calibration
  would force `(M q).2 = 1/2` there, breaking decisiveness.

These constitute the complete discrete impossibility skeleton of the
Hallucination Trilemma.
-/

end HoF

end
