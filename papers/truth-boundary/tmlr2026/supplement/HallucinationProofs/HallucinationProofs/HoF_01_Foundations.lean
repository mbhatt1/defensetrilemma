/-
  HoF Part 1: Foundations
  ========================
  Foundational definitions and basic topological properties for the
  "Hallucination of Failure" (HoF) theory of LLM hallucination.

  Generalized to work over any topological space `QA` with a continuous
  truth-distance function `δ : QA → ℝ`. No dependence on the eventual
  product structure `Q × A`; that is supplied by later files.

  We define:
    - TruthSet, FalseSet, TruthBoundary, StrictTruth
    - answerOf, confOf, HighConfRegion (model-level definitions)
  and prove basic topological properties (openness, closedness,
  disjointness, partition, subset relations).

  The file ends with a `HallucinationSetup` structure bundling the
  shared assumptions used across the HoF series.
-/

import Mathlib

open Set Topology Filter

namespace HoF

variable {QA : Type*} [TopologicalSpace QA]

/-! ## 1. Regions defined by truth-distance -/

/-- The truth set: points where truth-distance is non-positive (true). -/
def TruthSet (δ : QA → ℝ) : Set QA :=
  {p : QA | δ p ≤ 0}

/-- The false set: points where truth-distance is strictly positive. -/
def FalseSet (δ : QA → ℝ) : Set QA :=
  {p : QA | δ p > 0}

/-- The truth boundary: points where truth-distance is exactly zero. -/
def TruthBoundary (δ : QA → ℝ) : Set QA :=
  {p : QA | δ p = 0}

/-- The strict truth: points where truth-distance is strictly negative. -/
def StrictTruth (δ : QA → ℝ) : Set QA :=
  {p : QA | δ p < 0}

/-! ## 2. Model-level definitions -/

variable {Q A : Type*}

/-- The answer projection of a model `M : Q → A × ℝ`. -/
def answerOf (M : Q → A × ℝ) (q : Q) : A :=
  (M q).1

/-- The confidence projection of a model `M : Q → A × ℝ`. -/
def confOf (M : Q → A × ℝ) (q : Q) : ℝ :=
  (M q).2

/-- The high-confidence region: questions where the model's confidence is
at least `c`. -/
def HighConfRegion (M : Q → A × ℝ) (c : ℝ) : Set Q :=
  {q : Q | confOf M q ≥ c}

/-! ## 3. Membership lemmas -/

omit [TopologicalSpace QA] in
theorem mem_truthSet (δ : QA → ℝ) (p : QA) :
    p ∈ TruthSet δ ↔ δ p ≤ 0 :=
  Iff.rfl

omit [TopologicalSpace QA] in
theorem mem_falseSet (δ : QA → ℝ) (p : QA) :
    p ∈ FalseSet δ ↔ δ p > 0 :=
  Iff.rfl

omit [TopologicalSpace QA] in
theorem mem_truthBoundary (δ : QA → ℝ) (p : QA) :
    p ∈ TruthBoundary δ ↔ δ p = 0 :=
  Iff.rfl

omit [TopologicalSpace QA] in
theorem mem_strictTruth (δ : QA → ℝ) (p : QA) :
    p ∈ StrictTruth δ ↔ δ p < 0 :=
  Iff.rfl

theorem mem_highConfRegion (M : Q → A × ℝ) (c : ℝ) (q : Q) :
    q ∈ HighConfRegion M c ↔ confOf M q ≥ c :=
  Iff.rfl

/-! ## 4. Openness and Closedness -/

/-- The truth set is closed (preimage of `Iic 0` under a continuous map). -/
theorem truthSet_isClosed {δ : QA → ℝ} (hδ : Continuous δ) :
    IsClosed (TruthSet δ) :=
  isClosed_le hδ continuous_const

/-- The false set is open (preimage of `Ioi 0` under a continuous map). -/
theorem falseSet_isOpen {δ : QA → ℝ} (hδ : Continuous δ) :
    IsOpen (FalseSet δ) :=
  isOpen_lt continuous_const hδ

/-- The truth boundary is closed (preimage of `{0}` under a continuous map). -/
theorem truthBoundary_isClosed {δ : QA → ℝ} (hδ : Continuous δ) :
    IsClosed (TruthBoundary δ) :=
  isClosed_eq hδ continuous_const

/-- The strict truth region is open (preimage of `Iio 0` under a continuous map). -/
theorem strictTruth_isOpen {δ : QA → ℝ} (hδ : Continuous δ) :
    IsOpen (StrictTruth δ) :=
  isOpen_lt hδ continuous_const

/-- The high-confidence region is closed when the confidence is continuous. -/
theorem highConfRegion_isClosed [TopologicalSpace Q]
    {M : Q → A × ℝ} (hM_conf : Continuous (confOf M)) (c : ℝ) :
    IsClosed (HighConfRegion M c) :=
  isClosed_le continuous_const hM_conf

/-! ## 5. Trichotomy / Partition -/

omit [TopologicalSpace QA] in
/-- Every point belongs to exactly one of `StrictTruth`, `TruthBoundary`,
or `FalseSet`. -/
theorem truth_partition (δ : QA → ℝ) (p : QA) :
    (p ∈ StrictTruth δ ∧ p ∉ TruthBoundary δ ∧ p ∉ FalseSet δ) ∨
    (p ∉ StrictTruth δ ∧ p ∈ TruthBoundary δ ∧ p ∉ FalseSet δ) ∨
    (p ∉ StrictTruth δ ∧ p ∉ TruthBoundary δ ∧ p ∈ FalseSet δ) := by
  simp only [mem_strictTruth, mem_truthBoundary, mem_falseSet]
  rcases lt_trichotomy (δ p) 0 with h | h | h
  · left; exact ⟨h, ne_of_lt h, not_lt.mpr (le_of_lt h)⟩
  · right; left; exact ⟨not_lt.mpr (ge_of_eq h), h, not_lt.mpr (h ▸ le_refl _)⟩
  · right; right; exact ⟨not_lt.mpr (le_of_lt h), ne_of_gt h, h⟩

/-! ## 6. Disjointness -/

omit [TopologicalSpace QA] in
/-- The strict truth and false set are disjoint. -/
theorem strictTruth_falseSet_disjoint (δ : QA → ℝ) :
    Disjoint (StrictTruth δ) (FalseSet δ) := by
  rw [Set.disjoint_iff]
  intro p ⟨hlt, hgt⟩
  simp only [mem_strictTruth, mem_falseSet] at hlt hgt
  exact absurd (lt_trans hlt hgt) (lt_irrefl _)

omit [TopologicalSpace QA] in
/-- The truth boundary and false set are disjoint. -/
theorem truthBoundary_falseSet_disjoint (δ : QA → ℝ) :
    Disjoint (TruthBoundary δ) (FalseSet δ) := by
  rw [Set.disjoint_iff]
  intro p ⟨heq, hgt⟩
  simp only [mem_truthBoundary, mem_falseSet] at heq hgt
  exact absurd (heq ▸ hgt) (lt_irrefl _)

/-! ## 7. TruthSet decomposition -/

omit [TopologicalSpace QA] in
/-- The strict truth region is contained in the truth set. -/
theorem strictTruth_subset_truthSet (δ : QA → ℝ) :
    StrictTruth δ ⊆ TruthSet δ := by
  intro p hp
  rw [mem_strictTruth] at hp
  rw [mem_truthSet]
  exact le_of_lt hp

omit [TopologicalSpace QA] in
/-- The truth boundary is contained in the truth set. -/
theorem truthBoundary_subset_truthSet (δ : QA → ℝ) :
    TruthBoundary δ ⊆ TruthSet δ := by
  intro p hp
  rw [mem_truthBoundary] at hp
  rw [mem_truthSet]
  exact le_of_eq hp

omit [TopologicalSpace QA] in
/-- The truth set is the union of the strict truth and the truth boundary. -/
theorem truthSet_eq_strictTruth_union_boundary (δ : QA → ℝ) :
    TruthSet δ = StrictTruth δ ∪ TruthBoundary δ := by
  ext p
  simp only [TruthSet, StrictTruth, TruthBoundary, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · left; exact hlt
    · right; exact heq
  · rintro (hlt | heq)
    · exact le_of_lt hlt
    · exact le_of_eq heq

omit [TopologicalSpace QA] in
/-- The truth set and the false set partition the space. -/
theorem truthSet_union_falseSet (δ : QA → ℝ) :
    TruthSet δ ∪ FalseSet δ = Set.univ := by
  ext p
  simp only [TruthSet, FalseSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_univ, iff_true]
  exact le_or_gt (δ p) 0

omit [TopologicalSpace QA] in
/-- The truth set and the false set are disjoint. -/
theorem truthSet_falseSet_disjoint (δ : QA → ℝ) :
    Disjoint (TruthSet δ) (FalseSet δ) := by
  rw [Set.disjoint_iff]
  intro p ⟨hle, hgt⟩
  simp only [mem_truthSet, mem_falseSet] at hle hgt
  exact absurd (lt_of_lt_of_le hgt hle) (lt_irrefl _)

/-! ## 8. The Hallucination Setup -/

/-- The bundled data for the hallucination trilemma:
a connected question space `Q`, an answer space `A`, a continuous
model `M : Q → A × ℝ` with continuous answer and confidence projections,
a continuous truth-distance `δ : Q × A → ℝ`, and witnesses that the model
produces both strictly true and strictly false answers somewhere on `Q`. -/
structure HallucinationSetup where
  /-- Question space -/
  Q : Type*
  /-- Answer space -/
  A : Type*
  /-- Topological structure on `Q` -/
  topQ : TopologicalSpace Q
  /-- Topological structure on `A` -/
  topA : TopologicalSpace A
  /-- `Q` is connected -/
  connQ : @ConnectedSpace Q topQ
  /-- The model with confidence -/
  M : Q → A × ℝ
  /-- The answer projection is continuous -/
  hM_ans : @Continuous Q A topQ topA (fun q => (M q).1)
  /-- The confidence projection is continuous -/
  hM_conf : @Continuous Q ℝ topQ _ (fun q => (M q).2)
  /-- The truth-distance function -/
  δ : Q × A → ℝ
  /-- The truth-distance is continuous -/
  hδ : @Continuous (Q × A) ℝ (@instTopologicalSpaceProd Q A topQ topA) _ δ
  /-- There is a question on which the model is strictly true. -/
  true_witness : ∃ q : Q, δ (q, (M q).1) < 0
  /-- There is a question on which the model is strictly false. -/
  false_witness : ∃ q : Q, δ (q, (M q).1) > 0

end HoF
