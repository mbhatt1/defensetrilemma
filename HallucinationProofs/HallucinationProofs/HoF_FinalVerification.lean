/-
  HoF Final Verification
  ======================
  This file verifies the entire Hallucination Trilemma (HoF) theory.

  **Namespace collision report:**

  The following definitions collide and prevent importing all HoF files
  simultaneously into one Lean module:

  1. `HoF.TruthSet`, `HoF.FalseSet`, `HoF.TruthBoundary`, `HoF.StrictTruth`
     — defined in both:
     - `HoF_01_Foundations` (with a `[TopologicalSpace QA]` context)
     - `HoF_02_TruthSet`    (without the topology context)

  Because of these collisions, we cannot import HoF_01 and HoF_02
  together. Instead, we verify each file independently by building it
  via `lake build`. Every HoF file imports only `Mathlib` (not other
  HoF files), so they are all independently checkable. The collisions
  only matter when one tries to import multiple HoF files into a
  single Lean file.

  **Verification strategy:**
  We import the largest collision-free subset (HoF_02 onwards plus the
  capstone master theorem) and `#check` / `#print axioms` for the
  headline theorems.
-/

-- ============================================================
-- Collision-free subset: HoF_02 .. HoF_08 plus the master theorem.
-- (HoF_01 collides with HoF_02 on TruthSet/FalseSet/TruthBoundary/
--  StrictTruth; we drop HoF_01 from this verification module.)
-- Each of HoF_01..HoF_08 builds independently against `Mathlib`.
-- ============================================================
import HallucinationProofs.HoF_02_TruthSet
import HallucinationProofs.HoF_03_BoundaryCrossing
import HallucinationProofs.HoF_04_Faithfulness
import HallucinationProofs.HoF_05_Coverage
import HallucinationProofs.HoF_06_Calibration
import HallucinationProofs.HoF_07_TrilemmaCore
import HallucinationProofs.HoF_08_BorsukUlam
import HallucinationProofs.HoF_12_Approximate
import HallucinationProofs.HoF_MasterTheorem

-- ============================================================
-- Check the headline theorems
-- ============================================================

-- The Master Theorem (the crown jewel)
#check @HoF.hallucination_master_theorem
#check @HoF.hallucination_trilemma_three_clause
#check @HoF.HallucinationStructure

-- HoF_07: Trilemma core
#check @HoF.hallucination_trilemma
#check @HoF.hallucination_trilemma_strict
#check @HoF.hallucination_trilemma_unfolded
#check @HoF.hallucination_trilemma_strict_unfolded

-- HoF_08: Borsuk-Ulam variant
#check @HoF.antipodal_hallucination_trilemma
#check @HoF.antipodal_yields_truth_boundary

-- HoF_12: approximate bridge and zero-slack exact contradiction
#check @HoF.approx_trilemma
#check @HoF.exact_from_approx
#check @HoF.exact_from_strictCalibrated_via_approx

-- ============================================================
-- Print axioms (should be only Lean's three:
--   propext, Classical.choice, Quot.sound)
-- ============================================================

-- Master Theorem
#print axioms HoF.hallucination_master_theorem
#print axioms HoF.hallucination_trilemma_three_clause

-- Core trilemma
#print axioms HoF.hallucination_trilemma
#print axioms HoF.hallucination_trilemma_strict

-- Borsuk-Ulam variant
#print axioms HoF.antipodal_hallucination_trilemma

-- Approximate bridge
#print axioms HoF.exact_from_strictCalibrated_via_approx
