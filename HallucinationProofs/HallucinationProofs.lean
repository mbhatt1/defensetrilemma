-- HallucinationProofs: Topological Theory of Hallucination Trilemma
-- A faithful, calibrated, covering language model is topologically impossible.
--
-- Each HoF_* file is self-contained and imports only `Mathlib`. Several files
-- introduce overlapping `HoF`-namespace definitions (TruthSet, FalseSet,
-- TruthBoundary, StrictTruth, etc.) — they are intentional duplicates so that
-- each file can be machine-checked independently. Because of this, the
-- top-level entry file imports a maximal *collision-free* subset; the omitted
-- file (`HoF_01_Foundations`) is still built independently by `lake build`.

-- Foundations is checked independently; HoF_02 re-states its core defs
-- to keep the topology files self-contained.
-- import HallucinationProofs.HoF_01_Foundations

-- Topology of the truth set, IVT-style boundary crossings.
import HallucinationProofs.HoF_02_TruthSet
import HallucinationProofs.HoF_03_BoundaryCrossing

-- The three trilemma conditions.
import HallucinationProofs.HoF_04_Faithfulness
import HallucinationProofs.HoF_05_Coverage
import HallucinationProofs.HoF_06_Calibration

-- Core impossibility, antipodal obstruction, discrete shadow.
import HallucinationProofs.HoF_07_TrilemmaCore
import HallucinationProofs.HoF_08_BorsukUlam
import HallucinationProofs.HoF_09_Discrete

-- Pure discrete impossibility: no topology, no finiteness, no paths.
import HallucinationProofs.HoF_10_PureDiscrete

-- Multi-turn and probabilistic extensions.
import HallucinationProofs.HoF_11_MultiTurnProbabilistic

-- Approximate bridge: ε-calibration connects idealized theorem to real models.
import HallucinationProofs.HoF_12_Approximate

-- Capstone: bundled structure + master theorem + final axiom verification.
import HallucinationProofs.HoF_MasterTheorem
import HallucinationProofs.HoF_FinalVerification

-- Instantiation: the trilemma applied to prompt embedding space ℝᵈ.
import HallucinationProofs.HoF_Instantiation_PromptSpace
