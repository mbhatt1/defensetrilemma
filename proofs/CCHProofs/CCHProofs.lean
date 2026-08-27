-- CCHProofs: The Capability-Control-Honesty Trilemma via Lawvere's theorem
-- A general impossibility theorem for AI safety: no system can simultaneously
-- be Universal, externally Controlled, and self-Transparent.
--
-- Each CCH_* file imports only `Mathlib` and is independently checkable by
-- `lake build`. Because several files re-state shared definitions
-- (`NonTrivial`, `Controller`, `diag`, `Transparent`, etc.) so they remain
-- self-contained, the entry point imports a maximal *collision-free* subset.
-- The omitted file (`CCH_01_Foundations`) is still built independently.

-- Foundations is checked independently; its core defs reappear in CCH_05/06.
-- import CCHProofs.CCH_01_Foundations

-- The Lawvere fixed-point theorem and its classical instances
import CCHProofs.CCH_02_Lawvere
import CCHProofs.CCH_03_Cantor
import CCHProofs.CCH_04_FixedPointFree

-- The three CCH properties as functional/operator conditions
import CCHProofs.CCH_05_Controllers
import CCHProofs.CCH_06_Transparency

-- The three corners of the trilemma, each a Lawvere instance
import CCHProofs.CCH_07_CornerUC
import CCHProofs.CCH_08_CornerUT
import CCHProofs.CCH_09_CornerCT

-- Capstone: bundled CCHStructure + master theorem + axiom verification
import CCHProofs.CCH_MasterTrilemma
import CCHProofs.CCH_FinalVerification

-- Direct application to LLMs as functions (the bridge is one definition).
import CCHProofs.CCH_LLM_Direct
