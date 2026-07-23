-- Foundation: Toward a Gödel/Turing/Cook-Levin–level foundation for AI safety
--
-- A family of structural impossibility theorems, each derived from Lawvere's
-- diagonal applied with a different parameter. Together they characterize
-- the achievable region of capability/control/honesty/verifiability/
-- specifiability/composability for any sufficiently expressive system.

-- The master engine: Lawvere's diagonal in clean form.
import Foundation.F_01_LawvereCore

-- Rice's theorem: no nontrivial property is decidable.
import Foundation.F_02_RiceTheorem

-- The verification limit: bounded verifiers can't decide universal systems.
import Foundation.F_03_VerificationLimit

-- The Calibration Trilemma re-derived as a Lawvere instance.
import Foundation.F_04_CalibrationUnified

-- Deceptive alignment as Lawvere applied to training-reward controller.
import Foundation.F_05_DeceptionTheorem

-- Oversight hierarchies inherit the trilemma at every level.
import Foundation.F_06_OversightHierarchy

-- Composition of corner-systems fails to preserve corners.
import Foundation.F_07_CompositionFailure

-- Finite specifications cover measure-zero of universal behavior space.
import Foundation.F_08_SpecificationBound

-- Quantitative degradation: ε-approximate trilemma inequality.
import Foundation.F_09_QuantitativeDegradation

-- Master foundation theorem + final axiom verification.
import Foundation.F_10_MasterFoundation
import Foundation.F_10_FinalVerification
