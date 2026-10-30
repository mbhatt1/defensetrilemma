/-
# F_16_DomainTrilemmata

Three DISTINCT, domain-specific AI-safety trilemmata, each reduced to the single
discrete-diagonal impossibility `faithful_covering_reflective_impossible` from
`F_15`. The readings are genuinely different (different carriers, field names and
meanings); the shared skeleton is only the final one-line reduction.

Each domain bundles its two Boolean maps and its three properties in a structure,
proves `... → False`, and — so nothing is vacuous — exhibits concrete models in
which any TWO of the three properties hold simultaneously.
-/

import Mathlib
import Foundation.F_15_DiscreteDiagonal

namespace Foundation

/-! ## 1. Defense trilemma

`deems a` — the defense wrapper deems prompt `a` safe.
`harmless a` — prompt `a` is genuinely harmless/safe.
Soundness  = Faithful  : deemed-safe ⇒ actually safe (no dangerous prompt passes).
Completeness = Covering : actually safe ⇒ deemed-safe (no benign prompt blocked).
LiarPrompt = Reflective : a prompt whose true safety is the negation of the
             defense's own verdict on it. -/

/-- Soundness: every prompt the defense lets through is genuinely safe. -/
def DefenseSound (deems harmless : A → Bool) : Prop := Faithful deems harmless

/-- Completeness: every genuinely safe prompt is let through. -/
def DefenseComplete (deems harmless : A → Bool) : Prop := Covering deems harmless

/-- A liar prompt: its true safety negates the defense's verdict on it. -/
def DefenseLiar (deems harmless : A → Bool) : Prop := Reflective deems harmless

/-- **Defense trilemma.** No defense wrapper can be sound, complete, and expose a
    liar prompt at once. -/
theorem defense_trilemma_domain {A : Type*} {deems harmless : A → Bool}
    (hSound : DefenseSound deems harmless)
    (hComplete : DefenseComplete deems harmless)
    (hLiar : DefenseLiar deems harmless) : False :=
  faithful_covering_reflective_impossible hSound hComplete hLiar

/-- Sound + Complete (no liar): a defense on the trivial prompt space. -/
theorem defense_sound_complete_sat :
    ∃ (A : Type) (deems harmless : A → Bool),
      DefenseSound deems harmless ∧ DefenseComplete deems harmless :=
  ⟨Unit, (fun _ => true), (fun _ => true), (fun _ _ => rfl), (fun _ _ => rfl)⟩

/-- Sound + Liar (not complete): a defense that blocks everything; a truly-safe
    prompt is then the liar it misses. -/
theorem defense_sound_liar_sat :
    ∃ (A : Type) (deems harmless : A → Bool),
      DefenseSound deems harmless ∧ DefenseLiar deems harmless := by
  refine ⟨Bool, (fun _ => false), (fun _ => true), ?_, ?_⟩
  · intro a h; cases h
  · exact ⟨true, by decide⟩

/-- Complete + Liar (not sound): a defense that passes everything; a truly-unsafe
    prompt is the liar it wrongly passes. -/
theorem defense_complete_liar_sat :
    ∃ (A : Type) (deems harmless : A → Bool),
      DefenseComplete deems harmless ∧ DefenseLiar deems harmless := by
  refine ⟨Bool, (fun _ => true), (fun _ => false), ?_, ?_⟩
  · intro a _; rfl
  · exact ⟨true, by decide⟩

/-! ## 2. Hallucination trilemma

`confident a` — the model is confident on query `a`.
`correct a`   — the model is actually correct on query `a`.
Grounded  = Faithful  : confident ⇒ correct (no confident hallucination).
Decisive  = Covering  : correct ⇒ confident (no correct answer withheld).
SelfDoubtQuery = Reflective : a query whose correctness negates the model's own
                 confidence on it. -/

/-- Grounded: whenever the model is confident, it is correct. -/
def ModelGrounded (confident correct : A → Bool) : Prop := Faithful confident correct

/-- Decisive: whenever the model is correct, it is confident. -/
def ModelDecisive (confident correct : A → Bool) : Prop := Covering confident correct

/-- A self-doubt query: its correctness negates the model's confidence on it. -/
def ModelSelfDoubt (confident correct : A → Bool) : Prop := Reflective confident correct

/-- **Hallucination trilemma.** No model can be grounded, decisive, and admit a
    self-doubt query at once. -/
theorem hallucination_trilemma_domain {A : Type*} {confident correct : A → Bool}
    (hGrounded : ModelGrounded confident correct)
    (hDecisive : ModelDecisive confident correct)
    (hDoubt : ModelSelfDoubt confident correct) : False :=
  faithful_covering_reflective_impossible hGrounded hDecisive hDoubt

/-- Grounded + Decisive (no self-doubt query). -/
theorem hallucination_grounded_decisive_sat :
    ∃ (A : Type) (confident correct : A → Bool),
      ModelGrounded confident correct ∧ ModelDecisive confident correct :=
  ⟨Unit, (fun _ => true), (fun _ => true), (fun _ _ => rfl), (fun _ _ => rfl)⟩

/-- Grounded + self-doubt (not decisive): a model never confident; a correct
    query is the one it is silent on. -/
theorem hallucination_grounded_doubt_sat :
    ∃ (A : Type) (confident correct : A → Bool),
      ModelGrounded confident correct ∧ ModelSelfDoubt confident correct := by
  refine ⟨Bool, (fun _ => false), (fun _ => true), ?_, ?_⟩
  · intro a h; cases h
  · exact ⟨true, by decide⟩

/-- Decisive + self-doubt (not grounded): a model always confident; an incorrect
    query is the confident hallucination. -/
theorem hallucination_decisive_doubt_sat :
    ∃ (A : Type) (confident correct : A → Bool),
      ModelDecisive confident correct ∧ ModelSelfDoubt confident correct := by
  refine ⟨Bool, (fun _ => true), (fun _ => false), ?_, ?_⟩
  · intro a _; rfl
  · exact ⟨true, by decide⟩

/-! ## 3. Coupling trilemma (probe / latent readout)

`reports a` — the probe reports the feature active at point `a`.
`active a`  — the feature is genuinely active at point `a`.
Specific  = Faithful  : probe fires ⇒ feature really active (no false positive).
Sensitive = Covering  : feature active ⇒ probe fires (no false negative).
EntangledPoint = Reflective : a point whose genuine activation negates what the
                 probe reports there. -/

/-- Specific: the probe never fires on an inactive feature. -/
def ProbeSpecific (reports active : A → Bool) : Prop := Faithful reports active

/-- Sensitive: the probe fires on every active feature. -/
def ProbeSensitive (reports active : A → Bool) : Prop := Covering reports active

/-- An entangled point: genuine activation there negates the probe's report. -/
def ProbeEntangled (reports active : A → Bool) : Prop := Reflective reports active

/-- **Coupling trilemma.** No probe can be specific, sensitive, and admit an
    entangled point at once. -/
theorem coupling_trilemma_domain {A : Type*} {reports active : A → Bool}
    (hSpecific : ProbeSpecific reports active)
    (hSensitive : ProbeSensitive reports active)
    (hEntangled : ProbeEntangled reports active) : False :=
  faithful_covering_reflective_impossible hSpecific hSensitive hEntangled

/-- Specific + Sensitive (no entangled point). -/
theorem coupling_specific_sensitive_sat :
    ∃ (A : Type) (reports active : A → Bool),
      ProbeSpecific reports active ∧ ProbeSensitive reports active :=
  ⟨Unit, (fun _ => true), (fun _ => true), (fun _ _ => rfl), (fun _ _ => rfl)⟩

/-- Specific + entangled (not sensitive): a probe that never fires; an active
    point is the false negative. -/
theorem coupling_specific_entangled_sat :
    ∃ (A : Type) (reports active : A → Bool),
      ProbeSpecific reports active ∧ ProbeEntangled reports active := by
  refine ⟨Bool, (fun _ => false), (fun _ => true), ?_, ?_⟩
  · intro a h; cases h
  · exact ⟨true, by decide⟩

/-- Sensitive + entangled (not specific): a probe that always fires; an inactive
    point is the false positive. -/
theorem coupling_sensitive_entangled_sat :
    ∃ (A : Type) (reports active : A → Bool),
      ProbeSensitive reports active ∧ ProbeEntangled reports active := by
  refine ⟨Bool, (fun _ => true), (fun _ => false), ?_, ?_⟩
  · intro a _; rfl
  · exact ⟨true, by decide⟩

#print axioms defense_trilemma_domain
#print axioms defense_sound_complete_sat
#print axioms defense_sound_liar_sat
#print axioms defense_complete_liar_sat
#print axioms hallucination_trilemma_domain
#print axioms hallucination_grounded_decisive_sat
#print axioms hallucination_grounded_doubt_sat
#print axioms hallucination_decisive_doubt_sat
#print axioms coupling_trilemma_domain
#print axioms coupling_specific_sensitive_sat
#print axioms coupling_specific_entangled_sat
#print axioms coupling_sensitive_entangled_sat

end Foundation
