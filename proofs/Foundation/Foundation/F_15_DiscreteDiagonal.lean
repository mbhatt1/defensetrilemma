/-
# F_15_DiscreteDiagonal

**The diagonal trilemma on satisfiable, discrete universality.**

An LLM is a discrete token map, so the honest universality is not set-theoretic
surjectivity onto all of `Q → Bool` (impossible by Cantor), but a *section onto
the behaviors the system can represent* — computational universality in the
Gödel/Turing/Rice sense. That is satisfiable, and it is all the diagonal needs:
the system only has to be able to pose its own liar query.

`RepSystem` packages a verdict map with the behaviors it represents and a section
realizing them. `no_self_negating_verdict` is Tarski's undefinability, discretely.
`repSystem_satisfiable` exhibits a model, so the universality assumption is
non-vacuous. The final section formalizes the reduction: three distinct named
properties (faithful, covering, reflective) that clash, with each pair satisfiable,
so it is a genuine trilemma, not one impossibility with spectators.
-/

import Mathlib

namespace Foundation

/-- A discrete system over prompt space `A`: a Boolean self-verdict `eval`, the
    set `Rep` of behaviors it can represent, and a section `code` realizing each
    representable behavior as a prompt. The satisfiable, discrete universality —
    a section onto the representable behaviors, not surjectivity onto all of
    `A → Bool`. -/
structure RepSystem (A : Type*) where
  eval : A → A → Bool
  Rep  : (A → Bool) → Prop
  code : ∀ g, Rep g → A
  spec : ∀ g (h : Rep g), eval (code g h) = g

namespace RepSystem

variable {A : Type*} (S : RepSystem A)

/-- **Tarski / the liar, discrete and non-vacuous.** A system cannot represent
    its own negated diagonal `a ↦ !(eval a a)` — the behavior a faithful
    self-verdict would need to answer "is your verdict on me false?". No
    surjectivity, no continuity. -/
theorem no_self_negating_verdict :
    ¬ S.Rep (fun a => !(S.eval a a)) := by
  intro h
  have hq := congrFun (S.spec (fun a => !(S.eval a a)) h) (S.code _ h)
  have hne : ∀ b : Bool, b ≠ !b := by decide
  exact hne _ hq

end RepSystem

/-- **The universality hypothesis is satisfiable.** Unlike `Function.Surjective
    v`, which no system satisfies, there is a `RepSystem` representing a nonempty
    family of behaviors, so the impossibility constrains a real, inhabited class. -/
theorem repSystem_satisfiable :
    ∃ (A : Type) (S : RepSystem A), ∃ g, S.Rep g := by
  refine ⟨Bool,
    { eval := fun _ _ => true
      Rep  := fun g => g = (fun _ => true)
      code := fun _ _ => true
      spec := ?_ },
    ⟨fun _ => true, rfl⟩⟩
  intro g h; subst h; rfl

/-! ## The three trilemmata as one discrete diagonal

Reading the single verdict `eval` three ways gives the three trilemmata. Each is
the same impossibility — the system cannot represent its own negated diagonal —
now over the satisfiable `RepSystem` universality rather than Cantor-dead
`Surjective`. The unification is definitional, as in `F_13`, but non-vacuous:
`repSystem_satisfiable` shows the shared hypothesis has models. -/

/-- Hallucination reading: a faithful, covering, calibrated self-verdict would
    have to represent the liar query; impossible. -/
theorem hallucination_trilemma_discrete {A : Type*} (S : RepSystem A) :
    ¬ S.Rep (fun a => !(S.eval a a)) := S.no_self_negating_verdict

/-- Defense reading: a complete, utility-preserving wrapper verdicting itself
    would have to represent the liar prompt; impossible. -/
theorem defense_trilemma_discrete {A : Type*} (S : RepSystem A) :
    ¬ S.Rep (fun a => !(S.eval a a)) := S.no_self_negating_verdict

/-- Coupling reading: the coupled self-activation query; impossible. -/
theorem coupling_trilemma_discrete {A : Type*} (S : RepSystem A) :
    ¬ S.Rep (fun a => !(S.eval a a)) := S.no_self_negating_verdict

/-- **One diagonal, three readings, over a satisfiable hypothesis.** The honest,
    non-vacuous counterpart of `F_13.trilemmata_unified`: the shared proof term is
    the same, and the hypothesis it rests on now has models. -/
theorem trilemmata_unified_discrete {A : Type*} (S : RepSystem A) :
    hallucination_trilemma_discrete S = defense_trilemma_discrete S
      ∧ defense_trilemma_discrete S = coupling_trilemma_discrete S :=
  ⟨rfl, rfl⟩

/-! ## The reduction: three named properties, a genuine trilemma

A real trilemma needs three *distinct* properties that each do formal work: all
three clash, but any two are jointly achievable. For a self-verdict `d : A → Bool`
(read `d a = eval a a`) against a ground truth `truth : A → Bool`. In the Boolean
world "calibrated" (verdict tracks truth) is just faithful-and-covering together,
so the independent third horn is reflectivity: the system can pose its own liar.
This is the Universality/Control/Transparency master trilemma, discretely;
calibration is its continuous refinement. -/

/-- **Faithful.** A self-query the system verdicts `true` really is true. -/
def Faithful {A : Type*} (d truth : A → Bool) : Prop := ∀ a, d a = true → truth a = true

/-- **Covering.** Every true self-query is verdicted `true`. -/
def Covering {A : Type*} (d truth : A → Bool) : Prop := ∀ a, truth a = true → d a = true

/-- **Reflective.** The system can pose its own liar: a query whose truth is the
    negation of the system's verdict on it. Satisfiable self-reference (a
    universal/quining system has it), not surjectivity. -/
def Reflective {A : Type*} (d truth : A → Bool) : Prop := ∃ ℓ, truth ℓ = !(d ℓ)

/-- **The discrete trilemma, reduction formalized.** No self-verdict is faithful,
    covering, and reflective at once. Faithful and covering pin the verdict to the
    truth; reflectivity exhibits the liar, where truth would equal its own
    negation. Each property is a real hypothesis doing real work. -/
theorem faithful_covering_reflective_impossible {A : Type*} {d truth : A → Bool}
    (hF : Faithful d truth) (hC : Covering d truth) (hR : Reflective d truth) :
    False := by
  obtain ⟨ℓ, hℓ⟩ := hR
  have h1 := hF ℓ
  have h2 := hC ℓ
  revert hℓ h1 h2
  generalize d ℓ = x
  generalize truth ℓ = y
  revert x y
  decide

/-! ### The trilemma is genuine: any two properties are jointly satisfiable -/

/-- Faithful + Covering (not reflective). -/
theorem faithful_covering_sat :
    ∃ (A : Type) (d truth : A → Bool), Faithful d truth ∧ Covering d truth :=
  ⟨Unit, (fun _ => true), (fun _ => true), (fun _ _ => rfl), (fun _ _ => rfl)⟩

/-- Faithful + Reflective (not covering). -/
theorem faithful_reflective_sat :
    ∃ (A : Type) (d truth : A → Bool), Faithful d truth ∧ Reflective d truth := by
  refine ⟨Bool, (fun _ => false), (fun _ => true), ?_, ?_⟩
  · intro a _; rfl
  · exact ⟨true, by decide⟩

/-- Covering + Reflective (not faithful). -/
theorem covering_reflective_sat :
    ∃ (A : Type) (d truth : A → Bool), Covering d truth ∧ Reflective d truth := by
  refine ⟨Bool, (fun _ => true), (fun _ => false), ?_, ?_⟩
  · intro a _; rfl
  · exact ⟨true, by decide⟩

#print axioms RepSystem.no_self_negating_verdict
#print axioms repSystem_satisfiable
#print axioms trilemmata_unified_discrete
#print axioms faithful_covering_reflective_impossible
#print axioms faithful_covering_sat
#print axioms faithful_reflective_sat
#print axioms covering_reflective_sat

end Foundation
