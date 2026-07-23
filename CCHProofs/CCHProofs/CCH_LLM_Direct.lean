/-
  CCH_LLM_Direct.lean
  ===================
  An LLM IS a function. Treating it as one, the CCH Trilemma applies directly.

  Mathematically, an LLM is a map `M : Prompt → Prompt → Token`. The
  double-argument shape is not a fiction: the first slot is the system
  prompt or context (which can encode the system's self-description and
  behavioral instructions), and the second is the user query. Currying the
  natural `Prompt × Prompt → Token` shape gives exactly the type Lawvere's
  theorem operates on.

  *In-context learning* is the empirical claim that, for a sufficiently
  capable LLM, every desired behavior `f : Prompt → Token` is realized by
  some appropriate system prompt — i.e., the curried LLM is surjective
  onto `Prompt → Token`.

  Given that, the trilemma applies *directly* to LLMs: no metric, no
  continuous extension, no quantitative degradation argument. The bridge
  from abstract Lawvere to LLM impossibility is one definition and a
  one-line proof.

  This file also gives an *approximate* version for ε-ICL-universal
  systems, where the trilemma yields an ε-approximate fixed point — the
  bridge to real systems that aren't perfectly surjective.
-/

import Mathlib

namespace CCH

/-! ## 1. An LLM as a function -/

/-- An LLM as a curried map. The first prompt is the *system prompt* or
    context (encoding the system's behavioral specification); the second
    is the *user query*. The type captures what an LLM mathematically *is*. -/
abbrev LLM (Prompt Token : Type*) : Type _ := Prompt → Prompt → Token

/-! ## 2. In-context learning as surjectivity -/

/-- **In-context learning universality.** For every desired behavior
    `g : Prompt → Token`, some system prompt `p` makes the LLM realize
    `g` — i.e., `M p q = g q` for all queries `q`.

    This is exactly `Function.Surjective M` for the curried `M`. It is
    the formal counterpart of the empirical claim that LLMs can be
    *prompted* into any specifiable behavior. -/
def ICLUniversal {Prompt Token : Type*} (M : LLM Prompt Token) : Prop :=
  Function.Surjective M

theorem iclUniversal_iff {Prompt Token : Type*} (M : LLM Prompt Token) :
    ICLUniversal M ↔ Function.Surjective M := Iff.rfl

/-! ## 3. Lawvere's diagonal applied directly to LLMs -/

/-- **The diagonal fixed-point theorem for LLMs.**
    An ICL-universal LLM has, for every output transformation `t`, some
    system prompt `p` where applying the LLM to `p` *as both system prompt
    and user query* yields a fixed point of `t`.

    Proof: pick the system prompt that realizes the function
    `q ↦ t (M q q)`. By construction, the LLM's self-application at that
    prompt equals `t` of itself. -/
theorem LLM_diagonal_fixed_point
    {Prompt Token : Type*}
    (M : LLM Prompt Token) (hM : ICLUniversal M)
    (t : Token → Token) :
    ∃ p : Prompt, M p p = t (M p p) := by
  obtain ⟨p, hp⟩ := hM (fun q => t (M q q))
  exact ⟨p, congrFun hp p⟩

/-- An ICL-universal LLM cannot avoid the fixed points of any output
    transformation. Equivalently: no fixed-point-free `t` is consistent
    with full ICL universality. -/
theorem LLM_no_fixed_point_free
    {Prompt Token : Type*}
    (M : LLM Prompt Token) (hM : ICLUniversal M)
    (t : Token → Token) (ht : ∀ x, t x ≠ x) : False := by
  obtain ⟨p, hp⟩ := LLM_diagonal_fixed_point M hM t
  exact ht (M p p) hp.symm

/-! ## 4. The CCH Trilemma applied directly to LLMs -/

/-- **The CCH Trilemma for LLMs.**
    No LLM can simultaneously be:

    1. **ICL-universal** — every behavior is realizable by some prompt.
    2. **Controlled** — for some output transformation `t` (the "forbidden
       behavior"), the LLM's self-introspection `introspect p` never lands
       on a `t`-fixed-point.
    3. **Transparent** — the LLM's actual self-application `M p p` matches
       its self-introspection `introspect p`.

    The proof is one application of `LLM_diagonal_fixed_point`. -/
theorem LLM_trilemma
    {Prompt Token : Type*}
    (M : LLM Prompt Token)
    (t : Token → Token)
    (introspect : Prompt → Token)
    (hU : ICLUniversal M)
    (hC : ∀ p, t (introspect p) ≠ introspect p)
    (hT : ∀ p, M p p = introspect p) : False := by
  obtain ⟨p, hp⟩ := LLM_diagonal_fixed_point M hU t
  rw [hT p] at hp
  exact hC p hp.symm

/-! ## 5. Three corner readings -/

/-- **Corner 1.** ICL-universal + Controlled ⇒ not Transparent. -/
theorem LLM_corner_UC
    {Prompt Token : Type*}
    (M : LLM Prompt Token)
    (t : Token → Token)
    (introspect : Prompt → Token)
    (hU : ICLUniversal M)
    (hC : ∀ p, t (introspect p) ≠ introspect p) :
    ¬ (∀ p, M p p = introspect p) :=
  fun hT => LLM_trilemma M t introspect hU hC hT

/-- **Corner 2.** ICL-universal + Transparent ⇒ not Controlled. -/
theorem LLM_corner_UT
    {Prompt Token : Type*}
    (M : LLM Prompt Token)
    (t : Token → Token)
    (introspect : Prompt → Token)
    (hU : ICLUniversal M)
    (hT : ∀ p, M p p = introspect p) :
    ¬ (∀ p, t (introspect p) ≠ introspect p) :=
  fun hC => LLM_trilemma M t introspect hU hC hT

/-- **Corner 3.** Controlled + Transparent ⇒ not ICL-universal. -/
theorem LLM_corner_CT
    {Prompt Token : Type*}
    (M : LLM Prompt Token)
    (t : Token → Token)
    (introspect : Prompt → Token)
    (hC : ∀ p, t (introspect p) ≠ introspect p)
    (hT : ∀ p, M p p = introspect p) :
    ¬ ICLUniversal M :=
  fun hU => LLM_trilemma M t introspect hU hC hT

/-! ## 6. The Boolean specialization (safety LLMs) -/

/-- **Safety-judgment specialization.** An LLM whose output is a binary
    safety judgment, viewed as a function `Prompt → Prompt → Bool`, cannot
    simultaneously: (1) realize every `Prompt → Bool` judgment via prompting,
    and (2) admit a self-introspection that always disagrees with negation.

    This is Cantor's theorem applied to the safety setting:
    *no universal safety classifier is also reliably self-honest*. -/
theorem LLM_safety_corner_UC
    {Prompt : Type*}
    (M : LLM Prompt Bool)
    (introspect : Prompt → Bool)
    (hU : ICLUniversal M)
    (hC : ∀ p, !(introspect p) ≠ introspect p) :
    ¬ (∀ p, M p p = introspect p) := by
  intro hT
  -- Bypass `LLM_diagonal_fixed_point` to avoid Bool beta-reduction quirks.
  obtain ⟨p, hp⟩ := hU (fun q => !(M q q))
  have h : M p p = !(M p p) := congrFun hp p
  rw [hT p] at h
  -- h : introspect p = !(introspect p); contradicts hC p
  cases hb : introspect p <;> rw [hb] at h <;> simp at h

/-- The boolean negation controller is automatically non-trivial. -/
theorem bool_not_controller : ∀ b : Bool, !b ≠ b := by
  intro b; cases b <;> simp

/-- **Universal safety LLM has a self-misclassification.**
    For any ICL-universal `M : Prompt → Prompt → Bool` and any `introspect`,
    there exists a prompt where `M p p ≠ introspect p` — i.e., the LLM's
    actual safety judgment on itself disagrees with its claimed
    self-judgment. -/
theorem LLM_safety_self_misclassification
    {Prompt : Type*}
    (M : LLM Prompt Bool)
    (introspect : Prompt → Bool)
    (hU : ICLUniversal M) :
    ∃ p, M p p ≠ introspect p := by
  by_contra h
  push_neg at h
  exact LLM_safety_corner_UC M introspect hU
    (fun p => bool_not_controller (introspect p)) h

/-! ## 7. Approximate version (for ε-ICL-universal systems) -/

/-- **ε-approximate ICL universality.** For every desired behavior `g`,
    some prompt makes the LLM approximate `g` to within `ε` on every query.
    This is the realistic version: real LLMs aren't perfectly surjective,
    but they ARE approximately surjective over short prompts. -/
def ApproxICLUniversal {Prompt Token : Type*} [PseudoMetricSpace Token]
    (M : LLM Prompt Token) (ε : ℝ) : Prop :=
  ∀ g : Prompt → Token, ∃ p, ∀ q, dist (M p q) (g q) ≤ ε

/-- **Approximate Lawvere for LLMs.** An ε-ICL-universal LLM has, for
    every output transformation, an ε-approximate fixed point reached
    through self-application. -/
theorem LLM_approx_fixed_point
    {Prompt : Type*} {Token : Type*} [PseudoMetricSpace Token]
    (M : LLM Prompt Token) {ε : ℝ}
    (hM : ApproxICLUniversal M ε)
    (t : Token → Token) :
    ∃ p, dist (M p p) (t (M p p)) ≤ ε := by
  obtain ⟨p, hp⟩ := hM (fun q => t (M q q))
  exact ⟨p, hp p⟩

/-- **Approximate CCH Trilemma for LLMs.**
    If an LLM is ε-ICL-universal, its self-introspection is δ-transparent,
    and the controller demands `t (introspect p)` differ from `introspect p`
    by more than `ε + δ`, then we have a contradiction.

    This is the *quantitative degradation* form: real LLMs sit inside this
    inequality region, with the achievable corners bounded by the
    universality–transparency–controllability tradeoff. -/
theorem LLM_approx_trilemma
    {Prompt : Type*} {Token : Type*} [PseudoMetricSpace Token]
    (M : LLM Prompt Token)
    (t : Token → Token)
    (introspect : Prompt → Token)
    {ε δ : ℝ}
    (hU : ApproxICLUniversal M ε)
    (hT : ∀ p, dist (M p p) (introspect p) ≤ δ)
    (hC : ∀ p, dist (t (introspect p)) (introspect p) > ε + 2 * δ)
    (htLip : ∀ x y, dist (t x) (t y) ≤ dist x y) : False := by
  obtain ⟨p, hp⟩ := LLM_approx_fixed_point M hU t
  -- hp : dist (M p p) (t (M p p)) ≤ ε
  -- hT p : dist (M p p) (introspect p) ≤ δ
  -- htLip applied: dist (t (M p p)) (t (introspect p)) ≤ dist (M p p) (introspect p) ≤ δ
  have h1 : dist (t (M p p)) (t (introspect p)) ≤ δ :=
    le_trans (htLip _ _) (hT p)
  -- Triangle: dist (introspect p) (t (introspect p))
  --   ≤ dist (introspect p) (M p p) + dist (M p p) (t (M p p))
  --     + dist (t (M p p)) (t (introspect p))
  --   ≤ δ + ε + δ = ε + 2δ
  have h2 : dist (introspect p) (t (introspect p)) ≤ ε + 2 * δ := by
    calc dist (introspect p) (t (introspect p))
        ≤ dist (introspect p) (M p p) + dist (M p p) (t (introspect p)) :=
          dist_triangle _ _ _
      _ ≤ dist (introspect p) (M p p) +
            (dist (M p p) (t (M p p)) + dist (t (M p p)) (t (introspect p))) := by
          gcongr
          exact dist_triangle _ _ _
      _ = dist (M p p) (introspect p) + dist (M p p) (t (M p p)) +
            dist (t (M p p)) (t (introspect p)) := by
          rw [dist_comm (introspect p) (M p p)]; ring
      _ ≤ δ + ε + δ :=
          add_le_add (add_le_add (hT p) hp) h1
      _ = ε + 2 * δ := by ring
  -- And hC gives the strict inequality
  have h3 : dist (introspect p) (t (introspect p)) > ε + 2 * δ := by
    rw [dist_comm]; exact hC p
  linarith

/-! ## 8. Summary

| # | Theorem | What it says |
|---|---------|--------------|
| 1 | `LLM_diagonal_fixed_point` | An ICL-universal LLM has a self-application fixed point for every output transformation. |
| 2 | `LLM_no_fixed_point_free` | No fixed-point-free `t` is consistent with full ICL universality. |
| 3 | `LLM_trilemma` | ICL-universal + Controlled + Transparent ⇒ ⊥. |
| 4 | `LLM_corner_UC/UT/CT` | The three pairwise corners of the trilemma. |
| 5 | `LLM_safety_self_misclassification` | A universal safety LLM disagrees with any self-introspection at some prompt. |
| 6 | `LLM_approx_fixed_point` | ε-ICL-universal LLM has ε-approximate self-fixed-points. |
| 7 | `LLM_approx_trilemma` | Quantitative trilemma: tradeoff among (ε, δ, controller margin). |

The bridge from abstract Lawvere to real LLMs is **one definition and one
line of proof**: an LLM is a function, ICL is the surjectivity hypothesis,
Lawvere's diagonal does the rest.
-/

end CCH
