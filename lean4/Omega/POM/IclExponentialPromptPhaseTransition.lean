import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete exponential-prompt package for the ICL unseen-mass exponent.  The LDP input has
already been compressed to the threshold-side infimum `ldpInfimum`; the theorem below records the
resulting two-regime exponent as an exact exponential model. -/
structure pom_icl_exponential_prompt_phase_transition_data where
  pom_icl_exponential_prompt_phase_transition_kappa : ℝ
  pom_icl_exponential_prompt_phase_transition_alphaStar : ℝ
  pom_icl_exponential_prompt_phase_transition_ldpInfimum : ℝ

namespace pom_icl_exponential_prompt_phase_transition_data

/-- The critical prompt threshold `log 2 - alphaStar`. -/
def pom_icl_exponential_prompt_phase_transition_threshold
    (D : pom_icl_exponential_prompt_phase_transition_data) : ℝ :=
  Real.log 2 - D.pom_icl_exponential_prompt_phase_transition_alphaStar

/-- The phase-transition exponent selected by the LDP threshold. -/
def pom_icl_exponential_prompt_phase_transition_rate
    (D : pom_icl_exponential_prompt_phase_transition_data) : ℝ :=
  if D.pom_icl_exponential_prompt_phase_transition_kappa ≤
      D.pom_icl_exponential_prompt_phase_transition_threshold then
    0
  else
    D.pom_icl_exponential_prompt_phase_transition_ldpInfimum

/-- Exact exponential surrogate for the unseen prompt mass at level `m`. -/
def pom_icl_exponential_prompt_phase_transition_unseenMass
    (D : pom_icl_exponential_prompt_phase_transition_data) (m : ℕ) : ℝ :=
  Real.exp
    (-(((m : ℝ) + 1) * D.pom_icl_exponential_prompt_phase_transition_rate))

/-- Finite-level normalized exponent of the exact exponential surrogate. -/
def pom_icl_exponential_prompt_phase_transition_normalizedExponent
    (D : pom_icl_exponential_prompt_phase_transition_data) (m : ℕ) : ℝ :=
  -Real.log (D.pom_icl_exponential_prompt_phase_transition_unseenMass m) / ((m : ℝ) + 1)

/-- Paper-facing two-regime law for the exponential-prompt ICL transition. -/
def pom_icl_exponential_prompt_phase_transition_law
    (D : pom_icl_exponential_prompt_phase_transition_data) : Prop :=
  (∀ m : ℕ,
      D.pom_icl_exponential_prompt_phase_transition_normalizedExponent m =
        D.pom_icl_exponential_prompt_phase_transition_rate) ∧
    (D.pom_icl_exponential_prompt_phase_transition_kappa ≤
        D.pom_icl_exponential_prompt_phase_transition_threshold →
      D.pom_icl_exponential_prompt_phase_transition_rate = 0) ∧
    (¬ D.pom_icl_exponential_prompt_phase_transition_kappa ≤
        D.pom_icl_exponential_prompt_phase_transition_threshold →
      D.pom_icl_exponential_prompt_phase_transition_rate =
        D.pom_icl_exponential_prompt_phase_transition_ldpInfimum)

end pom_icl_exponential_prompt_phase_transition_data

open pom_icl_exponential_prompt_phase_transition_data

/-- Paper label: `thm:pom-icl-exponential-prompt-phase-transition`. -/
theorem paper_pom_icl_exponential_prompt_phase_transition
    (D : pom_icl_exponential_prompt_phase_transition_data) :
    D.pom_icl_exponential_prompt_phase_transition_law := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    unfold pom_icl_exponential_prompt_phase_transition_normalizedExponent
      pom_icl_exponential_prompt_phase_transition_unseenMass
    rw [Real.log_exp]
    have hden : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
  · intro hThreshold
    simp [pom_icl_exponential_prompt_phase_transition_rate, hThreshold]
  · intro hThreshold
    simp [pom_icl_exponential_prompt_phase_transition_rate, hThreshold]

end

end Omega.POM
