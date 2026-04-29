import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational

namespace Omega.Zeta

/-- Irrational log-ratio hypothesis, retaining the nonzero first logarithm needed below. -/
def xi_dual_base_dealiasing_injective_encoding_log_ratio_irrational
    (lambda₁ lambda₂ : ℝ) : Prop :=
  Real.log lambda₁ ≠ 0 ∧ Irrational (Real.log lambda₁ / Real.log lambda₂)

/-- Equality of the two phase coordinates, recorded as vanishing logarithmic phase defects. -/
def xi_dual_base_dealiasing_injective_encoding_same_phase_pair
    (γ γ' lambda₁ lambda₂ : ℝ) : Prop :=
  (γ - γ') * Real.log lambda₁ = 0 ∧ (γ - γ') * Real.log lambda₂ = 0

/-- Paper label: `thm:xi-dual-base-dealiasing-injective-encoding`.
If the two logarithmic phase defects vanish under an irrational log-ratio hypothesis, then
the encoded phase coordinate is injective. -/
theorem paper_xi_dual_base_dealiasing_injective_encoding
    {γ γ' lambda₁ lambda₂ : ℝ}
    (hIrr : xi_dual_base_dealiasing_injective_encoding_log_ratio_irrational lambda₁ lambda₂)
    (hPhase :
      xi_dual_base_dealiasing_injective_encoding_same_phase_pair γ γ' lambda₁ lambda₂) :
    γ = γ' := by
  have hdiff : γ - γ' = 0 := by
    exact (mul_eq_zero.mp hPhase.1).resolve_right hIrr.1
  exact sub_eq_zero.mp hdiff

end Omega.Zeta
