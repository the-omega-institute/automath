import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

noncomputable section

/-- The Jones projection sandwiches collapse to the same scalar `lam`. -/
def jonesSandwichScalar (e₁ e₂ lam : ℝ) : Prop :=
  e₁ * e₂ * e₁ = lam * e₁ ∧ e₂ * e₁ * e₂ = lam * e₂

/-- The scalar extracted from the Jones trace/index relation. -/
def scalarEqualsIndexRatio (lam ind₁ ind₂ ind₁₂ : ℝ) : Prop :=
  lam = ind₁₂ / (ind₁ * ind₂)

/-- The index gap `Γ = log ((Ind E₁ * Ind E₂) / Ind E₁₂)`. -/
def indexGap (ind₁ ind₂ ind₁₂ : ℝ) : ℝ :=
  Real.log ((ind₁ * ind₂) / ind₁₂)

/-- The Jones scalar is `exp (-Γ)`. -/
def scalarEqualsExpNegGap (lam ind₁ ind₂ ind₁₂ : ℝ) : Prop :=
  lam = Real.exp (-indexGap ind₁ ind₂ ind₁₂)

theorem paper_op_algebra_jones_scalar_equals_exp_minus_gap
    {e₁ e₂ lam ind₁ ind₂ ind₁₂ : ℝ}
    (hSandwich : jonesSandwichScalar e₁ e₂ lam)
    (hTrace : ind₁ * ind₂ * lam = ind₁₂)
    (h₁ : 0 < ind₁) (h₂ : 0 < ind₂) (h₁₂ : 0 < ind₁₂) :
    jonesSandwichScalar e₁ e₂ lam ∧
      scalarEqualsIndexRatio lam ind₁ ind₂ ind₁₂ ∧
      scalarEqualsExpNegGap lam ind₁ ind₂ ind₁₂ := by
  have hMulNe : ind₁ * ind₂ ≠ 0 := mul_ne_zero h₁.ne' h₂.ne'
  have hRatio : scalarEqualsIndexRatio lam ind₁ ind₂ ind₁₂ := by
    unfold scalarEqualsIndexRatio
    apply (eq_div_iff hMulNe).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hTrace
  have hExp : scalarEqualsExpNegGap lam ind₁ ind₂ ind₁₂ := by
    unfold scalarEqualsExpNegGap
    calc
      lam = ind₁₂ / (ind₁ * ind₂) := hRatio
      _ = ((ind₁ * ind₂) / ind₁₂)⁻¹ := by
            field_simp [h₁.ne', h₂.ne', h₁₂.ne']
      _ = Real.exp (-indexGap ind₁ ind₂ ind₁₂) := by
            unfold indexGap
            rw [Real.exp_neg, Real.exp_log (div_pos (mul_pos h₁ h₂) h₁₂)]
  exact ⟨hSandwich, hRatio, hExp⟩

end

end Omega.OperatorAlgebra
