import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete asymptotic constants for the Cauchy--Poisson Pinsker ratio package. -/
structure xi_cauchy_poisson_pinsker_sharp_ratio_data where
  sigmaSq : ℝ
  l1LeadingConstant : ℝ
  tvLeadingConstant : ℝ
  klLeadingConstant : ℝ
  sigmaSq_pos : 0 < sigmaSq
  l1LeadingConstant_eq :
    l1LeadingConstant = (3 * Real.sqrt 3 / (4 * Real.pi)) * sigmaSq
  tvLeadingConstant_eq : tvLeadingConstant = (1 / 2) * l1LeadingConstant
  klLeadingConstant_eq : klLeadingConstant = sigmaSq ^ 2 / 8

/-- Paper-facing algebraic statement for the sharp Pinsker ratio constants. -/
def xi_cauchy_poisson_pinsker_sharp_ratio_statement
    (D : xi_cauchy_poisson_pinsker_sharp_ratio_data) : Prop :=
  D.tvLeadingConstant ≠ 0 ∧
    D.klLeadingConstant / D.tvLeadingConstant ^ 2 = 8 * Real.pi ^ 2 / 27 ∧
    D.l1LeadingConstant ≠ 0 ∧
      D.klLeadingConstant / D.l1LeadingConstant ^ 2 = 2 * Real.pi ^ 2 / 27

/-- Paper label: `cor:xi-cauchy-poisson-pinsker-sharp-ratio`. -/
theorem paper_xi_cauchy_poisson_pinsker_sharp_ratio
    (D : xi_cauchy_poisson_pinsker_sharp_ratio_data) :
    xi_cauchy_poisson_pinsker_sharp_ratio_statement D := by
  have hsigma_ne : D.sigmaSq ≠ 0 := D.sigmaSq_pos.ne'
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := hpi_pos.ne'
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt_ne : Real.sqrt 3 ≠ 0 := hsqrt_pos.ne'
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hl1_ne : D.l1LeadingConstant ≠ 0 := by
    rw [D.l1LeadingConstant_eq]
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero (by norm_num) hsqrt_ne) (mul_ne_zero (by norm_num) hpi_ne))
      hsigma_ne
  have htv_ne : D.tvLeadingConstant ≠ 0 := by
    rw [D.tvLeadingConstant_eq]
    exact mul_ne_zero (by norm_num) hl1_ne
  refine ⟨htv_ne, ?_, hl1_ne, ?_⟩
  · rw [D.klLeadingConstant_eq, D.tvLeadingConstant_eq, D.l1LeadingConstant_eq]
    field_simp [hsigma_ne, hsqrt_ne, hpi_ne]
    rw [hsqrt_sq]
    ring
  · rw [D.klLeadingConstant_eq, D.l1LeadingConstant_eq]
    field_simp [hsigma_ne, hsqrt_ne, hpi_ne]
    rw [hsqrt_sq]
    ring

end

end Omega.Zeta
