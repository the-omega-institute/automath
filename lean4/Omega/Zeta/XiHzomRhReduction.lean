import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete zero-set package for the HZOM reduction to the critical line. -/
structure xi_hzom_rh_reduction_data where
  xi_hzom_rh_reduction_protocolZeros : Set ℂ
  xi_hzom_rh_reduction_arithmeticZeros : Set ℂ
  xi_hzom_rh_reduction_spectral_contraction_right :
    ∀ s, s ∈ xi_hzom_rh_reduction_protocolZeros → s.re ≤ (1 / 2 : ℝ)
  xi_hzom_rh_reduction_functional_equation_reflection :
    ∀ s, s ∈ xi_hzom_rh_reduction_protocolZeros → (1 / 2 : ℝ) ≤ s.re
  xi_hzom_rh_reduction_arithmetic_zero_set_equivalence :
    xi_hzom_rh_reduction_arithmeticZeros = xi_hzom_rh_reduction_protocolZeros

namespace xi_hzom_rh_reduction_data

/-- All arithmetic zeros lie on the critical line. -/
def xi_hzom_rh_reduction_zeros_on_critical_line
    (D : xi_hzom_rh_reduction_data) : Prop :=
  ∀ s, s ∈ D.xi_hzom_rh_reduction_arithmeticZeros → s.re = (1 / 2 : ℝ)

end xi_hzom_rh_reduction_data

/-- Paper label: `thm:xi-hzom-rh-reduction`. -/
theorem paper_xi_hzom_rh_reduction (D : xi_hzom_rh_reduction_data) :
    D.xi_hzom_rh_reduction_zeros_on_critical_line := by
  intro s hs
  have hprotocol : s ∈ D.xi_hzom_rh_reduction_protocolZeros := by
    simpa [D.xi_hzom_rh_reduction_arithmetic_zero_set_equivalence] using hs
  exact le_antisymm
    (D.xi_hzom_rh_reduction_spectral_contraction_right s hprotocol)
    (D.xi_hzom_rh_reduction_functional_equation_reflection s hprotocol)

end Omega.Zeta
