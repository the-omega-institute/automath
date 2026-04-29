import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Zeta.XiDualBaseDealiasingInjectiveEncoding

namespace Omega.Zeta

/-- Concrete two-base phase package for the bases `2` and the golden ratio. -/
structure xi_dual_base_dealiasing_2_phi_data where
  xi_dual_base_dealiasing_2_phi_gamma : ℝ
  xi_dual_base_dealiasing_2_phi_gamma' : ℝ
  xi_dual_base_dealiasing_2_phi_log_ratio_irrational :
    xi_dual_base_dealiasing_injective_encoding_log_ratio_irrational 2 Real.goldenRatio
  xi_dual_base_dealiasing_2_phi_same_phase_pair :
    xi_dual_base_dealiasing_injective_encoding_same_phase_pair
      xi_dual_base_dealiasing_2_phi_gamma
      xi_dual_base_dealiasing_2_phi_gamma' 2 Real.goldenRatio

namespace xi_dual_base_dealiasing_2_phi_data

/-- The two phase coordinates at bases `2` and `phi` encode the ordinate injectively. -/
def injective_encoding_for_two_phi (D : xi_dual_base_dealiasing_2_phi_data) : Prop :=
  D.xi_dual_base_dealiasing_2_phi_gamma = D.xi_dual_base_dealiasing_2_phi_gamma'

end xi_dual_base_dealiasing_2_phi_data

/-- Paper label: `cor:xi-dual-base-dealiasing-2-phi`. The existing dual-base injectivity criterion
applies to the concrete bases `2` and `Real.goldenRatio` once their irrational log-ratio certificate
and the equal phase-pair certificate are supplied. -/
theorem paper_xi_dual_base_dealiasing_2_phi (D : xi_dual_base_dealiasing_2_phi_data) :
    D.injective_encoding_for_two_phi := by
  exact
    paper_xi_dual_base_dealiasing_injective_encoding
      D.xi_dual_base_dealiasing_2_phi_log_ratio_irrational
      D.xi_dual_base_dealiasing_2_phi_same_phase_pair

end Omega.Zeta
