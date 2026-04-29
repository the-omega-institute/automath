import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete normalization data for the double-Cayley source of the coefficient `4`. -/
structure xi_scan_coefficient_four_double_cayley_data where
  xi_scan_coefficient_four_double_cayley_seriesCoefficient : ℝ
  xi_scan_coefficient_four_double_cayley_endpointConformalFactor : ℝ
  xi_scan_coefficient_four_double_cayley_endpointDensityCoefficient : ℝ
  xi_scan_coefficient_four_double_cayley_dynamicalDegreeIncrement : Nat
  xi_scan_coefficient_four_double_cayley_seriesCoefficient_eq :
    xi_scan_coefficient_four_double_cayley_seriesCoefficient = 2
  xi_scan_coefficient_four_double_cayley_endpointConformalFactor_eq :
    xi_scan_coefficient_four_double_cayley_endpointConformalFactor = 2
  xi_scan_coefficient_four_double_cayley_endpointDensityCoefficient_eq :
    xi_scan_coefficient_four_double_cayley_endpointDensityCoefficient =
      xi_scan_coefficient_four_double_cayley_endpointConformalFactor ^ 2
  xi_scan_coefficient_four_double_cayley_no_new_dynamical_degree :
    xi_scan_coefficient_four_double_cayley_dynamicalDegreeIncrement = 0

/-- The paper-facing normalization claim: the Carathéodory coefficient is `2`, the endpoint
pullback coefficient is `4`, and no new dynamical degree is introduced. -/
def xi_scan_coefficient_four_double_cayley_claim
    (D : xi_scan_coefficient_four_double_cayley_data) : Prop :=
  D.xi_scan_coefficient_four_double_cayley_seriesCoefficient = 2 ∧
    D.xi_scan_coefficient_four_double_cayley_endpointDensityCoefficient = 4 ∧
      D.xi_scan_coefficient_four_double_cayley_dynamicalDegreeIncrement = 0

/-- Paper label: `prop:xi-scan-coefficient-four-double-cayley`. -/
theorem paper_xi_scan_coefficient_four_double_cayley
    (D : xi_scan_coefficient_four_double_cayley_data) :
    xi_scan_coefficient_four_double_cayley_claim D := by
  refine ⟨D.xi_scan_coefficient_four_double_cayley_seriesCoefficient_eq, ?_,
    D.xi_scan_coefficient_four_double_cayley_no_new_dynamical_degree⟩
  rw [D.xi_scan_coefficient_four_double_cayley_endpointDensityCoefficient_eq,
    D.xi_scan_coefficient_four_double_cayley_endpointConformalFactor_eq]
  norm_num

end Omega.Zeta
