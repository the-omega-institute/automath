import Omega.Zeta.XiRealInputCramerGermQuadraticFieldRigidity

namespace Omega.Zeta

/-- Paper label: `thm:xi-real-input40-local-rate-strict-downward-asymmetry`. -/
theorem paper_xi_real_input40_local_rate_strict_downward_asymmetry
    (D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) :
    D.cumulants_in_qsqrt5 ∧ D.legendre_local_expansion ∧
      D.right_tail_strictly_more_costly := by
  exact paper_xi_real_input_cramer_germ_quadratic_field_rigidity D

end Omega.Zeta
