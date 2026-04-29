import Omega.Zeta.XiTimePart62dgcZGMatrixEulerNoScalarProduct

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zp-zg-prime-grammar-matrixization`. -/
theorem paper_xi_time_part9zp_zg_prime_grammar_matrixization
    (W : Omega.Zeta.XiZGAbelResidueLogDensityWitness) :
    Omega.Zeta.derivedZGNoScalarEulerProduct := by
  exact (paper_xi_time_part62dgc_zg_matrix_euler_no_scalar_product W).2.2.2

end Omega.Zeta
