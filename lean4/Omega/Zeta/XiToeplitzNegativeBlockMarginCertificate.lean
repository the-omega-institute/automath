import Omega.Zeta.XiToeplitzNegativeMarginVandermonde4Lowerbound

namespace Omega.Zeta

open XiToeplitzNegativeMarginData

/-- Paper label: `cor:xi-toeplitz-negative-block-margin-certificate`. -/
theorem paper_xi_toeplitz_negative_block_margin_certificate (D : XiToeplitzNegativeMarginData) :
    D.sigmaMin ^ 2 / D.opNormR ^ 2 ≤ D.delta := by
  exact (paper_xi_toeplitz_negative_margin_vandermonde4_lowerbound D).1

end Omega.Zeta
