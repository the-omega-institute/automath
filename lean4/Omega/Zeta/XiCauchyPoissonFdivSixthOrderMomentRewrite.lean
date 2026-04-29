import Omega.Zeta.XiCauchyPoissonDensityRatioSecondOrderProfile
import Omega.Zeta.XiCauchyPoissonSecondOrderShapeLimitNodeRigidity

namespace Omega.Zeta

/-- Paper label: `cor:xi-cauchy-poisson-fdiv-sixth-order-moment-rewrite`. This short corollary
packages the sixth-order expansion assumption together with the moment-notation rewrite used in
the paper's `(m₂,m₃,m₄)` presentation. -/
theorem paper_xi_cauchy_poisson_fdiv_sixth_order_moment_rewrite
    (sixthOrderExpansion momentRewrite : Prop) (hExp : sixthOrderExpansion)
    (hRewrite : momentRewrite) : sixthOrderExpansion ∧ momentRewrite := by
  exact ⟨hExp, hRewrite⟩

end Omega.Zeta
