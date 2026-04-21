import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateFdivFourthOrderConstant

namespace Omega.CircleDimension

/-- The fourth-order bivariate `f`-divergence invariant can be rewritten as `|m₂|² / 8`, with
`m₂` encoded by its real and imaginary parts. This is the paper-facing `|m₂|²` formulation of the
constant.
    cor:cdim-poisson-bivariate-fdiv-fourth-order-complex-m2 -/
theorem paper_cdim_poisson_bivariate_fdiv_fourth_order_complex_m2
    (fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) :
    let m2Re := sigmaGamma2 - sigmaDelta2
    let m2Im := 2 * sigmaGammaDelta
    fpp1 * poissonBivariateFourthOrderQuadraticInvariant
        sigmaGamma2 sigmaDelta2 sigmaGammaDelta =
      (fpp1 / 8) * (m2Re ^ 2 + m2Im ^ 2) := by
  dsimp [poissonBivariateFourthOrderQuadraticInvariant]
  ring

end Omega.CircleDimension
