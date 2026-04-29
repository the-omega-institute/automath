import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateFdivSixthOrderConstant

namespace Omega.CircleDimension

/-- The sixth-order bivariate `f`-divergence invariant can be rewritten as `(3 / 32) |m₃|²`, with
`m₃` encoded by its real and imaginary parts.  This is the paper-facing `|m₃|²` formulation of
the constant.
    cor:cdim-poisson-bivariate-fdiv-sixth-order-complex-m3 -/
theorem paper_cdim_poisson_bivariate_fdiv_sixth_order_complex_m3
    (fpp1 k300 k210 k120 k030 : ℝ) :
    let m3Re := k300 - 3 * k120
    let m3Im := 3 * k210 - k030
    fpp1 * ((3 / 32 : ℝ) * (((3 * k120 - k300) ^ 2) + ((3 * k210 - k030) ^ 2))) =
      ((3 * fpp1) / 32 : ℝ) * (m3Re ^ 2 + m3Im ^ 2) := by
  dsimp
  ring

end Omega.CircleDimension
