import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Omega.SyncKernelRealInput.MobiusCollapse
import Omega.SyncKernelRealInput.RealInput40MertensConstant
import Omega.SyncKernelRealInput.RealInput40MertensTwoSeriesTail

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The residual quadratic contribution left after collapsing the `(1 - z)` and `(1 + z)` branches
of the determinant factorization. -/
def real_input_40_mertens_two_series_residual (z : ℂ) : ℂ :=
  Complex.log (1 - 3 * z + z ^ 2) + Complex.log (1 + z - z ^ 2)

/-- Paper label: `prop:real-input-40-mertens-two-series`. In the concrete real-input-40 wrapper,
the Möbius-log contributions of the `(1-z)` and `(1+z)` branches collapse to the explicit
logarithms from `paper_mobius_collapse`, the remaining quadratic factors are recorded by the
residual series, the truncation tail is controlled by the existing geometric majorant, and the
constant term is the already formalized real-input-40 Mertens constant. -/
theorem paper_real_input_40_mertens_two_series (z : ℂ) (hz : ‖z‖ < 1) (N : ℕ) :
    mobius_collapse_one_minus z = -Complex.log (1 - z) ∧
      mobius_collapse_one_plus z = Complex.log (1 - z ^ 2) - Complex.log (1 - z) ∧
      real_input_40_mertens_two_series_residual z =
        Complex.log (1 - 3 * z + z ^ 2) + Complex.log (1 + z - z ^ 2) ∧
      real_input_40_mertens_two_series_tail_statement N ∧
      real_input_40_mertens_constant_value = 0 := by
  rcases paper_mobius_collapse z hz with ⟨hminus, hplus⟩
  have htail := real_input_40_mertens_two_series_tail_true N
  have hconst := paper_real_input_40_mertens_constant
  exact ⟨hminus, hplus, rfl, htail, hconst.2.1⟩

end

end Omega.SyncKernelRealInput
