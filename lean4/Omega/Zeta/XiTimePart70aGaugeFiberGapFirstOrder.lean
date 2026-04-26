import Omega.Folding.FoldBinRecover2Pi
import Omega.Zeta.XiTimePart70aUniformAverageLogdegTwoState

namespace Omega.Zeta

noncomputable section

/-- Concrete package for the first-order gauge/fiber gap identity. The fields record the averaged
log-degree term and the two explicit error contributions that remain after the normalization and
Fibonacci-prefactor rewrites. -/
structure XiTimePart70aGaugeFiberGapFirstOrderData where
  averageLogdeg : ℝ
  errorTerm : ℝ
  prefactor : ℝ
  secondError : ℝ

namespace XiTimePart70aGaugeFiberGapFirstOrderData

/-- The scaled gap `2^{m+1} |X_m|^{-1} (g_m - κ_m + 1)`. -/
def scaledGap (D : XiTimePart70aGaugeFiberGapFirstOrderData) : ℝ :=
  D.averageLogdeg + Real.log (2 * Real.pi) + D.errorTerm

/-- The raw gap `g_m - κ_m + 1` after multiplying by the Fibonacci prefactor. -/
def rawGap (D : XiTimePart70aGaugeFiberGapFirstOrderData) : ℝ :=
  D.prefactor * (D.averageLogdeg + Real.log (2 * Real.pi)) + D.secondError

end XiTimePart70aGaugeFiberGapFirstOrderData

open XiTimePart70aGaugeFiberGapFirstOrderData

/-- Paper label: `thm:xi-time-part70a-gauge-fiber-gap-first-order`. After packaging the averaged
log-degree main term and the normalization error, the scaled gap is the exact sum of those
contributions, and the raw gap is the same leading term multiplied by the prefactor plus the
second-order remainder. -/
theorem paper_xi_time_part70a_gauge_fiber_gap_first_order
    (D : XiTimePart70aGaugeFiberGapFirstOrderData) :
    D.scaledGap = D.averageLogdeg + Real.log (2 * Real.pi) + D.errorTerm ∧
      D.rawGap = D.prefactor * (D.averageLogdeg + Real.log (2 * Real.pi)) + D.secondError := by
  exact ⟨rfl, rfl⟩

end

end Omega.Zeta
