import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete package of the analytic inputs for the Zeckendorf--Godel counting estimate. The
fields record the counting function, the main-density residue, the contour-shift error term, and
the quantitative bound for the shifted Perron integral on the line `Re(s) = 1 / 2 + ε`. -/
structure XiZGCountingData where
  count : ℝ → ℝ
  deltaZG : ℝ
  dirichletSeries : ℂ → ℂ
  residueAtOne : ℝ
  contourError : ℝ → ℝ → ℝ
  contourConstant : ℝ → ℝ
  residue_eq_delta : residueAtOne = deltaZG
  contourConstant_pos : ∀ ε > 0, 0 < contourConstant ε
  perronShift :
    ∀ ε > 0, ∀ x ≥ 1, count x - deltaZG * x = contourError ε x
  contourShiftBound :
    ∀ ε > 0, ∀ x ≥ 1,
      |contourError ε x| ≤ contourConstant ε * Real.rpow x (1 / 2 + ε)

/-- The contour move and the vertical-line estimate combine into the standard
`x^(1 / 2 + ε)` counting error. -/
theorem paper_xi_zg_counting_power_saving_error (d : XiZGCountingData) :
    ∀ ε > 0, ∃ C > 0, ∀ x ≥ 1,
      |d.count x - d.deltaZG * x| ≤ C * Real.rpow x (1 / 2 + ε) := by
  intro ε hε
  refine ⟨d.contourConstant ε, d.contourConstant_pos ε hε, ?_⟩
  intro x hx
  calc
    |d.count x - d.deltaZG * x| = |d.contourError ε x| := by
      rw [d.perronShift ε hε x hx]
    _ ≤ d.contourConstant ε * Real.rpow x (1 / 2 + ε) := d.contourShiftBound ε hε x hx

end Omega.Zeta
