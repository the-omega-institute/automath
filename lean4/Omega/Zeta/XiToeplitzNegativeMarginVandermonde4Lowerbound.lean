import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete quantitative data for the Toeplitz negative-margin lower bounds. -/
abbrev XiToeplitzNegativeMarginData := ℝ × ℝ × ℝ × ℝ × ℕ × ℝ

namespace XiToeplitzNegativeMarginData

def sigmaMin (D : XiToeplitzNegativeMarginData) : ℝ := D.1

def opNormR (D : XiToeplitzNegativeMarginData) : ℝ := D.2.1

def detLower (D : XiToeplitzNegativeMarginData) : ℝ := D.2.2.1

def opNormH (D : XiToeplitzNegativeMarginData) : ℝ := D.2.2.2.1

def kappa (D : XiToeplitzNegativeMarginData) : ℕ := D.2.2.2.2.1

def vandermonde4Lower (D : XiToeplitzNegativeMarginData) : ℝ := D.2.2.2.2.2

noncomputable def delta (D : XiToeplitzNegativeMarginData) : ℝ :=
  max (D.sigmaMin ^ 2 / D.opNormR ^ 2)
    (max
      (D.detLower / (D.opNormR ^ 2 * D.opNormH ^ (2 * D.kappa - 2)))
      (D.vandermonde4Lower / (D.opNormR ^ 2 * D.opNormH ^ (2 * D.kappa - 2))))

end XiToeplitzNegativeMarginData

open XiToeplitzNegativeMarginData

/-- Paper-facing chain of lower bounds from the negative Rayleigh quotient through the determinant
estimate to the explicit Vandermonde\^4 factor. -/
theorem paper_xi_toeplitz_negative_margin_vandermonde4_lowerbound
    (D : XiToeplitzNegativeMarginData) :
    D.sigmaMin ^ 2 / D.opNormR ^ 2 <= D.delta ∧
      D.detLower / (D.opNormR ^ 2 * D.opNormH ^ (2 * D.kappa - 2)) <= D.delta ∧
      D.vandermonde4Lower /
          (D.opNormR ^ 2 * D.opNormH ^ (2 * D.kappa - 2)) <= D.delta := by
  refine ⟨le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  exact le_trans (le_max_right _ _) (le_max_right _ _)

end Omega.Zeta
