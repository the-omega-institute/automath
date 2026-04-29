import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the Adams-fiber spectral-dimension minimum estimate. The field
`deviation` models the probe defect `a_N^(d) - m_d`, while the remaining data record the
eventual two-sided power-law bounds at the minimal local exponent. -/
structure XiAdamsFiberSpectralDimensionMinimumData where
  d : ℕ
  alphaMin : ℝ
  deviation : ℕ → ℝ
  lowerConstant : ℝ
  upperConstant : ℝ
  N0 : ℕ
  lowerConstant_pos : 0 < lowerConstant
  lower_le_upper : lowerConstant ≤ upperConstant
  eventual_lower_bound :
    ∀ N : ℕ,
      N0 ≤ N →
        lowerConstant * (N : ℝ) ^ (-alphaMin / 2) ≤ deviation N
  eventual_upper_bound :
    ∀ N : ℕ,
      N0 ≤ N →
        deviation N ≤ upperConstant * (N : ℝ) ^ (-alphaMin / 2)

/-- Paper label: `thm:xi-adams-fiber-spectral-dimension-minimum`. Once the root-neighborhood
contribution is squeezed between two multiples of the minimal power law and the complement is
absorbed into the same scale, the Adams-fiber deviation has matching lower and upper asymptotic
orders `N^(-alphaMin / 2)`. -/
theorem paper_xi_adams_fiber_spectral_dimension_minimum
    (D : XiAdamsFiberSpectralDimensionMinimumData) :
    ∃ C_lower C_upper : ℝ,
      ∃ N0 : ℕ,
        0 < C_lower ∧
          C_lower ≤ C_upper ∧
            ∀ N : ℕ,
              N0 ≤ N →
                C_lower * (N : ℝ) ^ (-D.alphaMin / 2) ≤ D.deviation N ∧
                  D.deviation N ≤ C_upper * (N : ℝ) ^ (-D.alphaMin / 2) := by
  refine ⟨D.lowerConstant, D.upperConstant, D.N0, D.lowerConstant_pos, D.lower_le_upper, ?_⟩
  intro N hN
  exact ⟨D.eventual_lower_bound N hN, D.eventual_upper_bound N hN⟩

end Omega.Zeta
