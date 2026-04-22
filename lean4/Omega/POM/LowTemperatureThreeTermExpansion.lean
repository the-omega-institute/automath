import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

structure PomLowTemperatureWeightedAdjacencyData where
  aStar : ℝ
  rhoStar : ℝ
  gap : ℝ
  errorConstant : ℝ
  q0 : ℕ
  pressure : ℕ → ℝ
  remainder : ℕ → ℝ
  hAStar : 0 < aStar
  hRhoStar : 0 < rhoStar
  hGap : 0 ≤ gap
  hErrorConstant : 0 ≤ errorConstant
  hExpansion :
    ∀ q, q0 ≤ q →
      pressure q = (q : ℝ) * Real.log aStar + Real.log rhoStar + remainder q
  hRemainderNonneg : ∀ q, q0 ≤ q → 0 ≤ remainder q
  hRemainderBound :
    ∀ q, q0 ≤ q → remainder q ≤ errorConstant * Real.exp (-(q : ℝ) * gap)

def PomLowTemperatureWeightedAdjacencyData.leadingPressureExpansion
    (D : PomLowTemperatureWeightedAdjacencyData) : Prop :=
  ∀ q, D.q0 ≤ q →
    D.pressure q = (q : ℝ) * Real.log D.aStar + Real.log D.rhoStar + D.remainder q

def PomLowTemperatureWeightedAdjacencyData.exponentialErrorBound
    (D : PomLowTemperatureWeightedAdjacencyData) : Prop :=
  ∀ q, D.q0 ≤ q →
    0 ≤
        D.pressure q - ((q : ℝ) * Real.log D.aStar + Real.log D.rhoStar) ∧
      D.pressure q - ((q : ℝ) * Real.log D.aStar + Real.log D.rhoStar) ≤
        D.errorConstant * Real.exp (-(q : ℝ) * D.gap)

/-- `thm:pom-low-temperature-three-term-expansion` -/
theorem paper_pom_low_temperature_three_term_expansion
    (D : PomLowTemperatureWeightedAdjacencyData) :
    D.leadingPressureExpansion ∧ D.exponentialErrorBound := by
  refine ⟨D.hExpansion, ?_⟩
  intro q hq
  have hExpansion := D.hExpansion q hq
  have hNonneg := D.hRemainderNonneg q hq
  have hBound := D.hRemainderBound q hq
  have hDiff :
      D.pressure q - ((q : ℝ) * Real.log D.aStar + Real.log D.rhoStar) = D.remainder q := by
    linarith
  constructor
  · simpa [hDiff] using hNonneg
  · simpa [hDiff] using hBound

end Omega.POM
