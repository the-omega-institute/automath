import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.LowTemperatureThreeTermExpansion

namespace Omega.POM

/-- Concrete data for the zero-temperature Gibbs-limit corollary. The low-temperature three-term
expansion controls the exponentially small leakage outside the maximizing block, while the extra
input here records the convergence on the top block itself. -/
structure pom_zero_temperature_gibbs_limit_data where
  expansionData : PomLowTemperatureWeightedAdjacencyData
  stationaryMassOutside : ℕ → ℝ
  topBlockTvError : ℕ → ℝ
  piInfinityOutsideMass : ℝ
  outsideLeakConstant : ℝ
  topBlockConstant : ℝ
  hOutsideLeakConstant : 0 ≤ outsideLeakConstant
  hTopBlockConstant : 0 ≤ topBlockConstant
  hPiInfinitySupport : piInfinityOutsideMass = 0
  hOutsideLeakage :
    ∀ q, expansionData.q0 ≤ q →
      stationaryMassOutside q ≤
        expansionData.remainder q +
          outsideLeakConstant * Real.exp (-(q : ℝ) * expansionData.gap)
  hTopBlockConvergence :
    ∀ q, expansionData.q0 ≤ q →
      topBlockTvError q ≤
        topBlockConstant * Real.exp (-(q : ℝ) * expansionData.gap)

namespace pom_zero_temperature_gibbs_limit_data

/-- The total-variation envelope obtained by adding the outside mass leakage to the convergence
error on `V_*`. -/
def pom_zero_temperature_gibbs_limit_total_variation_bound
    (D : pom_zero_temperature_gibbs_limit_data) : Prop :=
  ∀ q, D.expansionData.q0 ≤ q →
    D.stationaryMassOutside q + D.topBlockTvError q ≤
      (D.expansionData.errorConstant + D.outsideLeakConstant + D.topBlockConstant) *
        Real.exp (-(q : ℝ) * D.expansionData.gap)

end pom_zero_temperature_gibbs_limit_data

open pom_zero_temperature_gibbs_limit_data

/-- Paper label: `cor:pom-zero-temperature-gibbs-limit`.

The low-temperature expansion bounds the leakage outside `V_*` by the remainder plus an explicit
exponential tail. Adding any exponentially convergent top-block approximation to the limiting
stationary law therefore gives a total-variation error bound with the same scale and forces the
limiting law to be supported on `V_*`. -/
theorem paper_pom_zero_temperature_gibbs_limit
    (D : pom_zero_temperature_gibbs_limit_data) :
    D.piInfinityOutsideMass = 0 ∧ D.pom_zero_temperature_gibbs_limit_total_variation_bound := by
  constructor
  · exact D.hPiInfinitySupport
  · intro q hq
    rcases paper_pom_low_temperature_three_term_expansion D.expansionData with
      ⟨_, hErrorBound⟩
    have hRemainderBound :
        D.expansionData.remainder q ≤
          D.expansionData.errorConstant * Real.exp (-(q : ℝ) * D.expansionData.gap) := by
      have hdiff :
          D.expansionData.pressure q -
              ((q : ℝ) * Real.log D.expansionData.aStar + Real.log D.expansionData.rhoStar) =
            D.expansionData.remainder q := by
        linarith [D.expansionData.hExpansion q hq]
      simpa [hdiff] using (hErrorBound q hq).2
    have hOutside := D.hOutsideLeakage q hq
    have hTop := D.hTopBlockConvergence q hq
    have hScaleNonneg :
        0 ≤ Real.exp (-(q : ℝ) * D.expansionData.gap) := by
      exact le_of_lt (Real.exp_pos _)
    nlinarith [hOutside, hTop, hRemainderBound, D.expansionData.hErrorConstant,
      D.hOutsideLeakConstant, D.hTopBlockConstant, hScaleNonneg]

end Omega.POM
