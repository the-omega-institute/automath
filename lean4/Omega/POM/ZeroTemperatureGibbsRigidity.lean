import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.LowTemperatureThreeTermExpansion

namespace Omega.POM

/-- Concrete data for the zero-temperature Gibbs rigidity package. The low-temperature three-term
expansion provides the exponentially small remainder, and the transfer estimates turn that
remainder into leakage bounds for the stationary mass and the left/right Perron vectors. -/
structure pom_zero_temperature_gibbs_rigidity_data where
  expansionData : PomLowTemperatureWeightedAdjacencyData
  stationaryMassOutside : ℕ → ℝ
  rightLeakRatio : ℕ → ℝ
  leftLeakRatio : ℕ → ℝ
  perronLeakConstant : ℝ
  hPerronLeakConstant : 0 ≤ perronLeakConstant
  hStationaryMassTransfer :
    ∀ q, expansionData.q0 ≤ q →
      stationaryMassOutside q ≤
        expansionData.remainder q +
          perronLeakConstant * Real.exp (-(q : ℝ) * expansionData.gap)
  hRightLeakTransfer :
    ∀ q, expansionData.q0 ≤ q →
      rightLeakRatio q ≤
        expansionData.remainder q +
          perronLeakConstant * Real.exp (-(q : ℝ) * expansionData.gap)
  hLeftLeakTransfer :
    ∀ q, expansionData.q0 ≤ q →
      leftLeakRatio q ≤
        expansionData.remainder q +
          perronLeakConstant * Real.exp (-(q : ℝ) * expansionData.gap)

namespace pom_zero_temperature_gibbs_rigidity_data

/-- Common exponential envelope constant obtained by combining the three-term remainder bound with
the Perron leakage estimate on the primitive top block. -/
def pom_zero_temperature_gibbs_rigidity_exponential_constant
    (D : pom_zero_temperature_gibbs_rigidity_data) : ℝ :=
  D.expansionData.errorConstant + D.perronLeakConstant

/-- Exponential concentration of the zero-temperature Gibbs state on the maximal-weight kernel:
the stationary mass outside the top block and the leakage of both Perron eigenvectors are all
controlled by the same `e^{-q Δ}` envelope. -/
def exponential_concentration (D : pom_zero_temperature_gibbs_rigidity_data) : Prop :=
  ∀ q, D.expansionData.q0 ≤ q →
    D.stationaryMassOutside q ≤
        D.pom_zero_temperature_gibbs_rigidity_exponential_constant *
          Real.exp (-(q : ℝ) * D.expansionData.gap) ∧
      D.rightLeakRatio q ≤
        D.pom_zero_temperature_gibbs_rigidity_exponential_constant *
          Real.exp (-(q : ℝ) * D.expansionData.gap) ∧
      D.leftLeakRatio q ≤
        D.pom_zero_temperature_gibbs_rigidity_exponential_constant *
          Real.exp (-(q : ℝ) * D.expansionData.gap)

end pom_zero_temperature_gibbs_rigidity_data

open pom_zero_temperature_gibbs_rigidity_data

/-- Paper label: `thm:pom-zero-temperature-gibbs-rigidity`. -/
theorem paper_pom_zero_temperature_gibbs_rigidity
    (D : pom_zero_temperature_gibbs_rigidity_data) : D.exponential_concentration := by
  intro q hq
  rcases paper_pom_low_temperature_three_term_expansion D.expansionData with
    ⟨hLeadingExpansion, hErrorBound⟩
  have hLeading := hLeadingExpansion q hq
  have hRemainderBound :
      D.expansionData.remainder q ≤
        D.expansionData.errorConstant * Real.exp (-(q : ℝ) * D.expansionData.gap) := by
    have hdiff :
        D.expansionData.pressure q -
            ((q : ℝ) * Real.log D.expansionData.aStar + Real.log D.expansionData.rhoStar) =
          D.expansionData.remainder q := by
      linarith
    simpa [hdiff] using (hErrorBound q hq).2
  have hScaleNonneg :
      0 ≤ Real.exp (-(q : ℝ) * D.expansionData.gap) := by
    exact le_of_lt (Real.exp_pos _)
  refine ⟨?_, ?_, ?_⟩
  · have hTransfer := D.hStationaryMassTransfer q hq
    unfold pom_zero_temperature_gibbs_rigidity_exponential_constant
    nlinarith [hTransfer, hRemainderBound, D.hPerronLeakConstant, hScaleNonneg]
  · have hTransfer := D.hRightLeakTransfer q hq
    unfold pom_zero_temperature_gibbs_rigidity_exponential_constant
    nlinarith [hTransfer, hRemainderBound, D.hPerronLeakConstant, hScaleNonneg]
  · have hTransfer := D.hLeftLeakTransfer q hq
    unfold pom_zero_temperature_gibbs_rigidity_exponential_constant
    nlinarith [hTransfer, hRemainderBound, D.hPerronLeakConstant, hScaleNonneg]

end Omega.POM
