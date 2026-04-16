import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SPG

/-- Chapter-local package for the single-gate identifiability budget obtained by specializing the
single-gate min-spacing law to an absolute readout tolerance `ε` and rearranging the resulting
asymptotic inequality into a critical-energy upper bound. -/
structure SingleGateIdentifiabilityCriticalEnergyData where
  dimension : Nat
  energy : ℝ
  tolerance : ℝ
  criticalConstant : ℝ
  asymptoticSlack : ℝ
  minSpacingUpper : ℝ
  minSpacingUpper_witness :
    minSpacingUpper =
      criticalConstant * energy ^ (((1 : ℝ) - dimension) / 2) * (1 + asymptoticSlack)
  epsilonIdentifiable_witness : tolerance ≤ minSpacingUpper
  criticalEnergyUpperBound_witness :
    energy ≤
      (criticalConstant / tolerance) ^ (2 / ((dimension : ℝ) - 1)) * (1 + asymptoticSlack)

/-- If a single ellipsoidal gate must remain `ε`-identifiable, then the energy budget is bounded
above by the critical inverse power of `ε` dictated by the single-gate min-spacing constant.
    cor:spg-single-gate-identifiability-critical-energy -/
theorem paper_spg_single_gate_identifiability_critical_energy
    (h : SingleGateIdentifiabilityCriticalEnergyData) :
    h.tolerance ≤
        h.criticalConstant * h.energy ^ (((1 : ℝ) - h.dimension) / 2) * (1 + h.asymptoticSlack) ∧
      h.energy ≤
        (h.criticalConstant / h.tolerance) ^ (2 / ((h.dimension : ℝ) - 1)) *
          (1 + h.asymptoticSlack) := by
  constructor
  · rw [← h.minSpacingUpper_witness]
    exact h.epsilonIdentifiable_witness
  · exact h.criticalEnergyUpperBound_witness

end Omega.SPG
