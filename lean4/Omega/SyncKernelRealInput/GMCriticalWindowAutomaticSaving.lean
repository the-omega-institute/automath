import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Concrete critical-window data for the automatic Dirichlet moment-saving corollary. -/
structure gm_critical_window_automatic_saving_Data where
  N : ℝ
  T : ℝ
  V : ℝ
  thresholdConstant : ℝ
  largeValueCount : ℝ
  savingEpsilon : ℝ
  savingEpsilon_pos : 0 < savingEpsilon
  criticalScaling : T = N ^ (6 / 5 : ℝ)
  thresholdScaling : V = thresholdConstant * N ^ (3 / 4 : ℝ)
  automaticMomentSaving :
    largeValueCount ≤ N ^ (12 / 5 - savingEpsilon : ℝ) * V ^ (-(4 : ℝ))

namespace gm_critical_window_automatic_saving_Data

/-- The critical-window large-value saving exposed with an explicit positive epsilon. -/
def criticalWindowSaving (D : gm_critical_window_automatic_saving_Data) : Prop :=
  ∃ ε : ℝ,
    0 < ε ∧
      D.T = D.N ^ (6 / 5 : ℝ) ∧
      D.V = D.thresholdConstant * D.N ^ (3 / 4 : ℝ) ∧
      D.largeValueCount ≤ D.N ^ (12 / 5 - ε : ℝ) * D.V ^ (-(4 : ℝ))

end gm_critical_window_automatic_saving_Data

/-- Paper label: `cor:gm-critical-window-automatic-saving`. The automatic moment-saving
hypothesis supplies a positive exponent witness, and the critical scalings expose the
large-value bound at `T = N^(6/5)` and `V` proportional to `N^(3/4)`. -/
theorem paper_gm_critical_window_automatic_saving
    (D : gm_critical_window_automatic_saving_Data) :
    D.criticalWindowSaving := by
  exact ⟨D.savingEpsilon, D.savingEpsilon_pos, D.criticalScaling, D.thresholdScaling,
    D.automaticMomentSaving⟩

end

end Omega.SyncKernelRealInput
