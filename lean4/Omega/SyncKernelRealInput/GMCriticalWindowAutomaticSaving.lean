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

/-- Concrete rational exponent data for the automatic-coefficient critical window. -/
structure gm_critical_window_automatic_saving_data where
  TExp : ℚ
  VExp : ℚ
  eps : ℚ
  TExp_eq : TExp = 6 / 5
  VExp_eq : VExp = 3 / 4
  eps_pos : 0 < eps

/-- The displayed exponent before the `V^{-4}` factor. -/
def gm_critical_window_automatic_saving_displayExponent
    (D : gm_critical_window_automatic_saving_data) : ℚ :=
  D.TExp + 6 / 5 - D.eps

/-- The total exponent after substituting the critical threshold `V = N^(3/4)`. -/
def gm_critical_window_automatic_saving_totalExponent
    (D : gm_critical_window_automatic_saving_data) : ℚ :=
  gm_critical_window_automatic_saving_displayExponent D - 4 * D.VExp

/-- The critical-window rational exponent calculation. -/
def gm_critical_window_automatic_saving_statement
    (D : gm_critical_window_automatic_saving_data) : Prop :=
  gm_critical_window_automatic_saving_displayExponent D = 12 / 5 - D.eps ∧
    gm_critical_window_automatic_saving_totalExponent D = -3 / 5 - D.eps ∧
      0 < D.eps

/-- The algebra behind the displayed large-values exponent after substituting
`T = N^(6/5)` and `V = N^(3/4)`. -/
theorem gm_critical_window_automatic_saving_exponent_algebra
    (D : gm_critical_window_automatic_saving_data) :
    gm_critical_window_automatic_saving_statement D := by
  refine ⟨?_, ?_, D.eps_pos⟩
  · unfold gm_critical_window_automatic_saving_displayExponent
    rw [D.TExp_eq]
    ring
  · unfold gm_critical_window_automatic_saving_totalExponent
      gm_critical_window_automatic_saving_displayExponent
    rw [D.TExp_eq, D.VExp_eq]
    ring

end Omega.SyncKernelRealInput
