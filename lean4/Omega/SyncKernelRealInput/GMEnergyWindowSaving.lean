import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:gm-energy-window-saving`. Substituting `T = N^(6/5)` gives the
rational exponent identity for the energy-coupling channel. -/
theorem paper_gm_energy_window_saving (theta : ℚ) :
    (6 / 5 : ℚ) * (1 - theta / 2) + (1 + theta / 2) = 11 / 5 - theta / 10 := by
  ring

end Omega.SyncKernelRealInput
