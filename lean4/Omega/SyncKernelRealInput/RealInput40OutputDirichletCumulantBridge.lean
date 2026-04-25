import Mathlib.Analysis.SpecialFunctions.Exp

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:real-input-40-output-dirichlet-cumulant-bridge`. -/
theorem paper_real_input_40_output_dirichlet_cumulant_bridge (logRatio ratio theta rem : ℕ → ℝ)
    (kappa2 kappa4 : ℝ)
    (hlog : ∀ m,
      logRatio m = -(kappa2 / 2) * (theta m)^2 + (kappa4 / 24) * (theta m)^4 + rem m)
    (hratio : ∀ m, ratio m = Real.exp (logRatio m)) :
    ∀ m,
      ratio m =
        Real.exp (-(kappa2 / 2) * (theta m)^2 + (kappa4 / 24) * (theta m)^4 + rem m) := by
  intro m
  rw [hratio m, hlog m]

end Omega.SyncKernelRealInput
