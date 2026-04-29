import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:real-input-40-reduced-mertens`. The displayed reduced finite-part
decomposition is the algebraic rearrangement of the isolated trivial-factor contribution. -/
theorem paper_real_input_40_reduced_mertens (logM logMnt zstar : ℝ) (a b : ℕ)
    (htriv :
      logM - logMnt = ((a : ℝ) - (b : ℝ)) * zstar + (b : ℝ) * zstar ^ 2) :
    logM = logMnt + ((a : ℝ) - (b : ℝ)) * zstar + (b : ℝ) * zstar ^ 2 := by
  linarith

end Omega.SyncKernelRealInput
