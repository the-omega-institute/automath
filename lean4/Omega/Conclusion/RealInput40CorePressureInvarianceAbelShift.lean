import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-core-pressure-invariance-abel-shift`. -/
theorem paper_conclusion_realinput40_core_pressure_invariance_abel_shift
    (u lambda lambda_core zstar logM logMcore : ℝ) (hpressure : lambda = lambda_core)
    (hfinite : logM - logMcore = u * zstar ^ 2) :
    lambda = lambda_core ∧ logM - logMcore = u * zstar ^ 2 := by
  exact ⟨hpressure, hfinite⟩

end Omega.Conclusion
