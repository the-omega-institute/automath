import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-euler-diagonal-identity`. -/
theorem paper_pom_diagonal_rate_euler_diagonal_identity
    (Hw R delta Rp avgLogDiag kappa : ℝ)
    (hkappa : kappa = Real.exp (-Rp) - 1)
    (hdiag : R = Hw + avgLogDiag - delta * Real.log (1 + kappa)) :
    R = Hw + avgLogDiag + delta * Rp := by
  calc
    R = Hw + avgLogDiag - delta * Real.log (1 + (Real.exp (-Rp) - 1)) := by
      simpa [hkappa] using hdiag
    _ = Hw + avgLogDiag - delta * Real.log (Real.exp (-Rp)) := by
      congr 1
      ring_nf
    _ = Hw + avgLogDiag - delta * (-Rp) := by
      rw [Real.log_exp]
    _ = Hw + avgLogDiag + delta * Rp := by
      ring

end Omega.POM
