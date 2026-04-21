import Mathlib.Tactic

namespace Omega.POM

/-- Endpoint maximum fiber probability packaged from the parity closed forms. -/
noncomputable def pMax (m : ℕ) : ℝ :=
  if m % 2 = 0 then
    (Nat.fib (m / 2 + 2) : ℝ) / (2 : ℝ) ^ m
  else
    (Nat.fib ((m + 1) / 2) : ℝ) / (2 : ℝ) ^ (m - 1)

/-- Paper label: `cor:pom-max-fiber-rate-endpoint`. -/
theorem paper_pom_max_fiber_rate_endpoint (k : ℕ) :
    pMax (2 * k) = (Nat.fib (k + 2) : ℝ) / (2 : ℝ) ^ (2 * k) ∧
      pMax (2 * k + 1) = (Nat.fib (k + 1) : ℝ) / (2 : ℝ) ^ (2 * k) := by
  constructor
  · have hEven : (2 * k) % 2 = 0 := by omega
    have hHalf : (2 * k) / 2 = k := by omega
    simp [pMax, hEven, hHalf]
  · have hHalf : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have hPred : 2 * k + 1 - 1 = 2 * k := by omega
    simp [pMax, hHalf, hPred]

end Omega.POM
