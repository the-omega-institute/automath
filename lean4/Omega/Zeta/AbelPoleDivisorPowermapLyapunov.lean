import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-abel-pole-divisor-powermap-lyapunov`. -/
theorem paper_xi_abel_pole_divisor_powermap_lyapunov {lambda : ℂ} (hlambda : lambda ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    (fun n : ℕ => lambda ^ (k * n)) = (fun n : ℕ => (lambda ^ k) ^ n) ∧
      (lambda ^ k)⁻¹ = (lambda⁻¹) ^ k := by
  let _ := hlambda
  let _ := hk
  constructor
  · funext n
    rw [pow_mul]
  · rw [inv_pow]

end Omega.Zeta
