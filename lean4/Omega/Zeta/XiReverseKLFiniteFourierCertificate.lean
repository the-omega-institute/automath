import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-reversekl-finite-fourier-certificate`.

The finite Fourier lower certificate and the global upper bound combine with the uniform geometric
tail estimate by monotonicity of multiplication by the nonnegative square `br ^ 2`. -/
theorem paper_xi_reversekl_finite_fourier_certificate (r Hr ar br «prefix» total : ℝ) (N : ℕ)
    (hLower : ar ^ 2 * «prefix» ≤ Hr) (hUpper : Hr ≤ br ^ 2 * total)
    (hTail : total ≤ «prefix» + r ^ (2 * (N + 1)) / (1 - r ^ 2)) :
    ar ^ 2 * «prefix» ≤ Hr ∧
      Hr ≤ br ^ 2 * («prefix» + r ^ (2 * (N + 1)) / (1 - r ^ 2)) := by
  refine ⟨hLower, ?_⟩
  exact le_trans hUpper (mul_le_mul_of_nonneg_left hTail (sq_nonneg br))

end Omega.Zeta
