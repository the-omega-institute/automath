import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the lower Poisson bound, the Taylor reverse-KL estimate, and the
Parseval/Fourier energy identity used in
`thm:xi-time-part9d-reversekl-l2-fourier`. -/
structure xi_time_part9d_reversekl_l2_fourier_data where
  r : ℝ
  reverseKL : ℝ
  poissonLower : ℝ
  l2Energy : ℝ
  fourierEnergy : ℝ
  h_r_pos : 0 < r
  h_r_lt_one : r < 1
  h_poissonLower : poissonLower = (1 - r) / (1 + r)
  h_reverseKL_taylor : reverseKL ≤ poissonLower⁻¹ ^ 2 * l2Energy
  h_parseval_fourier : l2Energy = fourierEnergy

/-- Paper label: `thm:xi-time-part9d-reversekl-l2-fourier`. -/
theorem paper_xi_time_part9d_reversekl_l2_fourier
    (D : xi_time_part9d_reversekl_l2_fourier_data) :
    D.reverseKL ≤ ((1 + D.r) / (1 - D.r)) ^ 2 * D.fourierEnergy := by
  have h_one_sub_ne : 1 - D.r ≠ 0 := by linarith [D.h_r_lt_one]
  have h_one_add_ne : 1 + D.r ≠ 0 := by linarith [D.h_r_pos]
  have h_inv : D.poissonLower⁻¹ = (1 + D.r) / (1 - D.r) := by
    rw [D.h_poissonLower]
    field_simp [h_one_sub_ne, h_one_add_ne]
  calc
    D.reverseKL ≤ D.poissonLower⁻¹ ^ 2 * D.l2Energy := D.h_reverseKL_taylor
    _ = ((1 + D.r) / (1 - D.r)) ^ 2 * D.fourierEnergy := by
      rw [h_inv, D.h_parseval_fourier]

end Omega.Zeta
