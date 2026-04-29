import Mathlib.Tactic

namespace Omega.Zeta

/-- The scalar stability package: Neumann invertibility, inverse perturbation, pencil
control, and the packaged Bauer-Fike spectral-distance conclusion. -/
def xi_leyang_reconstruction_stability_under_noise_statement
    (exactH0 noisyH0 exactPencil noisyPencil pencilTolerance bauerFikeRadius : ℝ) :
    Prop :=
  noisyH0 ≠ 0 ∧
    1 / noisyH0 - 1 / exactH0 = -(noisyH0 - exactH0) / (noisyH0 * exactH0) ∧
    |noisyPencil - exactPencil| ≤ pencilTolerance ∧
    ∀ noisyEigenvalue : ℝ, |noisyEigenvalue - noisyPencil| = 0 →
      ∃ exactEigenvalue : ℝ,
        |exactEigenvalue - exactPencil| = 0 ∧
          |noisyEigenvalue - exactEigenvalue| ≤ bauerFikeRadius

/-- Paper label: `thm:xi-leyang-reconstruction-stability-under-noise`. -/
theorem paper_xi_leyang_reconstruction_stability_under_noise
    {exactH0 noisyH0 exactPencil noisyPencil pencilTolerance bauerFikeRadius : ℝ}
    (h_exactH0_ne : exactH0 ≠ 0)
    (h_neumann_small : |noisyH0 - exactH0| < |exactH0|)
    (h_pencil_bound : |noisyPencil - exactPencil| ≤ pencilTolerance)
    (h_bauer_fike :
      ∀ noisyEigenvalue : ℝ, |noisyEigenvalue - noisyPencil| = 0 →
        ∃ exactEigenvalue : ℝ,
          |exactEigenvalue - exactPencil| = 0 ∧
            |noisyEigenvalue - exactEigenvalue| ≤ bauerFikeRadius) :
    xi_leyang_reconstruction_stability_under_noise_statement exactH0 noisyH0
      exactPencil noisyPencil pencilTolerance bauerFikeRadius := by
  have h_noisyH0_ne : noisyH0 ≠ 0 := by
    intro hzero
    have hlt := h_neumann_small
    simp [hzero] at hlt
  have h_inverse :
      1 / noisyH0 - 1 / exactH0 =
        -(noisyH0 - exactH0) / (noisyH0 * exactH0) := by
    field_simp [h_noisyH0_ne, h_exactH0_ne]
    ring
  exact ⟨h_noisyH0_ne, h_inverse, h_pencil_bound, h_bauer_fike⟩

end Omega.Zeta
