import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-diagonal-determines-spectrum`. -/
theorem paper_pom_diagonal_rate_diagonal_determines_spectrum
    (kappa : ℝ) (hkappa : 0 < kappa) :
    let paper_pom_diagonal_rate_diagonal_determines_spectrum_P : ℝ → ℝ := fun z => kappa + 1 - z
    let paper_pom_diagonal_rate_diagonal_determines_spectrum_det : ℝ → ℝ :=
      fun z => z * (-1) + kappa *
        paper_pom_diagonal_rate_diagonal_determines_spectrum_P z
    let paper_pom_diagonal_rate_diagonal_determines_spectrum_zeta : ℝ → ℝ :=
      fun z => 1 / paper_pom_diagonal_rate_diagonal_determines_spectrum_det z
    let paper_pom_diagonal_rate_diagonal_determines_spectrum_mu : ℝ := 1 / kappa
    (∀ z, paper_pom_diagonal_rate_diagonal_determines_spectrum_zeta z =
      1 / paper_pom_diagonal_rate_diagonal_determines_spectrum_det z) ∧
      (∀ z, paper_pom_diagonal_rate_diagonal_determines_spectrum_det z =
        (kappa + 1) * (kappa - z)) ∧
      (∀ z, paper_pom_diagonal_rate_diagonal_determines_spectrum_det z = 0 ↔ z = kappa) ∧
      (∀ z, paper_pom_diagonal_rate_diagonal_determines_spectrum_det z = 0 ↔
        z = 1 / paper_pom_diagonal_rate_diagonal_determines_spectrum_mu) := by
  dsimp
  have hdet : ∀ z, (z * (-1) + kappa * (kappa + 1 - z)) = (kappa + 1) * (kappa - z) := by
    intro z
    ring
  have hroot : ∀ z, (z * (-1) + kappa * (kappa + 1 - z)) = 0 ↔ z = kappa := by
    intro z
    rw [hdet z]
    have hkappa_plus_one_ne : kappa + 1 ≠ 0 := by
      linarith
    constructor
    · intro hz
      have hkappa_minus_z : kappa - z = 0 := by
        rcases mul_eq_zero.mp hz with hzero | hkappa_minus_z
        · exact (hkappa_plus_one_ne hzero).elim
        · exact hkappa_minus_z
      linarith
    · intro hz
      simp [hz]
  refine ⟨?_, hdet, hroot, ?_⟩
  · intro z
    rfl
  · intro z
    have hkappa_ne : kappa ≠ 0 := ne_of_gt hkappa
    have hrecip : 1 / (1 / kappa) = kappa := by
      field_simp [hkappa_ne]
    simpa [hrecip] using hroot z

end Omega.POM
