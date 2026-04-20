import Mathlib

namespace Omega.Zeta

/-- The degree-two local Lee--Yang factor attached to the diagonal `SU(2)` eigenphases
`u` and `u⁻¹`. -/
noncomputable def operatorLocalLeyangPolynomial (u : ℂ) : Polynomial ℂ :=
  1 - Polynomial.C (u + u⁻¹) * Polynomial.X + Polynomial.X ^ 2

/-- Paper-facing `SU(2)` specialization of the local Lee--Yang Euler factor: the quadratic has
constant and leading coefficient `1`, vanishes at `u` and `u⁻¹`, and both roots lie on the unit
circle.
    cor:operator-local-leyang-selfreciprocal-unitcircle -/
theorem paper_operator_local_leyang_selfreciprocal_unitcircle (u : ℂ) (hu : ‖u‖ = 1) :
    let P := operatorLocalLeyangPolynomial u
    P.coeff 0 = 1 ∧
      P.coeff 2 = 1 ∧
      1 - (u + u⁻¹) * u + u ^ 2 = 0 ∧
      1 - (u + u⁻¹) * u⁻¹ + (u⁻¹) ^ 2 = 0 ∧
      ‖u‖ = 1 ∧
      ‖u⁻¹‖ = 1 := by
  dsimp
  have hu0 : u ≠ 0 := by
    intro hu0
    simp [hu0] at hu
  refine ⟨?_, ?_, ?_, ?_, hu, ?_⟩
  · simp [operatorLocalLeyangPolynomial]
  · rw [operatorLocalLeyangPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub]
    simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]
  · have huinv : u⁻¹ * u = 1 := by
      field_simp [hu0]
    calc
      1 - (u + u⁻¹) * u + u ^ 2 = 1 - (u * u + u⁻¹ * u) + u ^ 2 := by ring
      _ = 0 := by simp [huinv, pow_two]
  · have huu : u * u⁻¹ = 1 := by
      field_simp [hu0]
    calc
      1 - (u + u⁻¹) * u⁻¹ + (u⁻¹) ^ 2 = 1 - (u * u⁻¹ + u⁻¹ * u⁻¹) + (u⁻¹) ^ 2 := by ring
      _ = 0 := by simp [huu, pow_two]
  · simpa [norm_inv] using hu

end Omega.Zeta
