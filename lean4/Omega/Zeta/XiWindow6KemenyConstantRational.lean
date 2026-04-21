import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The cubic factor `p(t)` appearing after splitting off the trivial eigenvalue `t = 1`. -/
def xiWindow6ResidualPolynomial (t : ℚ) : ℚ :=
  (48114 * t ^ 3 + 7263 * t ^ 2 - 506 * t - 55) / 48114

/-- The formal derivative `p'(t)` of the explicit cubic factor. -/
def xiWindow6ResidualPolynomialDeriv (t : ℚ) : ℚ :=
  (3 * 48114 * t ^ 2 + 2 * 7263 * t - 506) / 48114

/-- The Kemeny constant recovered from the logarithmic derivative at `t = 1`. -/
def xiWindow6KemenyConstant : ℚ :=
  xiWindow6ResidualPolynomialDeriv 1 / xiWindow6ResidualPolynomial 1

/-- Spectral-side expression for the Kemeny constant when the nontrivial spectrum is listed as
`λ₀, λ₁, λ₂`. -/
def xiWindow6KemenyFromSpectrum (lam : Fin 3 → ℚ) : ℚ :=
  ∑ i, 1 / (1 - lam i)

/-- The cubic with roots `λ₀, λ₁, λ₂`. -/
def xiWindow6FactorizedCubic (lam : Fin 3 → ℚ) (t : ℚ) : ℚ :=
  (t - lam 0) * (t - lam 1) * (t - lam 2)

/-- The derivative of the factored cubic, evaluated at `t = 1`. -/
def xiWindow6FactorizedCubicDerivAtOne (lam : Fin 3 → ℚ) : ℚ :=
  (1 - lam 1) * (1 - lam 2) + (1 - lam 0) * (1 - lam 2) + (1 - lam 0) * (1 - lam 1)

/-- For a cubic split into the three nontrivial eigenvalues, the logarithmic derivative at
`t = 1` is the spectral Kemeny sum. -/
lemma xiWindow6_factorized_log_derivative (lam : Fin 3 → ℚ) (hlam : ∀ i, lam i ≠ 1) :
    xiWindow6FactorizedCubicDerivAtOne lam / xiWindow6FactorizedCubic lam 1 =
      xiWindow6KemenyFromSpectrum lam := by
  have h0 : (1 - lam 0) ≠ 0 := sub_ne_zero.mpr (by simpa [eq_comm] using hlam 0)
  have h1 : (1 - lam 1) ≠ 0 := sub_ne_zero.mpr (by simpa [eq_comm] using hlam 1)
  have h2 : (1 - lam 2) ≠ 0 := sub_ne_zero.mpr (by simpa [eq_comm] using hlam 2)
  have hsum :
      xiWindow6KemenyFromSpectrum lam =
        1 / (1 - lam 0) + 1 / (1 - lam 1) + 1 / (1 - lam 2) := by
    rw [xiWindow6KemenyFromSpectrum, Fin.sum_univ_three]
  have hden : xiWindow6FactorizedCubic lam 1 ≠ 0 := by
    simp [xiWindow6FactorizedCubic, h0, h1, h2]
  apply (div_eq_iff hden).2
  rw [hsum]
  calc
    xiWindow6FactorizedCubicDerivAtOne lam
        = 3 - lam 2 * 2 + lam 2 * lam 1 + (lam 2 * lam 0 - lam 1 * 2) +
            (lam 1 * lam 0 - lam 0 * 2) := by
            unfold xiWindow6FactorizedCubicDerivAtOne
            ring
    _ = ((1 - lam 0) * (1 - lam 1) * (1 - lam 2)) *
          (1 / (1 - lam 0) + 1 / (1 - lam 1) + 1 / (1 - lam 2)) := by
            field_simp [h0, h1, h2]
            ring
    _ = (1 / (1 - lam 0) + 1 / (1 - lam 1) + 1 / (1 - lam 2)) *
          xiWindow6FactorizedCubic lam 1 := by
            simp [xiWindow6FactorizedCubic, mul_comm, mul_assoc]

/-- The audited window-`6` Kemeny constant is the logarithmic derivative `p'(1)/p(1)`, and this
explicit rational equals `79181 / 27408`.
    prop:xi-window6-kemeny-constant-rational -/
theorem paper_xi_window6_kemeny_constant_rational :
    xiWindow6KemenyConstant = xiWindow6ResidualPolynomialDeriv 1 / xiWindow6ResidualPolynomial 1 ∧
      xiWindow6KemenyConstant = 79181 / 27408 := by
  refine ⟨rfl, ?_⟩
  norm_num [xiWindow6KemenyConstant, xiWindow6ResidualPolynomial, xiWindow6ResidualPolynomialDeriv]

end Omega.Zeta
