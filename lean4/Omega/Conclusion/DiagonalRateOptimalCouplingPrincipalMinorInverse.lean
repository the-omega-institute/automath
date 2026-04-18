import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.DiagonalRateScalarCollapse

namespace Omega.Conclusion

noncomputable section

open scoped BigOperators

/-- Closed-form principal minor from the diagonal-rate optimal-coupling parametrization
`(1 / Z) * U * (κ I + J) * U`. -/
def diagonalRatePrincipalMinor {n : ℕ}
    (κ Z : ℝ) (u : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  κ ^ (S.card - 1) * (κ + S.card) / Z ^ S.card * ∏ i ∈ S, (u i) ^ 2

/-- Closed-form inverse entry from the same parametrization. -/
def diagonalRateInverseEntry
    (n : ℕ) (κ Z : ℝ) (u : Fin n → ℝ) (i j : Fin n) : ℝ :=
  if h : i = j then
    Z / κ * (u i)⁻¹ * (u i)⁻¹ - Z / (κ * (κ + n)) * (u i)⁻¹ * (u i)⁻¹
  else
    -(Z / (κ * (κ + n)) * (u i)⁻¹ * (u j)⁻¹)

/-- The top eigenvalue of the normalized matrix `(1 / Z) * (κ I + J)`. -/
def diagonalRateNormalizedTopEigenvalue (n : ℕ) (κ Z : ℝ) : ℝ :=
  (κ + n) / Z

/-- The repeated bulk eigenvalue of the normalized matrix `(1 / Z) * (κ I + J)`. -/
def diagonalRateNormalizedBulkEigenvalue (κ Z : ℝ) : ℝ :=
  κ / Z

/-- The normalized condition number extracted from the two closed-form eigenvalues. -/
def diagonalRateNormalizedConditionNumber (n : ℕ) (κ Z : ℝ) : ℝ :=
  diagonalRateNormalizedTopEigenvalue n κ Z / diagonalRateNormalizedBulkEigenvalue κ Z

theorem diagonalRatePrincipalMinor_pos {n : ℕ} {κ Z : ℝ} (hκ : 0 < κ) (hZ : 0 < Z)
    (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) (S : Finset (Fin n)) (hS : S.Nonempty) :
    0 < diagonalRatePrincipalMinor κ Z u S := by
  have hPow : 0 < κ ^ (S.card - 1) := pow_pos hκ _
  have hCard : 0 < κ + S.card := by
    positivity
  have hDen : 0 < Z ^ S.card := pow_pos hZ _
  have hProd : 0 < ∏ i ∈ S, (u i) ^ 2 := by
    refine Finset.prod_pos ?_
    intro i hi
    exact sq_pos_of_pos (hu i)
  unfold diagonalRatePrincipalMinor
  exact mul_pos (div_pos (mul_pos hPow hCard) hDen) hProd

theorem diagonalRateInverseEntry_offDiag_neg
    {n : ℕ} {κ Z : ℝ} (hκ : 0 < κ) (hZ : 0 < Z)
    (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) (i j : Fin n) (hij : i ≠ j) :
    diagonalRateInverseEntry n κ Z u i j < 0 := by
  have hκn : 0 < κ + n := by positivity
  have hTerm : 0 < Z / (κ * (κ + n)) * (u i)⁻¹ * (u j)⁻¹ := by
    have hBase : 0 < Z / (κ * (κ + n)) := div_pos hZ (mul_pos hκ hκn)
    exact mul_pos (mul_pos hBase (inv_pos.mpr (hu i))) (inv_pos.mpr (hu j))
  have hNeg : -(Z / (κ * (κ + n)) * (u i)⁻¹ * (u j)⁻¹) < 0 := by
    linarith
  simpa [diagonalRateInverseEntry, hij] using hNeg

theorem diagonalRateNormalizedConditionNumber_eq
    (n : ℕ) {κ Z : ℝ} (hκ : 0 < κ) (hZ : 0 < Z) :
    diagonalRateNormalizedConditionNumber n κ Z = 1 + n / κ := by
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ
  unfold diagonalRateNormalizedConditionNumber
    diagonalRateNormalizedTopEigenvalue diagonalRateNormalizedBulkEigenvalue
  field_simp [hκ_ne, hZ_ne]

/-- The scalar-collapse diagonal-rate parametrization yields closed principal-minor and inverse-sign
formulas, together with the normalized eigenvalue and condition-number package.
    thm:conclusion-diagonal-rate-optimal-coupling-principal-minor-inverse -/
theorem paper_conclusion_diagonal_rate_optimal_coupling_principal_minor_inverse :
    ∀ {n : ℕ} {κ Z : ℝ},
      0 < κ → 0 < Z →
      ∀ u : Fin n → ℝ, (∀ i, 0 < u i) →
        diagonalRatePrincipalMinor κ Z u Finset.univ =
            κ ^ (n - 1) * (κ + n) / Z ^ n * ∏ i, (u i) ^ 2 ∧
          (∀ S : Finset (Fin n), S.Nonempty → 0 < diagonalRatePrincipalMinor κ Z u S) ∧
          (∀ i j : Fin n, i ≠ j → diagonalRateInverseEntry n κ Z u i j < 0) ∧
          0 < diagonalRateNormalizedBulkEigenvalue κ Z ∧
          0 < diagonalRateNormalizedTopEigenvalue n κ Z ∧
          diagonalRateNormalizedConditionNumber n κ Z = 1 + n / κ := by
  intro n κ Z hκ hZ u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [diagonalRatePrincipalMinor]
  · intro S hS
    exact diagonalRatePrincipalMinor_pos hκ hZ u hu S hS
  · intro i j hij
    exact diagonalRateInverseEntry_offDiag_neg hκ hZ u hu i j hij
  · unfold diagonalRateNormalizedBulkEigenvalue
    exact div_pos hκ hZ
  · unfold diagonalRateNormalizedTopEigenvalue
    positivity
  · exact diagonalRateNormalizedConditionNumber_eq n hκ hZ

end

end Omega.Conclusion
