import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite Fourier-coordinate data for a convolution operator already expressed in its
Fourier basis.  The coefficients are the Fourier multipliers, and `dominantMode` records the
nonnegative maximal multiplier used for the operator-norm statement. -/
structure conclusion_farey_limit_kernel_fourier_diagonalization_data where
  conclusion_farey_limit_kernel_fourier_diagonalization_dimension : ℕ
  conclusion_farey_limit_kernel_fourier_diagonalization_dimension_pos :
    0 < conclusion_farey_limit_kernel_fourier_diagonalization_dimension
  conclusion_farey_limit_kernel_fourier_diagonalization_coeff :
    Fin conclusion_farey_limit_kernel_fourier_diagonalization_dimension → ℝ
  conclusion_farey_limit_kernel_fourier_diagonalization_coeff_nonnegative :
    ∀ n, 0 ≤ conclusion_farey_limit_kernel_fourier_diagonalization_coeff n
  conclusion_farey_limit_kernel_fourier_diagonalization_dominantMode :
    Fin conclusion_farey_limit_kernel_fourier_diagonalization_dimension
  conclusion_farey_limit_kernel_fourier_diagonalization_dominant_spec :
    ∀ n,
      conclusion_farey_limit_kernel_fourier_diagonalization_coeff n ≤
        conclusion_farey_limit_kernel_fourier_diagonalization_coeff
          conclusion_farey_limit_kernel_fourier_diagonalization_dominantMode

namespace conclusion_farey_limit_kernel_fourier_diagonalization_data

/-- The standard Fourier coordinate vector with frequency `n`. -/
def conclusion_farey_limit_kernel_fourier_diagonalization_fourierBasis
    (D : conclusion_farey_limit_kernel_fourier_diagonalization_data)
    (n : Fin D.conclusion_farey_limit_kernel_fourier_diagonalization_dimension) :
    Fin D.conclusion_farey_limit_kernel_fourier_diagonalization_dimension → ℝ :=
  fun k => if k = n then 1 else 0

/-- The convolution operator in Fourier coordinates: multiplication by the Fourier coefficient. -/
def conclusion_farey_limit_kernel_fourier_diagonalization_convolutionOperator
    (D : conclusion_farey_limit_kernel_fourier_diagonalization_data)
    (v : Fin D.conclusion_farey_limit_kernel_fourier_diagonalization_dimension → ℝ) :
    Fin D.conclusion_farey_limit_kernel_fourier_diagonalization_dimension → ℝ :=
  fun k => D.conclusion_farey_limit_kernel_fourier_diagonalization_coeff k * v k

/-- The operator norm of a nonnegative diagonal Fourier multiplier. -/
def conclusion_farey_limit_kernel_fourier_diagonalization_operatorNorm
    (D : conclusion_farey_limit_kernel_fourier_diagonalization_data) : ℝ :=
  D.conclusion_farey_limit_kernel_fourier_diagonalization_coeff
    D.conclusion_farey_limit_kernel_fourier_diagonalization_dominantMode

/-- Concrete Fourier diagonalization and nonnegative norm package. -/
def conclusion_farey_limit_kernel_fourier_diagonalization_statement
    (D : conclusion_farey_limit_kernel_fourier_diagonalization_data) : Prop :=
  (∀ n,
      D.conclusion_farey_limit_kernel_fourier_diagonalization_convolutionOperator
          (D.conclusion_farey_limit_kernel_fourier_diagonalization_fourierBasis n) =
        fun k =>
          D.conclusion_farey_limit_kernel_fourier_diagonalization_coeff n *
            D.conclusion_farey_limit_kernel_fourier_diagonalization_fourierBasis n k) ∧
    D.conclusion_farey_limit_kernel_fourier_diagonalization_operatorNorm =
      D.conclusion_farey_limit_kernel_fourier_diagonalization_coeff
        D.conclusion_farey_limit_kernel_fourier_diagonalization_dominantMode ∧
    (∀ n,
      0 ≤ D.conclusion_farey_limit_kernel_fourier_diagonalization_coeff n ∧
        D.conclusion_farey_limit_kernel_fourier_diagonalization_coeff n ≤
          D.conclusion_farey_limit_kernel_fourier_diagonalization_operatorNorm)

end conclusion_farey_limit_kernel_fourier_diagonalization_data

open conclusion_farey_limit_kernel_fourier_diagonalization_data

/-- Paper label: `thm:conclusion-farey-limit-kernel-fourier-diagonalization`. -/
theorem paper_conclusion_farey_limit_kernel_fourier_diagonalization
    (D : conclusion_farey_limit_kernel_fourier_diagonalization_data) :
    D.conclusion_farey_limit_kernel_fourier_diagonalization_statement := by
  unfold conclusion_farey_limit_kernel_fourier_diagonalization_statement
  refine ⟨?_, rfl, ?_⟩
  · intro n
    funext k
    by_cases hk : k = n
    · subst hk
      simp [conclusion_farey_limit_kernel_fourier_diagonalization_convolutionOperator,
        conclusion_farey_limit_kernel_fourier_diagonalization_fourierBasis]
    · simp [conclusion_farey_limit_kernel_fourier_diagonalization_convolutionOperator,
        conclusion_farey_limit_kernel_fourier_diagonalization_fourierBasis, hk]
  · intro n
    exact ⟨D.conclusion_farey_limit_kernel_fourier_diagonalization_coeff_nonnegative n,
      D.conclusion_farey_limit_kernel_fourier_diagonalization_dominant_spec n⟩

end Omega.Conclusion
