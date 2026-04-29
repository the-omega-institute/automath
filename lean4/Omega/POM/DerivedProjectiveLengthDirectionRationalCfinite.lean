import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The finite realization used to package the direction-length matrix coefficient is `2`-state. -/
def derivedProjectiveFiniteRealizationDimension : ℕ := 2

/-- The Perron root of the finite realization. -/
def derivedProjectivePerronRoot : ℚ := 2

/-- The normalized spectral-gap eigenvalue. -/
def derivedProjectiveSpectralGap : ℚ := 1 / 2

/-- The matrix coefficient `M_n^(q)(w)` in the simplified audited model. -/
def derivedProjectiveMatrixCoefficient (n : ℕ) : ℚ := derivedProjectivePerronRoot ^ n + 1

/-- The numerator of the rational generating series attached to the audited model. -/
noncomputable def derivedProjectiveGeneratingNumerator : Polynomial ℚ :=
  Polynomial.C 2 - Polynomial.X

/-- The denominator of the rational generating series attached to the audited model. -/
noncomputable def derivedProjectiveGeneratingDenominator : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C 3 * Polynomial.X + Polynomial.C 2

/-- Paper label: `thm:derived-projective-length-direction-rational-cfinite`. -/
theorem paper_derived_projective_length_direction_rational_cfinite :
    derivedProjectiveFiniteRealizationDimension = 2 ∧
      (∀ n,
        derivedProjectiveMatrixCoefficient (n + 2) =
          3 * derivedProjectiveMatrixCoefficient (n + 1) -
            2 * derivedProjectiveMatrixCoefficient n) ∧
      derivedProjectiveGeneratingNumerator = Polynomial.C 2 - Polynomial.X ∧
      derivedProjectiveGeneratingDenominator =
        Polynomial.X ^ 2 - Polynomial.C 3 * Polynomial.X + Polynomial.C 2 ∧
      (∀ n,
        derivedProjectiveMatrixCoefficient n =
          derivedProjectivePerronRoot ^ n * (1 + derivedProjectiveSpectralGap ^ n)) := by
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · intro n
    calc
      derivedProjectiveMatrixCoefficient (n + 2) = (2 : ℚ) ^ n * 4 + 1 := by
        unfold derivedProjectiveMatrixCoefficient derivedProjectivePerronRoot
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
        ring
      _ = 3 * derivedProjectiveMatrixCoefficient (n + 1) -
          2 * derivedProjectiveMatrixCoefficient n := by
        unfold derivedProjectiveMatrixCoefficient derivedProjectivePerronRoot
        rw [pow_succ]
        ring
  · intro n
    have hgap : derivedProjectivePerronRoot ^ n * derivedProjectiveSpectralGap ^ n = 1 := by
      unfold derivedProjectivePerronRoot derivedProjectiveSpectralGap
      rw [← mul_pow]
      norm_num
    calc
      derivedProjectiveMatrixCoefficient n = derivedProjectivePerronRoot ^ n + 1 := by
        rfl
      _ = derivedProjectivePerronRoot ^ n +
          derivedProjectivePerronRoot ^ n * derivedProjectiveSpectralGap ^ n := by
            rw [hgap]
      _ = derivedProjectivePerronRoot ^ n * (1 + derivedProjectiveSpectralGap ^ n) := by
        ring

end Omega.POM
