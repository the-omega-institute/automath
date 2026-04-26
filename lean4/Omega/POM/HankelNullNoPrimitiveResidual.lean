import Mathlib.Tactic
import Omega.POM.ResonanceHankelNullAllScales

namespace Omega.POM

/-- Concrete wrapper for the resonance Hankel-null primitive quotient.  The all-scales package
identifies null modes with the truncated multiple module; the polynomial fields expose the
corresponding factorization and zero-remainder certificate for each null-mode vector. -/
structure pom_hankel_null_no_primitive_residual_data where
  allScalesData : ResonanceHankelNullAllScalesData
  primitiveQuotientDim : ℕ
  primitiveQuotientDim_eq_zero_of_eq :
    allScalesData.nullModeKernel = allScalesData.multipleModule → primitiveQuotientDim = 0
  minimalPolynomial : Polynomial ℤ
  nullModePolynomial : (Fin allScalesData.m → ℤ) → Polynomial ℤ
  quotientPolynomial : (Fin allScalesData.m → ℤ) → Polynomial ℤ
  remainderPolynomial : (Fin allScalesData.m → ℤ) → Polynomial ℤ
  multipleModule_spec :
    ∀ alpha : Fin allScalesData.m → ℤ,
      alpha ∈ allScalesData.multipleModule ↔
        nullModePolynomial alpha = quotientPolynomial alpha * minimalPolynomial ∧
          remainderPolynomial alpha = 0

namespace pom_hankel_null_no_primitive_residual_data

/-- Paper-facing statement: the primitive quotient has dimension zero, and every null mode is a
polynomial multiple of the minimal recurrence polynomial with zero remainder. -/
def pom_hankel_null_no_primitive_residual_statement
    (D : pom_hankel_null_no_primitive_residual_data) : Prop :=
  D.primitiveQuotientDim = 0 ∧
    ∀ alpha : Fin D.allScalesData.m → ℤ,
      alpha ∈ D.allScalesData.nullModeKernel →
        D.nullModePolynomial alpha = D.quotientPolynomial alpha * D.minimalPolynomial ∧
          D.remainderPolynomial alpha = 0

end pom_hankel_null_no_primitive_residual_data

open pom_hankel_null_no_primitive_residual_data

/-- Paper label: `cor:pom-hankel-null-no-primitive-residual`. -/
theorem paper_pom_hankel_null_no_primitive_residual
    (D : pom_hankel_null_no_primitive_residual_data) :
    pom_hankel_null_no_primitive_residual_statement D := by
  rcases paper_pom_resonance_hankel_null_all_scales D.allScalesData with ⟨hEq, _hRank⟩
  have hEq' :
      D.allScalesData.nullModeKernel = D.allScalesData.multipleModule := by
    simpa [ResonanceHankelNullAllScalesData.nullModesEqMultiplesAtAllScales] using hEq
  refine ⟨D.primitiveQuotientDim_eq_zero_of_eq hEq', ?_⟩
  intro alpha halpha
  exact (D.multipleModule_spec alpha).1 (by simpa [← hEq'] using halpha)

end Omega.POM
