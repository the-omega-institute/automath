import Omega.CircleDimension.ImplementationStructuralHalfCircleDimension
import Omega.Folding.KilloEllipseDiagonalPrimeRegisterEquivalence

namespace Omega.Conclusion

open Omega.CircleDimension
open Omega.Folding

/-- Paper label: `thm:conclusion-integer-ellipse-double-register-free-realization`. The diagonal
integer-ellipse monoid is the concrete two-register prime-exponent model, admits no faithful
finite additive linearization, and keeps both half-circle-dimension normalizations at `1/2`. -/
theorem paper_conclusion_integer_ellipse_double_register_free_realization :
    killoEllipseDiagonalPrimeRegisterEquivalence ∧
      (∀ k : ℕ, killoFiniteRegisterLinearizationObstructed k) ∧
      Function.Injective killo_implementation_vs_structural_half_circle_dimension_impl_embedding ∧
      killo_implementation_vs_structural_half_circle_dimension_additive_dim = (1 : ℚ) / 2 ∧
      killo_implementation_vs_structural_half_circle_dimension_impl_dim = (1 : ℚ) / 2 := by
  rcases paper_killo_implementation_vs_structural_half_circle_dimension with
    ⟨hadd, hobstruct, himpl, himpldim⟩
  refine ⟨paper_killo_ellipse_diagonal_prime_register_equivalence, hobstruct, himpl, hadd,
    himpldim⟩

end Omega.Conclusion
