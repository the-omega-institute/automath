import Omega.CircleDimension.ImplementationStructuralHalfCircleDimension
import Omega.Folding.KilloNoFiniteAdditiveRegisterLinearization

namespace Omega.DerivedConsequences

/-- Concrete wrapper combining the structural half-circle dimension with the implementation-level
`Nat`-multiplication witness and the finite-register obstruction. -/
def derived_multiplicative_implementation_hom_gap_derived_multiplicative_implementation_hom_gap_statement :
    Prop :=
  (∀ a b : ℕ,
      Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_embedding
          (a * b) =
        a * b) ∧
    (∀ a b : ℕ,
      Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_embedding
          (a * b) =
        Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_embedding
            a *
          Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_embedding
            b) ∧
    (∀ k : ℕ, Omega.Folding.killoFiniteRegisterLinearizationObstructed k) ∧
    Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_additive_dim =
      (1 : ℚ) / (2 : ℚ) ∧
    Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_dim =
      (1 : ℚ) / (2 : ℚ)

local notation "derived_multiplicative_implementation_hom_gap_statement" =>
  derived_multiplicative_implementation_hom_gap_derived_multiplicative_implementation_hom_gap_statement

/-- Paper label: `thm:derived-multiplicative-implementation-hom-gap`. -/
theorem paper_derived_multiplicative_implementation_hom_gap :
    derived_multiplicative_implementation_hom_gap_statement := by
  rcases Omega.CircleDimension.paper_killo_implementation_vs_structural_half_circle_dimension with
    ⟨hadd, hlin, _, himpl⟩
  refine ⟨?_, ?_, ?_, hadd, himpl⟩
  · intro a b
    rfl
  · intro a b
    rfl
  · intro k
    exact Omega.Folding.paper_killo_no_finite_additive_register_linearization k

end Omega.DerivedConsequences
