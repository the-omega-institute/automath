import Mathlib.Tactic
import Omega.CircleDimension.CircleDim
import Omega.Folding.KilloNoFiniteAdditiveRegisterLinearization

namespace Omega.CircleDimension

/-- The additive structural half-circle dimension is the rank-one baseline `1/2`. -/
def killo_implementation_vs_structural_half_circle_dimension_additive_dim : ℚ :=
  halfCircleDim 1 0

/-- The implementation-level witness is the canonical injection of the countable multiplicative
carrier into `ℕ`. -/
def killo_implementation_vs_structural_half_circle_dimension_impl_embedding : ℕ → ℕ :=
  id

/-- The implementation half-circle dimension again collapses to the single visible half-axis. -/
def killo_implementation_vs_structural_half_circle_dimension_impl_dim : ℚ :=
  halfCircleDim 1 0

/-- Paper-facing formulation of the strict gap: the additive model sits at `1/2`, every finite
additive linearization of the multiplicative model is obstructed, and the implementation layer is
still witnessed inside one copy of `ℕ`. -/
def killo_implementation_vs_structural_half_circle_dimension_statement : Prop :=
  killo_implementation_vs_structural_half_circle_dimension_additive_dim = (1 : ℚ) / (2 : ℚ) ∧
    (∀ k : ℕ, Omega.Folding.killoFiniteRegisterLinearizationObstructed k) ∧
    Function.Injective
      killo_implementation_vs_structural_half_circle_dimension_impl_embedding ∧
    killo_implementation_vs_structural_half_circle_dimension_impl_dim = (1 : ℚ) / (2 : ℚ)

/-- Paper label: `prop:killo-implementation-vs-structural-half-circle-dimension`. -/
theorem paper_killo_implementation_vs_structural_half_circle_dimension :
    killo_implementation_vs_structural_half_circle_dimension_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [killo_implementation_vs_structural_half_circle_dimension_additive_dim,
      halfCircleDim, circleDim]
  · intro k
    exact Omega.Folding.paper_killo_no_finite_additive_register_linearization k
  · intro a b hab
    exact hab
  · norm_num [killo_implementation_vs_structural_half_circle_dimension_impl_dim,
      halfCircleDim, circleDim]

end Omega.CircleDimension
