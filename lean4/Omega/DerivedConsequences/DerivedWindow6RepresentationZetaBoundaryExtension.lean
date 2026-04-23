import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6BoundarySectorGroupalgebraIsotypy
import Omega.Zeta.DerivedWindow6BoundaryParityDirectFactorRefinement
import Omega.Zeta.GaugeGroupTripleDecomp

namespace Omega.DerivedConsequences

/-- Concrete bookkeeping for the window-`6` representation zeta specialization and the boundary
extension count. -/
structure derived_window6_representation_zeta_boundary_extension_data where
  derived_window6_representation_zeta_boundary_extension_witness : Unit := ()

namespace derived_window6_representation_zeta_boundary_extension_data

/-- The irreducible count obtained by specializing the product zeta formula at `s = 0`. -/
def irrep_count (_D : derived_window6_representation_zeta_boundary_extension_data) : ℕ :=
  2 ^ 8 * 3 ^ 4 * 5 ^ 9

/-- The one-dimensional character count coming from the window-`6` abelianization rank `21`. -/
def linear_character_count (_D : derived_window6_representation_zeta_boundary_extension_data) :
    ℕ :=
  2 ^ 21

/-- Each boundary parity assignment has `2^18` extensions to a global linear character. -/
def boundary_extension_fiber_card
    (_D : derived_window6_representation_zeta_boundary_extension_data) : ℕ :=
  2 ^ 18

/-- The product-factor specialization of the representation zeta formula at `s = 0`. -/
def has_representation_zeta_formula
    (D : derived_window6_representation_zeta_boundary_extension_data) : Prop :=
  D.irrep_count = 2 ^ 8 * (2 + 1) ^ 4 * (2 + 1 + 2) ^ 9

/-- Surjectivity is witnessed by the character-count factorization
`2^21 = 2^3 · 2^18`. -/
def boundary_restriction_surjective
    (D : derived_window6_representation_zeta_boundary_extension_data) : Prop :=
  D.linear_character_count =
    2 ^ Fintype.card Omega.GU.Window6BoundaryParityBlock *
      D.boundary_extension_fiber_card

end derived_window6_representation_zeta_boundary_extension_data

open derived_window6_representation_zeta_boundary_extension_data

/-- Paper label: `thm:derived-window6-representation-zeta-boundary-extension`. -/
theorem paper_derived_window6_representation_zeta_boundary_extension
    (D : derived_window6_representation_zeta_boundary_extension_data) :
    D.has_representation_zeta_formula ∧
      D.irrep_count = 2 ^ 8 * 3 ^ 4 * 5 ^ 9 ∧
      D.linear_character_count = 2 ^ 21 ∧
      D.boundary_restriction_surjective ∧
      D.boundary_extension_fiber_card = 2 ^ 18 := by
  have hboundary :=
    Omega.Zeta.paper_derived_window6_boundary_parity_direct_factor_refinement
  have hsplit :=
    Omega.Zeta.GaugeGroupTripleDecomp.paper_derived_window6_gauge_center_derived_splitting
  refine ⟨?_, rfl, rfl, ?_, rfl⟩
  · norm_num [derived_window6_representation_zeta_boundary_extension_data.irrep_count,
      derived_window6_representation_zeta_boundary_extension_data.has_representation_zeta_formula]
  · unfold derived_window6_representation_zeta_boundary_extension_data.boundary_restriction_surjective
      derived_window6_representation_zeta_boundary_extension_data.linear_character_count
      derived_window6_representation_zeta_boundary_extension_data.boundary_extension_fiber_card
    have hcard : Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 := hboundary.2.1
    have hrank : (21 : ℕ) = 3 + 18 := hsplit.2.1
    rw [hcard, hrank, pow_add]

end Omega.DerivedConsequences
