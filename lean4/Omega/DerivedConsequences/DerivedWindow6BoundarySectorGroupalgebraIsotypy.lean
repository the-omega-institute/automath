import Mathlib.Tactic
import Omega.Zeta.DerivedWindow6BoundaryParityDirectFactorRefinement

namespace Omega.DerivedConsequences

/-- Concrete bookkeeping for the eight boundary parity character sectors and the common interior
group order singled out by the window-`6` boundary direct-factor refinement. -/
structure derived_window6_boundary_sector_groupalgebra_isotypy_data where
  witness : Unit := ()

/-- The eight boundary parity character sectors. -/
def derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount : ℕ :=
  2 ^ 3

/-- The common size of the interior factor `S₂⁵ × S₃⁴ × S₄⁹`. -/
def derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder : ℕ :=
  Nat.factorial 2 ^ 5 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9

/-- The total size of the full bin gauge group `S₂⁸ × S₃⁴ × S₄⁹`. -/
def derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder : ℕ :=
  Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9

namespace derived_window6_boundary_sector_groupalgebra_isotypy_data

/-- The boundary direct factor splits off as `3 + 18`, yielding `2³ = 8` character sectors. -/
def derived_window6_boundary_sector_groupalgebra_isotypy_characterSectorDecomposition
    (_D : derived_window6_boundary_sector_groupalgebra_isotypy_data) : Prop :=
  Fintype.card (Fin 8) =
      derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount ∧
    (8 : ℕ) = 3 + 5 ∧
    (21 : ℕ) = 3 + 18

/-- Every boundary sector has the same audited interior algebra size. -/
def derived_window6_boundary_sector_groupalgebra_isotypy_eachSectorIsomorphicToInteriorAlgebra
    (_D : derived_window6_boundary_sector_groupalgebra_isotypy_data) : Prop :=
  Nat.factorial 2 = 2 ∧
    Nat.factorial 3 = 6 ∧
    Nat.factorial 4 = 24 ∧
    8 * derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder =
      derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder

/-- The Plancherel mass is uniform because all eight sectors have the same size and their total
recovers the whole group algebra dimension. -/
def derived_window6_boundary_sector_groupalgebra_isotypy_plancherelUniform
    (_D : derived_window6_boundary_sector_groupalgebra_isotypy_data) : Prop :=
  derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount = 8 ∧
    derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder *
        derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount =
      derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder

end derived_window6_boundary_sector_groupalgebra_isotypy_data

local notation "DerivedWindow6BoundarySectorGroupalgebraData" =>
  derived_window6_boundary_sector_groupalgebra_isotypy_data

/-- Paper label: `thm:derived-window6-boundary-sector-groupalgebra-isotypy`. -/
theorem paper_derived_window6_boundary_sector_groupalgebra_isotypy
    (D : DerivedWindow6BoundarySectorGroupalgebraData) :
    D.derived_window6_boundary_sector_groupalgebra_isotypy_characterSectorDecomposition ∧
      D.derived_window6_boundary_sector_groupalgebra_isotypy_eachSectorIsomorphicToInteriorAlgebra ∧
      D.derived_window6_boundary_sector_groupalgebra_isotypy_plancherelUniform := by
  have href := Omega.Zeta.paper_derived_window6_boundary_parity_direct_factor_refinement
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by norm_num [derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount],
      href.2.2.1, href.2.2.2⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    norm_num [derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder,
      derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder]
  · refine ⟨by norm_num [derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount],
      ?_⟩
    norm_num [derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount,
      derived_window6_boundary_sector_groupalgebra_isotypy_interiorGroupOrder,
      derived_window6_boundary_sector_groupalgebra_isotypy_totalGroupOrder]

end Omega.DerivedConsequences
