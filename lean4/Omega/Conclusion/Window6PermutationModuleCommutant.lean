import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite data for the window-`6` permutation-module commutant: a commutant indexing type
with an explicit decomposition into the visible `M_21` matrix sector and the `21` scalar standard
blocks. -/
structure conclusion_window6_permutation_module_commutant_data where
  commutantIndex : Type
  commutantFintype : Fintype commutantIndex
  commutantBlockEquiv : commutantIndex ≃ ((Fin 21 × Fin 21) ⊕ Fin 21)

namespace conclusion_window6_permutation_module_commutant_data

/-- The visible full matrix sector has `21 × 21` matrix units. -/
abbrev conclusion_window6_permutation_module_commutant_visible_matrix_sector :=
  Fin 21 × Fin 21

/-- The hidden standard-block scalar sector has one scalar for each of the `21` blocks. -/
abbrev conclusion_window6_permutation_module_commutant_standard_scalar_sector :=
  Fin 21

/-- The commutant is indexed by the direct sum of the visible matrix units and the scalar standard
blocks. -/
def commutant_iso (D : conclusion_window6_permutation_module_commutant_data) : Prop :=
  let _ := D.commutantFintype
  Nonempty
    (D.commutantIndex ≃
      (conclusion_window6_permutation_module_commutant_visible_matrix_sector ⊕
        conclusion_window6_permutation_module_commutant_standard_scalar_sector))

/-- Finite dimension of the commutant indexing type. -/
def commutant_dimension (D : conclusion_window6_permutation_module_commutant_data) : ℕ :=
  let _ := D.commutantFintype
  Fintype.card D.commutantIndex

end conclusion_window6_permutation_module_commutant_data

open conclusion_window6_permutation_module_commutant_data

/-- Paper label: `thm:conclusion-window6-permutation-module-commutant`. -/
theorem paper_conclusion_window6_permutation_module_commutant
    (D : conclusion_window6_permutation_module_commutant_data) :
    D.commutant_iso ∧ D.commutant_dimension = 462 := by
  let _ := D.commutantFintype
  refine ⟨⟨D.commutantBlockEquiv⟩, ?_⟩
  unfold commutant_dimension
  calc
    Fintype.card D.commutantIndex =
        Fintype.card ((Fin 21 × Fin 21) ⊕ Fin 21) :=
      Fintype.card_congr D.commutantBlockEquiv
    _ = 462 := by norm_num

end Omega.Conclusion
