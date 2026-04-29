import Mathlib.Data.Fintype.Card

namespace Omega.Zeta

/-- Concrete block data for the boundary two-sheet commutant: the four scalar block choices are
indexed by an explicitly four-element type. -/
structure xi_window6_boundary_two_sheet_commutant_fourdimensional_data where
  commutantIndex : Type
  commutantFintype : Fintype commutantIndex
  fourBlockDecomposition : commutantIndex ≃ Fin 4

namespace xi_window6_boundary_two_sheet_commutant_fourdimensional_data

/-- Finite dimension of the scalar block-choice commutant. -/
def commutantDimension
    (D : xi_window6_boundary_two_sheet_commutant_fourdimensional_data) : ℕ :=
  let _ := D.commutantFintype
  Fintype.card D.commutantIndex

end xi_window6_boundary_two_sheet_commutant_fourdimensional_data

/-- Paper label: `cor:xi-window6-boundary-two-sheet-commutant-fourdimensional`. -/
theorem paper_xi_window6_boundary_two_sheet_commutant_fourdimensional
    (D : xi_window6_boundary_two_sheet_commutant_fourdimensional_data) :
    D.commutantDimension = 4 := by
  let _ := D.commutantFintype
  unfold xi_window6_boundary_two_sheet_commutant_fourdimensional_data.commutantDimension
  calc
    Fintype.card D.commutantIndex = Fintype.card (Fin 4) :=
      Fintype.card_congr D.fourBlockDecomposition
    _ = 4 := by rfl

end Omega.Zeta
