import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped BigOperators

noncomputable section

/-- Concrete data for a quadratic eigenvalue pencil after simultaneous modal diagonalization. -/
structure xi_qep_commuting_modal_factorization_data where
  Mode : Type
  instFintypeMode : Fintype Mode
  instDecidableEqMode : DecidableEq Mode
  mass : Matrix Mode Mode ℂ
  damping : Matrix Mode Mode ℂ
  stiffness : Matrix Mode Mode ℂ
  leftModal : Matrix Mode Mode ℂ
  rightModal : Matrix Mode Mode ℂ
  modalMass : Mode → ℂ
  modalDamping : Mode → ℂ
  modalStiffness : Mode → ℂ
  conjugated_pencil :
    ∀ z : ℂ,
      leftModal * (z ^ 2 • mass + z • damping + stiffness) * rightModal =
        diagonal
          (fun j : Mode => z ^ 2 * modalMass j + z * modalDamping j + modalStiffness j)

attribute [instance] xi_qep_commuting_modal_factorization_data.instFintypeMode
attribute [instance] xi_qep_commuting_modal_factorization_data.instDecidableEqMode

/-- The modal factor attached to one simultaneously diagonalized mode. -/
def xi_qep_commuting_modal_factorization_mode_factor
    (D : xi_qep_commuting_modal_factorization_data) (z : ℂ) (j : D.Mode) : ℂ :=
  z ^ 2 * D.modalMass j + z * D.modalDamping j + D.modalStiffness j

/-- The determinant product formula for the conjugated quadratic pencil. -/
def xi_qep_commuting_modal_factorization_statement
    (D : xi_qep_commuting_modal_factorization_data) : Prop :=
  ∀ z : ℂ,
    Matrix.det (D.leftModal * (z ^ 2 • D.mass + z • D.damping + D.stiffness) * D.rightModal) =
      ∏ j : D.Mode, xi_qep_commuting_modal_factorization_mode_factor D z j

/-- Paper label: `prop:xi-qep-commuting-modal-factorization`. -/
theorem paper_xi_qep_commuting_modal_factorization
    (D : xi_qep_commuting_modal_factorization_data) :
    xi_qep_commuting_modal_factorization_statement D := by
  intro z
  rw [D.conjugated_pencil z, Matrix.det_diagonal]
  rfl

end

end Omega.Zeta
