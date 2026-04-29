import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Omega.Zeta.XiTimePart55dWindow6MicrostateHilbertGaugeSplitting

namespace Omega.Zeta

/-- The visible full-matrix block in the window-`6` commutant. -/
abbrev xi_time_part55d_window6_action_image_commutant_rigidity_visible_matrix_sector :=
  Fin 21 × Fin 21

/-- The hidden multiplicity-one scalar blocks coming from the `Std₄`, `Std₃`, and `sgn₂`
packets. -/
abbrev xi_time_part55d_window6_action_image_commutant_rigidity_hidden_scalar_sector :=
  Fin 27 ⊕ (Fin 8 ⊕ Fin 8)

/-- Concrete block data for the window-`6` action-image commutant. -/
structure xi_time_part55d_window6_action_image_commutant_rigidity_data where
  commutantIndex : Type
  commutantFintype : Fintype commutantIndex
  blockDecomposition :
    commutantIndex ≃
      (xi_time_part55d_window6_action_image_commutant_rigidity_visible_matrix_sector ⊕
        xi_time_part55d_window6_action_image_commutant_rigidity_hidden_scalar_sector)
  visibleBlock : Matrix (Fin 21) (Fin 21) ℝ
  visibleHiddenBlock :
    Matrix (Fin 21) xi_time_part55d_window6_action_image_commutant_rigidity_hidden_scalar_sector ℝ
  hiddenVisibleBlock :
    Matrix xi_time_part55d_window6_action_image_commutant_rigidity_hidden_scalar_sector
      (Fin 21) ℝ
  visibleBlock_selfAdjoint : visibleBlock.transpose = visibleBlock
  visibleHiddenBlock_zero : visibleHiddenBlock = 0
  hiddenVisibleBlock_zero : hiddenVisibleBlock = 0

namespace xi_time_part55d_window6_action_image_commutant_rigidity_data

/-- Paper-facing rigidity package: the Hilbert splitting has dimensions `21 + 27 + 8 + 8 = 64`,
the commutant is the visible full matrix block plus `43` scalar hidden blocks, and the
hidden-visible off-diagonal blocks vanish. -/
def statement (h : xi_time_part55d_window6_action_image_commutant_rigidity_data) : Prop :=
  xi_time_part55d_window6_microstate_hilbert_gauge_splitting_statement ∧
    let _ := h.commutantFintype
    Nonempty
        (h.commutantIndex ≃
          (xi_time_part55d_window6_action_image_commutant_rigidity_visible_matrix_sector ⊕
            xi_time_part55d_window6_action_image_commutant_rigidity_hidden_scalar_sector)) ∧
      Fintype.card xi_time_part55d_window6_action_image_commutant_rigidity_hidden_scalar_sector =
        43 ∧
      Fintype.card h.commutantIndex = 21 ^ 2 + 43 ∧
      h.visibleBlock.transpose = h.visibleBlock ∧
      h.visibleHiddenBlock = 0 ∧
      h.hiddenVisibleBlock = 0

end xi_time_part55d_window6_action_image_commutant_rigidity_data

open xi_time_part55d_window6_action_image_commutant_rigidity_data

/-- Paper label: `thm:xi-time-part55d-window6-action-image-commutant-rigidity`. -/
theorem paper_xi_time_part55d_window6_action_image_commutant_rigidity
    (h : xi_time_part55d_window6_action_image_commutant_rigidity_data) : h.statement := by
  dsimp [xi_time_part55d_window6_action_image_commutant_rigidity_data.statement]
  let _ := h.commutantFintype
  refine ⟨paper_xi_time_part55d_window6_microstate_hilbert_gauge_splitting, ⟨h.blockDecomposition⟩,
    ?_, ?_, h.visibleBlock_selfAdjoint, h.visibleHiddenBlock_zero, h.hiddenVisibleBlock_zero⟩
  · native_decide
  · simpa [pow_two,
      xi_time_part55d_window6_action_image_commutant_rigidity_visible_matrix_sector,
      xi_time_part55d_window6_action_image_commutant_rigidity_hidden_scalar_sector] using
      Fintype.card_congr h.blockDecomposition

end Omega.Zeta
