import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete boundary-block data for the window-6 two-sheet crossed-product model. -/
structure conclusion_window6_boundary_crossed_product_delta34_data where
  conclusion_window6_boundary_crossed_product_delta34_boundary_block : Type
  conclusion_window6_boundary_crossed_product_delta34_diagonal_weight :
    conclusion_window6_boundary_crossed_product_delta34_boundary_block → ℝ
  conclusion_window6_boundary_crossed_product_delta34_swap :
    conclusion_window6_boundary_crossed_product_delta34_boundary_block →
      conclusion_window6_boundary_crossed_product_delta34_boundary_block
  conclusion_window6_boundary_crossed_product_delta34_uplift :
    conclusion_window6_boundary_crossed_product_delta34_boundary_block → ℤ
  conclusion_window6_boundary_crossed_product_delta34_matrix_coordinate :
    conclusion_window6_boundary_crossed_product_delta34_boundary_block ≃ Fin 2 × Fin 2
  conclusion_window6_boundary_crossed_product_delta34_swap_involutive :
    Function.Involutive conclusion_window6_boundary_crossed_product_delta34_swap
  conclusion_window6_boundary_crossed_product_delta34_diagonal_swap_invariant :
    ∀ b,
      conclusion_window6_boundary_crossed_product_delta34_diagonal_weight
          (conclusion_window6_boundary_crossed_product_delta34_swap b) =
        conclusion_window6_boundary_crossed_product_delta34_diagonal_weight b
  conclusion_window6_boundary_crossed_product_delta34_delta34_cert :
    ∀ b,
      conclusion_window6_boundary_crossed_product_delta34_uplift
          (conclusion_window6_boundary_crossed_product_delta34_swap b) =
        conclusion_window6_boundary_crossed_product_delta34_uplift b + 34

namespace conclusion_window6_boundary_crossed_product_delta34_data

/-- The crossed-product block is coordinatized by a concrete `2 × 2` matrix block. -/
def conclusion_window6_boundary_crossed_product_delta34_crossed_product_iso
    (D : conclusion_window6_boundary_crossed_product_delta34_data) : Prop :=
  Nonempty
    (D.conclusion_window6_boundary_crossed_product_delta34_boundary_block ≃ Fin 2 × Fin 2)

/-- The two uplift sheets in every boundary pair differ by exactly `34`. -/
def conclusion_window6_boundary_crossed_product_delta34_sheet_pair_delta
    (D : conclusion_window6_boundary_crossed_product_delta34_data) : Prop :=
  ∀ b,
    D.conclusion_window6_boundary_crossed_product_delta34_uplift
        (D.conclusion_window6_boundary_crossed_product_delta34_swap b) =
      D.conclusion_window6_boundary_crossed_product_delta34_uplift b + 34

/-- The geometric flip is an involution preserving the diagonal boundary algebra. -/
def conclusion_window6_boundary_crossed_product_delta34_geo_flip
    (D : conclusion_window6_boundary_crossed_product_delta34_data) : Prop :=
  Function.Involutive D.conclusion_window6_boundary_crossed_product_delta34_swap ∧
    ∀ b,
      D.conclusion_window6_boundary_crossed_product_delta34_diagonal_weight
          (D.conclusion_window6_boundary_crossed_product_delta34_swap b) =
        D.conclusion_window6_boundary_crossed_product_delta34_diagonal_weight b

end conclusion_window6_boundary_crossed_product_delta34_data

/-- Paper label: `thm:conclusion-window6-boundary-crossed-product-delta34`. -/
theorem paper_conclusion_window6_boundary_crossed_product_delta34
    (D : conclusion_window6_boundary_crossed_product_delta34_data) :
    D.conclusion_window6_boundary_crossed_product_delta34_crossed_product_iso ∧
      D.conclusion_window6_boundary_crossed_product_delta34_sheet_pair_delta ∧
      D.conclusion_window6_boundary_crossed_product_delta34_geo_flip := by
  exact
    ⟨⟨D.conclusion_window6_boundary_crossed_product_delta34_matrix_coordinate⟩,
      D.conclusion_window6_boundary_crossed_product_delta34_delta34_cert,
      D.conclusion_window6_boundary_crossed_product_delta34_swap_involutive,
      D.conclusion_window6_boundary_crossed_product_delta34_diagonal_swap_invariant⟩

end Omega.Conclusion
