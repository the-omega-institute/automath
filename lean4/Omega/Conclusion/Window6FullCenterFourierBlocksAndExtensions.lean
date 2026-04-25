import Mathlib.Tactic

namespace Omega.Conclusion

/-- Dimension of the abelianization character space in the window-`6` model. -/
def conclusion_window6_full_center_fourier_blocks_and_extensions_abelianization_dim : ℕ :=
  21

/-- Dimension of the full center character space in the window-`6` model. -/
def conclusion_window6_full_center_fourier_blocks_and_extensions_center_dim : ℕ :=
  8

/-- Dimension of the boundary center character space in the window-`6` model. -/
def conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_dim : ℕ :=
  3

/-- The number of one-dimensional extensions of a full center character. -/
def conclusion_window6_full_center_fourier_blocks_and_extensions_full_center_extension_count :
    ℕ :=
  2 ^
    (conclusion_window6_full_center_fourier_blocks_and_extensions_abelianization_dim -
      conclusion_window6_full_center_fourier_blocks_and_extensions_center_dim)

/-- The number of one-dimensional extensions of a boundary center character. -/
def conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_extension_count :
    ℕ :=
  2 ^
    (conclusion_window6_full_center_fourier_blocks_and_extensions_abelianization_dim -
      conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_dim)

/-- Concrete finite-vector-space core for the window-`6` Fourier block calculation. -/
def conclusion_window6_full_center_fourier_blocks_and_extensions_has_center_fourier_decomposition :
    Prop :=
  2 ^ conclusion_window6_full_center_fourier_blocks_and_extensions_center_dim *
      conclusion_window6_full_center_fourier_blocks_and_extensions_full_center_extension_count =
        2 ^
          conclusion_window6_full_center_fourier_blocks_and_extensions_abelianization_dim ∧
    2 ^ conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_dim *
        conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_extension_count =
          2 ^
            conclusion_window6_full_center_fourier_blocks_and_extensions_abelianization_dim

/-- Paper label:
`thm:conclusion-window6-full-center-fourier-blocks-and-extensions`.

The window-`6` character projections have kernel dimensions `21 - 8 = 13` and
`21 - 3 = 18`, giving the advertised extension counts. -/
theorem paper_conclusion_window6_full_center_fourier_blocks_and_extensions :
    conclusion_window6_full_center_fourier_blocks_and_extensions_has_center_fourier_decomposition ∧
      conclusion_window6_full_center_fourier_blocks_and_extensions_full_center_extension_count =
        2 ^ 13 ∧
      conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_extension_count =
        2 ^ 18 := by
  unfold conclusion_window6_full_center_fourier_blocks_and_extensions_has_center_fourier_decomposition
  unfold conclusion_window6_full_center_fourier_blocks_and_extensions_full_center_extension_count
  unfold conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_extension_count
  unfold conclusion_window6_full_center_fourier_blocks_and_extensions_abelianization_dim
  unfold conclusion_window6_full_center_fourier_blocks_and_extensions_center_dim
  unfold conclusion_window6_full_center_fourier_blocks_and_extensions_boundary_dim
  norm_num

end Omega.Conclusion
