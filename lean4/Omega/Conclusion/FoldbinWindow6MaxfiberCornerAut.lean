import Mathlib.Tactic

namespace Omega.Conclusion

/-- The number of simple matrix blocks in the `m = 6` max-fiber corner. -/
def conclusion_foldbin_window6_maxfiber_corner_aut_blockCount : ℕ :=
  9

/-- The matrix size in each max-fiber corner block. -/
def conclusion_foldbin_window6_maxfiber_corner_aut_matrixSize : ℕ :=
  4

/-- The Lie dimension contributed by the product of projective block automorphism groups. -/
def conclusion_foldbin_window6_maxfiber_corner_aut_projectiveAutDimension : ℕ :=
  conclusion_foldbin_window6_maxfiber_corner_aut_blockCount *
    (conclusion_foldbin_window6_maxfiber_corner_aut_matrixSize ^ 2 - 1)

/-- The diagonal invariant-field rank contributed by the nine `M₄(ℂ)` blocks. -/
def conclusion_foldbin_window6_maxfiber_corner_aut_invariantFieldRank : ℕ :=
  conclusion_foldbin_window6_maxfiber_corner_aut_blockCount *
    (conclusion_foldbin_window6_maxfiber_corner_aut_matrixSize - 1)

/-- Concrete package for the `m = 6` max-fiber corner decomposition `M₄(ℂ)^9`.

The automorphism and invariant-field counts reduce to the block-product identities
`9 * (4^2 - 1) = 135` and `9 * (4 - 1) = 27`. -/
def conclusion_foldbin_window6_maxfiber_corner_aut_package : Prop :=
  conclusion_foldbin_window6_maxfiber_corner_aut_blockCount = 9 ∧
    conclusion_foldbin_window6_maxfiber_corner_aut_matrixSize = 4 ∧
    conclusion_foldbin_window6_maxfiber_corner_aut_projectiveAutDimension =
      9 * (4 ^ 2 - 1) ∧
    conclusion_foldbin_window6_maxfiber_corner_aut_projectiveAutDimension = 135 ∧
    conclusion_foldbin_window6_maxfiber_corner_aut_invariantFieldRank = 9 * (4 - 1) ∧
    conclusion_foldbin_window6_maxfiber_corner_aut_invariantFieldRank = 27

/-- Paper label: `thm:conclusion-foldbin-window6-maxfiber-corner-aut`. -/
theorem paper_conclusion_foldbin_window6_maxfiber_corner_aut :
    conclusion_foldbin_window6_maxfiber_corner_aut_package := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · native_decide
  · rfl
  · native_decide

end Omega.Conclusion
