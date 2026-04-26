import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Base-`2` logarithm written via the natural logarithm. -/
noncomputable def conclusion_window6_visible_bits_collision_drop_log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- The ordinary window-`6` multiplicity list with histogram `(2,4,8,5,2)` on the support
`{1,2,3,4,5}`. -/
def conclusion_window6_visible_bits_collision_drop_ordinary_sizes : List ℕ :=
  [1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5]

/-- The binary-uplift window-`6` multiplicity list with histogram `(8,4,9)` on the support
`{2,3,4}`. -/
def conclusion_window6_visible_bits_collision_drop_binary_sizes : List ℕ :=
  [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4]

/-- Average hidden bits in the ordinary window-`6` model. -/
noncomputable def conclusion_window6_visible_bits_collision_drop_ordinary_hidden_bits : ℝ :=
  (3 / 4 : ℝ) +
    (3 / 8 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 3 +
    (5 / 32 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 5

/-- Average hidden bits in the binary-uplift window-`6` model. -/
noncomputable def conclusion_window6_visible_bits_collision_drop_binary_hidden_bits : ℝ :=
  (11 / 8 : ℝ) +
    (3 / 16 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 3

/-- Corresponding visible bits in the ordinary window-`6` model. -/
noncomputable def conclusion_window6_visible_bits_collision_drop_ordinary_visible_bits : ℝ :=
  6 - conclusion_window6_visible_bits_collision_drop_ordinary_hidden_bits

/-- Corresponding visible bits in the binary-uplift window-`6` model. -/
noncomputable def conclusion_window6_visible_bits_collision_drop_binary_visible_bits : ℝ :=
  6 - conclusion_window6_visible_bits_collision_drop_binary_hidden_bits

/-- Normalized collision fingerprint in the ordinary window-`6` model. -/
def conclusion_window6_visible_bits_collision_drop_ordinary_collision : ℚ :=
  21 * 220 / 4096

/-- Normalized collision fingerprint in the binary-uplift window-`6` model. -/
def conclusion_window6_visible_bits_collision_drop_binary_collision : ℚ :=
  21 * 212 / 4096

/-- The paper-facing arithmetic package for the visible-bit gain and the collision drop. -/
def conclusion_window6_visible_bits_collision_drop_statement : Prop :=
  conclusion_window6_visible_bits_collision_drop_ordinary_sizes.length = 21 ∧
    conclusion_window6_visible_bits_collision_drop_binary_sizes.length = 21 ∧
    conclusion_window6_visible_bits_collision_drop_ordinary_sizes.sum = 64 ∧
    conclusion_window6_visible_bits_collision_drop_binary_sizes.sum = 64 ∧
    conclusion_window6_visible_bits_collision_drop_ordinary_hidden_bits =
      (3 / 4 : ℝ) +
        (3 / 8 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 3 +
        (5 / 32 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 5 ∧
    conclusion_window6_visible_bits_collision_drop_binary_hidden_bits =
      (11 / 8 : ℝ) +
        (3 / 16 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 3 ∧
    conclusion_window6_visible_bits_collision_drop_binary_visible_bits -
        conclusion_window6_visible_bits_collision_drop_ordinary_visible_bits =
      (-5 / 8 : ℝ) +
        (3 / 16 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 3 +
        (5 / 32 : ℝ) * conclusion_window6_visible_bits_collision_drop_log2 5 ∧
    (2 : ℕ) ^ 20 < 3 ^ 6 * 5 ^ 5 ∧
    conclusion_window6_visible_bits_collision_drop_ordinary_collision = 1155 / 1024 ∧
    conclusion_window6_visible_bits_collision_drop_binary_collision = 1113 / 1024 ∧
    conclusion_window6_visible_bits_collision_drop_ordinary_collision -
        conclusion_window6_visible_bits_collision_drop_binary_collision =
      21 / 512

/-- Paper label: `prop:conclusion-window6-visible-bits-collision-drop`. The binary uplift raises
the visible-bit count by the explicit logarithmic amount and lowers the normalized collision
fingerprint from `1155/1024` to `1113/1024`. -/
theorem paper_conclusion_window6_visible_bits_collision_drop :
    conclusion_window6_visible_bits_collision_drop_statement := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, rfl, rfl, ?_,
    by native_decide, ?_, ?_, ?_⟩
  · unfold conclusion_window6_visible_bits_collision_drop_binary_visible_bits
      conclusion_window6_visible_bits_collision_drop_ordinary_visible_bits
      conclusion_window6_visible_bits_collision_drop_binary_hidden_bits
      conclusion_window6_visible_bits_collision_drop_ordinary_hidden_bits
    ring
  · norm_num [conclusion_window6_visible_bits_collision_drop_ordinary_collision]
  · norm_num [conclusion_window6_visible_bits_collision_drop_binary_collision]
  · norm_num [conclusion_window6_visible_bits_collision_drop_ordinary_collision,
      conclusion_window6_visible_bits_collision_drop_binary_collision]

end Omega.Conclusion
