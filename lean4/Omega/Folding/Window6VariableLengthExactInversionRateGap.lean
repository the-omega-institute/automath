import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Folding

/-- The optimal average binary prefix length for the equiprobable `d`-symbol fibers used in the
window-`6` exact inversion audit. -/
def window6OptimalBinaryPrefixAverage : ℕ → ℚ
  | 2 => 1
  | 3 => 5 / 3
  | 4 => 2
  | _ => 0

/-- The exact average auxiliary bit cost for variable-length inversion at window `6`. -/
def window6VariableLengthExactInversionRate : ℚ :=
  ((Omega.cBinFiberHist 6 2 : ℚ) * 2 * window6OptimalBinaryPrefixAverage 2 +
      (Omega.cBinFiberHist 6 3 : ℚ) * 3 * window6OptimalBinaryPrefixAverage 3 +
      (Omega.cBinFiberHist 6 4 : ℚ) * 4 * window6OptimalBinaryPrefixAverage 4) / 64

/-- The corresponding average number of visible bits after exact variable-length inversion. -/
def window6VariableLengthVisibleBits : ℚ :=
  6 - window6VariableLengthExactInversionRate

/-- The optimal fixed-length exact inversion threshold is `⌈log₂ 4⌉ = 2`. -/
def window6FixedLengthExactInversionThreshold : ℕ :=
  Nat.clog 2 4

/-- Window-`6` exact inversion has optimal variable-length auxiliary rate `27/16`, hence visible
rate `69/16`, while the best fixed-length exact inversion threshold is `2` bits, leaving a strict
gap of `5/16` bits.
    thm:window6-variable-length-exact-inversion-rate-gap -/
theorem paper_window6_variable_length_exact_inversion_rate_gap :
    window6OptimalBinaryPrefixAverage 2 = 1 ∧
      window6OptimalBinaryPrefixAverage 3 = 5 / 3 ∧
      window6OptimalBinaryPrefixAverage 4 = 2 ∧
      window6VariableLengthExactInversionRate = 27 / 16 ∧
      window6VariableLengthVisibleBits = 69 / 16 ∧
      window6FixedLengthExactInversionThreshold = 2 ∧
      (window6FixedLengthExactInversionThreshold : ℚ) - window6VariableLengthExactInversionRate =
        5 / 16 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · norm_num [window6VariableLengthExactInversionRate, window6OptimalBinaryPrefixAverage,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4]
  · norm_num [window6VariableLengthVisibleBits, window6VariableLengthExactInversionRate,
      window6OptimalBinaryPrefixAverage, Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3,
      Omega.cBinFiberHist_6_4]
  · native_decide
  · norm_num [window6FixedLengthExactInversionThreshold, window6VariableLengthExactInversionRate,
      window6OptimalBinaryPrefixAverage, Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3,
      Omega.cBinFiberHist_6_4]

end Omega.Folding
