import Omega.Folding.NormalizationComplexity

namespace Omega.Folding

/-- Stable addition and multiplication reuse the fold normalization audit bounds; the value-layer
arithmetic contributes at most a quadratic bit budget controlled by the encoded-value length.
    prop:stable-arith-complexity -/
theorem paper_stable_arith_complexity (m : ℕ) :
    foldResolutionCost m ≤ 2 * m + 2 ∧
      foldBitCost m ≤ 2 * (m + 2) * (m + 3) ∧
      foldEncodedValueBitLength m ^ 2 + foldBitCost m ≤
        (m + 3) ^ 2 + 2 * (m + 2) * (m + 3) := by
  rcases paper_fold_complexity m with ⟨hLogBound, _, _, hResolution, _, _, hBit⟩
  have hBitLength : foldEncodedValueBitLength m ≤ m + 3 := by
    unfold foldEncodedValueBitLength
    omega
  have hBitLengthSq : foldEncodedValueBitLength m ^ 2 ≤ (m + 3) ^ 2 := by
    calc
      foldEncodedValueBitLength m ^ 2
          = foldEncodedValueBitLength m * foldEncodedValueBitLength m := by simp [pow_two]
      _ ≤ foldEncodedValueBitLength m * (m + 3) := Nat.mul_le_mul_left _ hBitLength
      _ ≤ (m + 3) * (m + 3) := Nat.mul_le_mul_right _ hBitLength
      _ = (m + 3) ^ 2 := by simp [pow_two]
  exact ⟨hResolution, hBit, Nat.add_le_add hBitLengthSq hBit⟩

end Omega.Folding
