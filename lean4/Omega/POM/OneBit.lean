import Omega.Folding.VisibleValueOverflow

namespace Omega.POM

/-- Single hidden-bit decomposition of a word into its stable folded value and one overflow bit.
    lem:pom-one-bit -/
theorem paper_pom_one_bit (w : Omega.Word m) :
    ∃! b : Fin 2,
      Omega.weight w = Omega.stableValue (Omega.Fold w) + b.1 * Nat.fib (m + 2) := by
  refine ⟨⟨Omega.hiddenBit w, by
    have hbit := Omega.hiddenBit_le_one w
    omega⟩, ?_, ?_⟩
  · simpa using Omega.weight_eq_stableValue_add_hiddenBit w
  · intro b hb
    have hbit : Omega.hiddenBit w ≤ 1 := Omega.hiddenBit_le_one w
    have hFibPos : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
    have hmain := Omega.weight_eq_stableValue_add_hiddenBit w
    have hmul : Omega.hiddenBit w * Nat.fib (m + 2) = b.1 * Nat.fib (m + 2) := by
      omega
    have hval : b.1 = Omega.hiddenBit w := (Nat.eq_of_mul_eq_mul_right hFibPos hmul).symm
    exact Fin.ext hval

end Omega.POM
