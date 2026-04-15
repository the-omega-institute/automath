import Omega.Folding.FiberArithmetic
import Omega.Folding.MaxFiberTwoStep

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Resolution-folding publication wrapper for the unique overflow decomposition.
    cor:visible-value-overflow -/
theorem paper_resolution_folding_visible_value_overflow
    (m : ℕ) (_hm : 1 ≤ m) (w : Omega.Word m) :
    (∃! b : Fin 2,
      Omega.weight w =
        Omega.stableValue (Omega.Fold w) + b.1 * Nat.fib (m + 2)) ∧
      ∃! x : Omega.X m, Omega.weight w % Nat.fib (m + 2) = Omega.stableValue x := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨Omega.hiddenBit w, by
      have hbit := Omega.hiddenBit_le_one w
      omega⟩, ?_, ?_⟩
    · simpa using Omega.weight_eq_stableValue_add_hiddenBit w
    · intro b hb
      have hbit : Omega.hiddenBit w ≤ 1 := Omega.hiddenBit_le_one w
      have hb' : b.1 ≤ 1 := by omega
      have hFibPos : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
      have hmain := Omega.weight_eq_stableValue_add_hiddenBit w
      have hmul : Omega.hiddenBit w * Nat.fib (m + 2) = b.1 * Nat.fib (m + 2) := by omega
      have hval : b.1 = Omega.hiddenBit w := (Nat.eq_of_mul_eq_mul_right hFibPos hmul).symm
      apply Fin.ext
      exact hval
  · refine ⟨Omega.Fold w, ?_, ?_⟩
    · exact (Omega.stableValue_Fold_mod w).symm
    · intro x hx
      apply _root_.Omega.X.eq_of_stableValue_eq
      rw [Omega.stableValue_Fold_mod w]
      exact hx.symm

end Omega.Folding
