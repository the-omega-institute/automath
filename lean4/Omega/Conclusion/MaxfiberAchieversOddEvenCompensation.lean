import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Conclusion-facing synthesis of the odd-window vanishing statement with the even-window
two-phase hidden-bit split. The two complementary achievers average to exactly `1/2` in each
hidden-bit coordinate after normalizing by `2 F_{k+2}`.
    thm:conclusion-maxfiber-achievers-odd-even-compensation -/
theorem paper_conclusion_maxfiber_achievers_odd_even_compensation (k : Nat) {alpha beta : Type*}
    (sOdd : alpha -> Int) (Modd : Finset alpha) (x1 x2 : beta) (d0 d1 : beta -> Nat)
    (hOdd : forall x, x ∈ Modd -> sOdd x = 0)
    (hEven1 : d0 x1 = Nat.fib (k + 1) ∧ d1 x1 = Nat.fib k)
    (hEven2 : d0 x2 = Nat.fib k ∧ d1 x2 = Nat.fib (k + 1))
    (hFib : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k) :
    (forall x, x ∈ Modd -> sOdd x = 0) ∧
      (((d0 x1 + d0 x2 : Rat) / (2 * Nat.fib (k + 2)) = (1 : Rat) / 2)) ∧
      (((d1 x1 + d1 x2 : Rat) / (2 * Nat.fib (k + 2)) = (1 : Rat) / 2)) := by
  rcases hEven1 with ⟨h01, h11⟩
  rcases hEven2 with ⟨h02, h12⟩
  refine ⟨hOdd, ?_, ?_⟩
  · rw [h01, h02, hFib]
    have hsum_nat : 0 < Nat.fib (k + 1) + Nat.fib k := by
      have hfib_pos : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (Nat.succ_pos k)
      omega
    have hsum_ne : ((Nat.fib (k + 1) + Nat.fib k : Nat) : Rat) ≠ 0 := by
      have hsum_pos : (0 : Rat) < ((Nat.fib (k + 1) + Nat.fib k : Nat) : Rat) := by
        exact_mod_cast hsum_nat
      linarith
    have hcast :
        ((Nat.fib (k + 1) + Nat.fib k : Nat) : Rat) =
          (Nat.fib (k + 1) : Rat) + Nat.fib k := by
      norm_num
    rw [← hcast]
    field_simp [hsum_ne]
  · rw [h11, h12, hFib]
    have hsum_nat : 0 < Nat.fib (k + 1) + Nat.fib k := by
      have hfib_pos : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (Nat.succ_pos k)
      omega
    have hsum_ne : ((Nat.fib (k + 1) + Nat.fib k : Nat) : Rat) ≠ 0 := by
      have hsum_pos : (0 : Rat) < ((Nat.fib (k + 1) + Nat.fib k : Nat) : Rat) := by
        exact_mod_cast hsum_nat
      linarith
    have hcast :
        ((Nat.fib (k + 1) + Nat.fib k : Nat) : Rat) =
          (Nat.fib (k + 1) : Rat) + Nat.fib k := by
      norm_num
    rw [add_comm, ← hcast]
    field_simp [hsum_ne]

end Omega.Conclusion
