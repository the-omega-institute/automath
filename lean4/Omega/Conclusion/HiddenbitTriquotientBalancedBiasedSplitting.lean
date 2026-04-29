import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hiddenbit-triquotient-balanced-biased-splitting`. -/
theorem paper_conclusion_hiddenbit_triquotient_balanced_biased_splitting (k : ℕ)
    (hk : 6 ≤ k) :
    ({(1 / 2 : ℚ),
      (1 / 2 : ℚ) + (Nat.fib (k - 2) : ℚ) / ((2 : ℚ) * Nat.fib (k + 1)),
      (1 / 2 : ℚ) - (Nat.fib (k - 2) : ℚ) / ((2 : ℚ) * Nat.fib (k + 1))} :
      Finset ℚ).card = 3 := by
  let d : ℚ := (Nat.fib (k - 2) : ℚ) / ((2 : ℚ) * Nat.fib (k + 1))
  have hfib_num_pos : 0 < Nat.fib (k - 2) := by
    exact Nat.fib_pos.mpr (by omega)
  have hfib_den_pos : 0 < Nat.fib (k + 1) := by
    exact Nat.fib_pos.mpr (by omega)
  have hnum : (Nat.fib (k - 2) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfib_num_pos
  have hden_fib : (Nat.fib (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfib_den_pos
  have hd : d ≠ 0 := by
    exact div_ne_zero hnum (mul_ne_zero (by norm_num) hden_fib)
  change ({(1 / 2 : ℚ), (1 / 2 : ℚ) + d, (1 / 2 : ℚ) - d} : Finset ℚ).card = 3
  have hplus_ne_half : (1 / 2 : ℚ) + d ≠ 1 / 2 := by
    intro h
    apply hd
    linarith
  have hminus_ne_half : (1 / 2 : ℚ) - d ≠ 1 / 2 := by
    intro h
    apply hd
    linarith
  have hminus_ne_plus : (1 / 2 : ℚ) - d ≠ (1 / 2 : ℚ) + d := by
    intro h
    apply hd
    linarith
  have hhalf_ne_plus : (1 / 2 : ℚ) ≠ (1 / 2 : ℚ) + d := by
    exact fun h => hplus_ne_half h.symm
  have hhalf_ne_minus : (1 / 2 : ℚ) ≠ (1 / 2 : ℚ) - d := by
    exact fun h => hminus_ne_half h.symm
  have hplus_ne_minus : (1 / 2 : ℚ) + d ≠ (1 / 2 : ℚ) - d := by
    exact fun h => hminus_ne_plus h.symm
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simpa [Finset.mem_singleton] using hplus_ne_minus
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact hhalf_ne_plus h
    · exact hhalf_ne_minus h

end Omega.Conclusion
