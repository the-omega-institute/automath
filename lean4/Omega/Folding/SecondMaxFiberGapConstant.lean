import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.FiberSpectrum
import Omega.Folding.MaxFiberHigh

namespace Omega

private theorem fib_add_five_eq_three_mul_add_five_mul (n : Nat) :
    Nat.fib (n + 5) = 3 * Nat.fib n + 5 * Nat.fib (n + 1) := by
  have h2 := Nat.fib_add_two (n := n)
  have h3 := Nat.fib_add_two (n := n + 1)
  have h4 := Nat.fib_add_two (n := n + 2)
  have h5 := Nat.fib_add_two (n := n + 3)
  rw [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at h3
  rw [show n + 2 + 2 = n + 4 by omega, show n + 2 + 1 = n + 3 by omega] at h4
  rw [show n + 3 + 2 = n + 5 by omega, show n + 3 + 1 = n + 4 by omega] at h5
  omega

private theorem fib_add_five_le_thirteen_mul (n : Nat) (hn : 1 ≤ n) :
    Nat.fib (n + 5) ≤ 13 * Nat.fib n := by
  rw [fib_add_five_eq_three_mul_add_five_mul]
  have hsucc : Nat.fib (n + 1) ≤ 2 * Nat.fib n := fib_succ_le_double n hn
  have hmul : 5 * Nat.fib (n + 1) ≤ 5 * (2 * Nat.fib n) := Nat.mul_le_mul_left 5 hsucc
  omega

set_option maxHeartbeats 400000 in
/-- Paper-facing global gap certificate: the second-largest distinct fiber multiplicity is always at
most `25/26` of the largest one, and the constant is sharp at `m = 13`.
    cor:pom-second-max-gap-constant -/
theorem paper_pom_second_max_gap_constant
    (two_step : ∀ m, 6 ≤ m →
      Omega.X.maxFiberMultiplicity m =
        Omega.X.maxFiberMultiplicity (m - 2) + Omega.X.maxFiberMultiplicity (m - 4))
    (forbidden_even : ∀ k : Nat, 5 ≤ k →
      cNthMaxFiber (2 * k) 1 =
        Omega.X.maxFiberMultiplicity (2 * k) - Nat.fib (k - 4))
    (forbidden_odd : ∀ k : Nat, 5 ≤ k →
      cNthMaxFiber (2 * k + 1) 1 =
        Omega.X.maxFiberMultiplicity (2 * k + 1) - Nat.fib (k - 4)) :
    (∀ m : Nat, 2 ≤ m → 26 * cNthMaxFiber m 1 ≤ 25 * Omega.X.maxFiberMultiplicity m) ∧
      26 * cNthMaxFiber 13 1 = 25 * Omega.X.maxFiberMultiplicity 13 := by
  rcases Omega.paper_pom_second_max_fiber_closed_form two_step forbidden_even forbidden_odd with
    ⟨h8, h9, h10, heven, hodd⟩
  refine ⟨?_, ?_⟩
  · intro m hm
    by_cases hsmall : m ≤ 10
    · interval_cases m
      · have h2 : cNthMaxFiber 2 1 = 1 := by native_decide
        rw [h2, Omega.X.maxFiberMultiplicity_two]
        omega
      · have h3 : cNthMaxFiber 3 1 = 1 := by native_decide
        rw [h3, Omega.X.maxFiberMultiplicity_three]
        omega
      · rw [cNthMaxFiber_second_four, Omega.X.maxFiberMultiplicity_four]
        omega
      · rw [cNthMaxFiber_second_five, Omega.X.maxFiberMultiplicity_five]
        omega
      · rw [cNthMaxFiber_second_six, Omega.X.maxFiberMultiplicity_six]
        omega
      · rw [cNthMaxFiber_second_seven, Omega.X.maxFiberMultiplicity_seven]
        omega
      · rw [h8, Omega.X.maxFiberMultiplicity_eight]
        omega
      · rw [h9, Omega.X.maxFiberMultiplicity_nine]
        omega
      · rw [h10, Omega.X.maxFiberMultiplicity_ten]
        omega
    · push_neg at hsmall
      have hm11 : 11 ≤ m := by omega
      rcases Nat.even_or_odd m with hmEven | hmOdd
      · rcases hmEven with ⟨k, hk⟩
        rw [hk, ← two_mul]
        have hk5 : 5 ≤ k := by omega
        have hk1 : 1 ≤ k := by omega
        rw [heven k hk5, Omega.X.maxFiberMultiplicity_even_of_two_step two_step k hk1]
        have hmono : Nat.fib (k - 4) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
        have hoddBound : Nat.fib (k + 1) ≤ 13 * Nat.fib (k - 4) := by
          simpa [show (k - 4) + 5 = k + 1 by omega] using
            fib_add_five_le_thirteen_mul (k - 4) (by omega)
        have hsucc : Nat.fib (k + 2) ≤ 2 * Nat.fib (k + 1) := by
          simpa [show (k + 1) + 1 = k + 2 by omega] using
            fib_succ_le_double (k + 1) (by omega)
        have htopBound : Nat.fib (k + 2) ≤ 26 * Nat.fib (k - 4) := by
          calc
            Nat.fib (k + 2) ≤ 2 * Nat.fib (k + 1) := hsucc
            _ ≤ 2 * (13 * Nat.fib (k - 4)) := Nat.mul_le_mul_left 2 hoddBound
            _ = 26 * Nat.fib (k - 4) := by omega
        omega
      · rcases hmOdd with ⟨k, hk⟩
        rw [hk]
        have hk5 : 5 ≤ k := by omega
        have hk1 : 1 ≤ k := by omega
        rw [hodd k hk5, Omega.X.maxFiberMultiplicity_odd_of_two_step two_step k hk1]
        have hmono : Nat.fib (k - 4) ≤ 2 * Nat.fib (k + 1) := by
          calc
            Nat.fib (k - 4) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
            _ ≤ 2 * Nat.fib (k + 1) := by omega
        have hoddBound : Nat.fib (k + 1) ≤ 13 * Nat.fib (k - 4) := by
          simpa [show (k - 4) + 5 = k + 1 by omega] using
            fib_add_five_le_thirteen_mul (k - 4) (by omega)
        have htopBound : 2 * Nat.fib (k + 1) ≤ 26 * Nat.fib (k - 4) := by
          calc
            2 * Nat.fib (k + 1) ≤ 2 * (13 * Nat.fib (k - 4)) := Nat.mul_le_mul_left 2 hoddBound
            _ = 26 * Nat.fib (k - 4) := by omega
        omega
  · have h13second : cNthMaxFiber 13 1 = 2 * Nat.fib (6 + 1) - Nat.fib (6 - 4) := hodd 6 (by omega)
    have h13top : Omega.X.maxFiberMultiplicity 13 = 2 * Nat.fib (6 + 1) :=
      Omega.X.maxFiberMultiplicity_odd_of_two_step two_step 6 (by omega)
    rw [h13second, h13top]
    norm_num [Nat.fib]

end Omega
