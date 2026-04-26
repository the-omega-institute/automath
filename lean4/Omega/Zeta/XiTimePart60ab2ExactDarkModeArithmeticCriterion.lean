import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Zeta

private lemma xi_time_part60ab2_exact_dark_mode_arithmetic_criterion_even_fib_shift
    (m : ℕ) : Even (Nat.fib (m + 2)) ↔ m % 3 = 1 := by
  rw [Nat.even_iff, Omega.fib_mod_two_period (m + 2)]
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hshift : (m + 2) % 3 = 2 := by omega
    simp [h0, hshift, Nat.fib]
  · have hshift : (m + 2) % 3 = 0 := by omega
    simp [h1, hshift, Nat.fib]
  · have hshift : (m + 2) % 3 = 1 := by omega
    simp [h2, hshift, Nat.fib]

/-- Paper label: `thm:xi-time-part60ab2-exact-dark-mode-arithmetic-criterion`. -/
theorem paper_xi_time_part60ab2_exact_dark_mode_arithmetic_criterion
    (m M : ℕ) (zeroMode : ZMod M → Prop) (hM : M = Nat.fib (m + 2))
    (hcrit : ∀ k : ZMod M,
      zeroMode k ↔
        Even M ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧
          k * (Nat.fib (j + 1) : ZMod M) = ((M / 2 : ℕ) : ZMod M)) :
    (Even M → zeroMode ((M / 2 : ℕ) : ZMod M)) ∧
      (m % 3 = 1 ↔ zeroMode ((M / 2 : ℕ) : ZMod M)) := by
  subst M
  have hparity := xi_time_part60ab2_exact_dark_mode_arithmetic_criterion_even_fib_shift m
  have hEven_to_zero :
      Even (Nat.fib (m + 2)) →
        zeroMode ((Nat.fib (m + 2) / 2 : ℕ) : ZMod (Nat.fib (m + 2))) := by
    intro hEven
    have hm : 1 ≤ m := by
      have hm1 : m % 3 = 1 := hparity.mp hEven
      omega
    exact (hcrit ((Nat.fib (m + 2) / 2 : ℕ) : ZMod (Nat.fib (m + 2)))).mpr
      ⟨hEven, ⟨1, by omega, hm, by simp [Nat.fib]⟩⟩
  refine ⟨hEven_to_zero, ?_⟩
  constructor
  · intro hm
    exact hEven_to_zero (hparity.mpr hm)
  · intro hzero
    exact hparity.mp
      ((hcrit ((Nat.fib (m + 2) / 2 : ℕ) : ZMod (Nat.fib (m + 2)))).mp hzero).1

end Omega.Zeta
