import Mathlib.Tactic
import Omega.Folding.MomentSum

namespace Omega.Conclusion

theorem paper_conclusion_golden_squeeze_dim_aut (m : ℕ) :
    ((4 : ℚ) ^ m) / (Nat.fib (m + 2) : ℚ) ≤ (Omega.momentSum 2 m : ℚ) ∧
      (Omega.momentSum 2 m : ℚ) ≤ (2 ^ m : ℚ) * Omega.X.maxFiberMultiplicity m := by
  constructor
  · have hfib_pos : (0 : ℚ) < (Nat.fib (m + 2) : ℚ) := by
      exact_mod_cast fib_succ_pos (m + 1)
    have hlowNat : 4 ^ m ≤ Nat.fib (m + 2) * Omega.momentSum 2 m := by
      calc
        4 ^ m = (2 ^ m) ^ 2 := by
          calc
            4 ^ m = (2 ^ 2) ^ m := by norm_num
            _ = 2 ^ (2 * m) := by rw [pow_mul]
            _ = 2 ^ (m * 2) := by congr 1; omega
            _ = (2 ^ m) ^ 2 := by rw [pow_mul]
        _ ≤ Nat.fib (m + 2) * Omega.momentSum 2 m := Omega.momentSum_cauchy_schwarz m
    have hlowQ : (4 : ℚ) ^ m ≤ (Nat.fib (m + 2) : ℚ) * (Omega.momentSum 2 m : ℚ) := by
      exact_mod_cast hlowNat
    exact (div_le_iff₀ hfib_pos).2 (by simpa [mul_comm] using hlowQ)
  · have hupperNat : Omega.momentSum 2 m ≤ Omega.X.maxFiberMultiplicity m ^ (2 - 1) * 2 ^ m :=
      Omega.momentSum_le_max_pow 2 m (by omega)
    have hupperQ :
        (Omega.momentSum 2 m : ℚ) ≤
          (Omega.X.maxFiberMultiplicity m ^ (2 - 1) * 2 ^ m : ℚ) := by
      exact_mod_cast hupperNat
    simpa [pow_one, mul_comm] using hupperQ

end Omega.Conclusion
