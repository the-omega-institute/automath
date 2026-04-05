import Mathlib.Tactic

/-!
# Spectrum product sign law

The sign pattern (-1)^(q(q+1)/2) has period 4 in q.
-/

namespace Omega.Conclusion

/-- q*(q+1) is always even, so the natural division by 2 is exact. -/
private theorem mul_succ_even (q : ℕ) : 2 ∣ q * (q + 1) :=
  Nat.even_mul_succ_self q |>.two_dvd

/-- (-1)^(q(q+1)/2) has period 4.
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem neg_one_pow_triangular_mod4 (q : ℕ) :
    (-1 : ℤ) ^ (q * (q + 1) / 2) =
      if q % 4 = 0 ∨ q % 4 = 3 then 1 else -1 := by
  -- Suffices to show the result for q mod 4 shifted by multiples of 4
  -- Key: T(q+4) = T(q) + 2q + 10, and T(q+4) - T(q) is always even
  -- So (-1)^T(q+4) = (-1)^(T(q) + 2q + 10) and the sign depends only on T(q) mod 2
  induction q using Nat.strongRecOn with
  | _ q ih =>
    match q with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | 3 => simp
    | q + 4 =>
      -- T(q+4) = (q+4)(q+5)/2 = q(q+1)/2 + (2q+5)·2 - q(q+1)/2 ...
      -- Actually: (q+4)(q+5) = q(q+1) + 4(2q+5), so T(q+4) = T(q) + 2(2q+5)
      have heven : 2 ∣ q * (q + 1) := mul_succ_even q
      have hkey : (q + 4) * (q + 4 + 1) / 2 = q * (q + 1) / 2 + (4 * q + 10) := by
        have : (q + 4) * (q + 4 + 1) = q * (q + 1) + 2 * (4 * q + 10) := by ring
        omega
      rw [hkey, pow_add, ih q (by omega)]
      have : (-1 : ℤ) ^ (4 * q + 10) = 1 := by
        rw [show 4 * q + 10 = 2 * (2 * q + 5) from by ring, pow_mul, neg_one_sq, one_pow]
      rw [this, mul_one]
      have hmod : (q + 4) % 4 = q % 4 := by omega
      simp only [hmod]

end Omega.Conclusion
