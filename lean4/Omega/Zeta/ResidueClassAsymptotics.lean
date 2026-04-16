import Mathlib.Tactic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing residue-class asymptotic seed for the prime-languages paper.
    lem:residue-class-asymptotics -/
theorem paper_prime_languages_residue_class_asymptotics (k : ℕ) :
    ((2 : ℤ) ^ (2 * k) + (-2 : ℤ) ^ (2 * k) = 2 * 4 ^ k) ∧
      ((2 : ℤ) ^ (2 * k + 1) + (-2 : ℤ) ^ (2 * k + 1) = 0) := by
  constructor
  · calc
      (2 : ℤ) ^ (2 * k) + (-2 : ℤ) ^ (2 * k)
          = (2 : ℤ) ^ (2 * k) + (2 : ℤ) ^ (2 * k) := by simp
      _ = 2 * (2 : ℤ) ^ (2 * k) := by ring
      _ = 2 * ((2 : ℤ) ^ 2) ^ k := by rw [pow_mul]
      _ = 2 * 4 ^ k := by norm_num
  · calc
      (2 : ℤ) ^ (2 * k + 1) + (-2 : ℤ) ^ (2 * k + 1)
          = (2 : ℤ) ^ (2 * k) * 2 + (2 : ℤ) ^ (2 * k) * (-2) := by
              rw [pow_add, pow_add]
              simp
      _ = 0 := by ring

end Omega.Zeta
