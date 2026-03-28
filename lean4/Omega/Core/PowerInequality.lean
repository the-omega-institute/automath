import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Omega

/-- (a+b)^q >= a^q + b^q + 1 for q >= 2, a >= 1, b >= 1.
    prop:pom-coarsegraining-collision-moment-strict-monotonicity -/
theorem pow_add_strict_super (a b q : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hq : 2 ≤ q) :
    a ^ q + b ^ q + 1 ≤ (a + b) ^ q := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  induction q with
  | zero =>
    -- q = 2: need a²+b²+1 ≤ (a+b)² = a²+2ab+b²
    simp only [Nat.zero_add, pow_succ, pow_zero, one_mul]
    nlinarith [Nat.mul_le_mul ha hb]
  | succ q ih =>
    have ihq : a ^ (q + 2) + b ^ (q + 2) + 1 ≤ (a + b) ^ (q + 2) := ih (by omega)
    -- Goal: a^(q+3) + b^(q+3) + 1 ≤ (a+b)^(q+3)
    -- Key idea: (a+b)^(q+3) = (a+b)*(a+b)^(q+2)
    -- We show this via: a*(a+b)^(q+2) + b*(a+b)^(q+2) = (a+b)^(q+3)
    -- and a*(a+b)^(q+2) ≥ a^(q+3) (since (a+b)^(q+2) ≥ a^(q+2))
    -- and b*(a+b)^(q+2) ≥ b^(q+3) + 1 (since (a+b)^(q+2) ≥ b^(q+2) + a^(q+2) + 1
    --   from IH, so b*(a+b)^(q+2) ≥ b*b^(q+2) + b*a^(q+2) + b ≥ b^(q+3) + 1 + 1)
    have hab : (a + b) ^ (q + 3) = (a + b) * (a + b) ^ (q + 2) := by
      rw [show q + 3 = (q + 2) + 1 from by omega, pow_succ, Nat.mul_comm]
    rw [hab]
    have ha_pow : a ^ (q + 2) ≤ (a + b) ^ (q + 2) :=
      Nat.pow_le_pow_left (by omega) _
    have hb_pow : b ^ (q + 2) ≤ (a + b) ^ (q + 2) :=
      Nat.pow_le_pow_left (by omega) _
    -- (a+b) * (a+b)^n = a*(a+b)^n + b*(a+b)^n
    -- ≥ a*a^n + b*(a^n + b^n + 1) = a^(n+1) + b*a^n + b^(n+1) + b
    -- ≥ a^(n+1) + b^(n+1) + 1 + 1 = a^(n+1) + b^(n+1) + 2 ≥ a^(n+1)+b^(n+1)+1
    -- Key witness: b * ihq and a * ha_pow
    have ha_exp : a ^ (q + 1 + 2) = a * a ^ (q + 2) := by
      rw [show q + 1 + 2 = (q + 2) + 1 from by omega, pow_succ, Nat.mul_comm]
    have hb_exp : b ^ (q + 1 + 2) = b * b ^ (q + 2) := by
      rw [show q + 1 + 2 = (q + 2) + 1 from by omega, pow_succ, Nat.mul_comm]
    rw [ha_exp, hb_exp]
    nlinarith [Nat.mul_le_mul_left a ha_pow,
               Nat.mul_le_mul_left b ihq,
               Nat.one_le_pow (q + 2) a ha,
               Nat.one_le_pow (q + 2) b hb]

end Omega
