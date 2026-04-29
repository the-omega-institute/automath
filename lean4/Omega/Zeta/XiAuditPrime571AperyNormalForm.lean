import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-audit-prime-571-apery-normal-form`. -/
theorem paper_xi_audit_prime_571_apery_normal_form :
    571 = 21 * 11 + 34 * 10 ∧
      (∀ a b : Nat, b < 21 → 571 = 21 * a + 34 * b → a = 11 ∧ b = 10) := by
  constructor
  · norm_num
  · intro a b hb h
    omega

end Omega.Zeta
