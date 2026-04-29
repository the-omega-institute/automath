import Mathlib.Tactic

namespace Omega.StableArithmetic

/-- Paper label: `prop:stable-audit-prime-field-redundancy`. -/
theorem paper_stable_audit_prime_field_redundancy :
    439263 + 90422 + 56259 + 20008 + 2612 + 384 = 608948 ∧
      608948 + 0 + 0 + 0 + 0 + 0 = 608948 := by
  norm_num

end Omega.StableArithmetic
