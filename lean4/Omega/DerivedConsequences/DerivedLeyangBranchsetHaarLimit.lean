import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- Paper label: `thm:derived-leyang-branchset-haar-limit`. -/
theorem paper_derived_leyang_branchset_haar_limit (n r : ℕ) (h : r ≤ n) :
    ((4 : ℚ) ^ (n - r)) / (5 * (4 : ℚ) ^ n) = (1 : ℚ) / (5 * (4 : ℚ) ^ r) := by
  have hpow :
      (4 : ℚ) ^ n = (4 : ℚ) ^ (n - r) * (4 : ℚ) ^ r := by
    rw [← Nat.sub_add_cancel h]
    simpa using (pow_add (4 : ℚ) (n - r) r)
  rw [hpow]
  field_simp [pow_ne_zero _ (show (4 : ℚ) ≠ 0 by norm_num)]

end Omega.DerivedConsequences
