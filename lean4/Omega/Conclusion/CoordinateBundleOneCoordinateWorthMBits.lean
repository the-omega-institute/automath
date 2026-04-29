import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleCodimensionExponentialDefect

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-coordinatebundle-one-coordinate-worth-m-bits`. -/
theorem paper_conclusion_coordinatebundle_one_coordinate_worth_m_bits (m n s : ℕ) (hs : s < n) :
    coordinateBundleAuditGap m n s = 2 ^ m * coordinateBundleAuditGap m n (s + 1) := by
  have hs' : n - s = n - (s + 1) + 1 := by
    omega
  calc
    coordinateBundleAuditGap m n s = 2 ^ (m * (n - s)) := by
      rw [paper_conclusion_coordinatebundle_codimension_exponential_defect]
    _ = 2 ^ (m * (n - (s + 1) + 1)) := by rw [hs']
    _ = 2 ^ (m * (n - (s + 1)) + m) := by rw [Nat.mul_add, Nat.mul_one]
    _ = 2 ^ (m * (n - (s + 1))) * 2 ^ m := by rw [pow_add]
    _ = 2 ^ m * 2 ^ (m * (n - (s + 1))) := by rw [Nat.mul_comm]
    _ = 2 ^ m * coordinateBundleAuditGap m n (s + 1) := by
      rw [paper_conclusion_coordinatebundle_codimension_exponential_defect]

end Omega.Conclusion
