import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-coordinatebundle-critical-audit-density`. -/
theorem paper_conclusion_coordinatebundle_critical_audit_density (m n s : ℕ) (hs : 0 < s)
    (hsn : s ≤ n) :
    Real.log ((2 : ℝ) ^ (m * (n - s))) /
        ((2 : ℝ) * (s : ℝ) * (2 : ℝ) ^ (m * (s - 1))) =
      (((m * (n - s) : ℕ) : ℝ) * Real.log 2) /
        ((2 : ℝ) * (s : ℝ) * (2 : ℝ) ^ (m * (s - 1))) := by
  have _hs_used := hs
  have _hsn_used := hsn
  rw [Real.log_pow]

end Omega.Conclusion
