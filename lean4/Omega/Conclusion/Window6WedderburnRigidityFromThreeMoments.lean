import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-wedderburn-rigidity-from-three-moments`. -/
theorem paper_conclusion_window6_wedderburn_rigidity_from_three_moments
    (n2 n3 n4 : ℕ)
    (hcenter : n2 + n3 + n4 = 21)
    (hmicro : 2 * n2 + 3 * n3 + 4 * n4 = 64)
    (halg : 2 ^ 2 * n2 + 3 ^ 2 * n3 + 4 ^ 2 * n4 = 212) :
    n2 = 8 ∧ n3 = 4 ∧ n4 = 9 := by
  omega

end Omega.Conclusion
