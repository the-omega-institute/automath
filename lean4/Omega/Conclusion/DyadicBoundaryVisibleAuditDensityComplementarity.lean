import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_dyadic_boundary_visible_audit_density_complementarity {K Q N : ℕ}
    (hN : 0 < N) (hKQ : K + Q = N) :
    ((K : ℚ) / (N : ℚ) + (Q : ℚ) / (N : ℚ) = 1) := by
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hKQq : (K : ℚ) + (Q : ℚ) = (N : ℚ) := by exact_mod_cast hKQ
  rw [← add_div, hKQq]
  exact div_self hNq

end Omega.Conclusion
