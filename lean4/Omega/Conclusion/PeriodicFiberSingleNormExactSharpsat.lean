import Mathlib.Tactic
import Omega.Conclusion.PeriodicFiberAcceptanceRateNormalizedSharpSat

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-periodic-fiber-single-norm-exact-sharpsat`. -/
theorem paper_conclusion_periodic_fiber_single_norm_exact_sharpsat
    (m n satCount : ℕ) (norm scalar : ℝ) (hm : ((2 : ℝ) ^ m - 1) ≠ 0)
    (hn : ((2 : ℝ) ^ n) ≠ 0)
    (hscalar : scalar = ((2 : ℝ) ^ n / ((2 : ℝ) ^ m - 1)) * (norm - 1))
    (hnorm : norm =
      1 + (((2 : ℝ) ^ m - 1) * (satCount : ℝ) / ((2 : ℝ) ^ n))) :
    scalar = satCount ∧ ((1 : ℝ) / 2 ≤ scalar ↔ 1 ≤ satCount) := by
  have hscalar_eq : scalar = satCount := by
    rw [hscalar, hnorm]
    field_simp [hm, hn]
    ring
  refine ⟨hscalar_eq, ?_⟩
  rw [hscalar_eq]
  constructor
  · intro h
    by_cases hzero : satCount = 0
    · subst satCount
      norm_num at h
    · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero)
  · intro h
    have hreal : (1 : ℝ) ≤ satCount := by
      exact_mod_cast h
    linarith

end Omega.Conclusion
