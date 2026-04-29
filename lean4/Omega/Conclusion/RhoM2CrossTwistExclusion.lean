import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-rho-m2-cross-twist-exclusion`. -/
theorem paper_conclusion_rho_m2_cross_twist_exclusion (m : ℕ) (hm : 2 ≤ m)
    (rho rho_in rho_bd rho_cross : ℝ) (hrho : rho = max (max rho_in rho_bd) rho_cross)
    (hcross : rho_cross ≤ max rho_in rho_bd) :
    rho_cross ≤ max rho_in rho_bd ∧ rho = max rho_in rho_bd := by
  have _rankAtLeastTwo : 2 ≤ m := hm
  refine ⟨hcross, ?_⟩
  simpa [max_eq_left hcross] using hrho

end Omega.Conclusion
