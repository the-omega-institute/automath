import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-core-mirror-branch-saturation-dominance`. -/
theorem paper_conclusion_core_mirror_branch_saturation_dominance {c : ℝ} (hc : 1 < c) :
    (c / c = 1) ∧ (1 / c < 1) := by
  have hc0 : c ≠ 0 := by linarith
  constructor
  · exact div_self hc0
  · have hcpos : 0 < c := by linarith
    field_simp [hc0]
    exact hc

end Omega.Conclusion
