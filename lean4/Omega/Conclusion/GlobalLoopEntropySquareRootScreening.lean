import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-global-loop-entropy-square-root-screening`.
Exponentiating the certified loop-entropy inequality gives a bound on `ρ²`, and taking square
roots yields the screening estimates. -/
theorem paper_conclusion_global_loop_entropy_square_root_screening
    (rho L : ℝ) (hL : 0 ≤ L) (hunit : rho ^ 2 < 1) (hcert : -Real.log (1 - rho ^ 2) ≤ L) :
    |rho| ≤ Real.sqrt (1 - Real.exp (-L)) ∧ |rho| ≤ min 1 (Real.sqrt L) := by
  have hone_minus_pos : 0 < 1 - rho ^ 2 := by
    linarith
  have hlog_lower : -L ≤ Real.log (1 - rho ^ 2) := by
    linarith
  have hexp_le : Real.exp (-L) ≤ 1 - rho ^ 2 := by
    calc
      Real.exp (-L) ≤ Real.exp (Real.log (1 - rho ^ 2)) := Real.exp_le_exp.mpr hlog_lower
      _ = 1 - rho ^ 2 := by rw [Real.exp_log hone_minus_pos]
  have hsq : rho ^ 2 ≤ 1 - Real.exp (-L) := by
    linarith
  have habs_screen : |rho| ≤ Real.sqrt (1 - Real.exp (-L)) := by
    exact Real.abs_le_sqrt hsq
  have hone_sub_exp_le : 1 - Real.exp (-L) ≤ L := by
    have haux : 1 - L ≤ Real.exp (-L) := by
      simpa using Real.one_sub_le_exp_neg L
    linarith
  have habs_sqrtL : |rho| ≤ Real.sqrt L := by
    exact Real.abs_le_sqrt (le_trans hsq hone_sub_exp_le)
  have habs_le_one : |rho| ≤ 1 := by
    nlinarith [sq_abs rho, hunit]
  exact ⟨habs_screen, le_min habs_le_one habs_sqrtL⟩

end Omega.Conclusion
