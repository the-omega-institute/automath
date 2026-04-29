import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-oracle-critical-budget-entropy-identity`. -/
theorem paper_pom_oracle_critical_budget_entropy_identity (a1 h1 betaCrit : ℝ)
    (hEntropy : h1 = Real.log 2 - a1) (hBeta : betaCrit = a1 / Real.log 2) :
    betaCrit = 1 - h1 / Real.log 2 := by
  have hlog2 : Real.log 2 ≠ 0 := by
    have hpos : 0 < Real.log 2 := by
      apply Real.log_pos
      norm_num
    linarith
  rw [hBeta, hEntropy]
  field_simp [hlog2]
  ring

end Omega.POM
