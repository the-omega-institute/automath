import Mathlib.Tactic
import Omega.Conclusion.Elementary2GroupMinimalTorusDimension

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-anomaly-phase-budget-rigidity`.
The verified elementary `2`-group torus lower bound at `ν = 21` supplies the anomaly phase
budget, while the collision/anomaly numerical split is elementary arithmetic. -/
theorem paper_conclusion_window6_anomaly_phase_budget_rigidity :
    (∀ r : ℕ,
        conclusion_elementary_2group_minimal_torus_dimension_faithful_phase_model 21 r →
          21 ≤ r) ∧
      (21 : ℕ) + 53 = 74 := by
  refine ⟨?_, by norm_num⟩
  intro r hρ
  exact (paper_conclusion_elementary_2group_minimal_torus_dimension 21).1 r hρ

end Omega.Conclusion
