import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete Perron--Frobenius entropy data for scan-budget/codimension duality. -/
structure conclusion_scan_budget_codim_duality_data where
  conclusion_scan_budget_codim_duality_topEntropy : ℝ := Real.log 2
  conclusion_scan_budget_codim_duality_thresholdEntropy : ℝ := 0

namespace conclusion_scan_budget_codim_duality_data

/-- The entropy gap in the threshold ambiguity layer. -/
def conclusion_scan_budget_codim_duality_epsilon
    (D : conclusion_scan_budget_codim_duality_data) : ℝ :=
  D.conclusion_scan_budget_codim_duality_topEntropy -
    D.conclusion_scan_budget_codim_duality_thresholdEntropy

/-- Hausdorff codimension normalized by the full binary entropy `log 2`. -/
def conclusion_scan_budget_codim_duality_codimension
    (D : conclusion_scan_budget_codim_duality_data) : ℝ :=
  D.conclusion_scan_budget_codim_duality_epsilon / Real.log 2

/-- The exponential scan threshold associated to depth `n`. -/
def conclusion_scan_budget_codim_duality_scanThreshold
    (D : conclusion_scan_budget_codim_duality_data) (n : ℕ) : ℝ :=
  Real.exp (D.conclusion_scan_budget_codim_duality_epsilon * n)

/-- The same threshold written in codimension units. -/
def conclusion_scan_budget_codim_duality_codimThreshold
    (D : conclusion_scan_budget_codim_duality_data) (n : ℕ) : ℝ :=
  Real.exp ((Real.log 2 * D.conclusion_scan_budget_codim_duality_codimension) * n)

/-- Concrete statement of scan-budget/codimension duality. -/
def conclusion_scan_budget_codim_duality_statement
    (D : conclusion_scan_budget_codim_duality_data) : Prop :=
  Real.log 2 * D.conclusion_scan_budget_codim_duality_codimension =
      D.conclusion_scan_budget_codim_duality_epsilon ∧
    (∀ n : ℕ,
      D.conclusion_scan_budget_codim_duality_scanThreshold n =
        D.conclusion_scan_budget_codim_duality_codimThreshold n) ∧
    (∀ n : ℕ,
      D.conclusion_scan_budget_codim_duality_scanThreshold n =
        Real.exp
          ((Real.log 2 * D.conclusion_scan_budget_codim_duality_codimension) * n))

end conclusion_scan_budget_codim_duality_data

open conclusion_scan_budget_codim_duality_data

/-- Paper label: `thm:conclusion-scan-budget-codim-duality`. -/
theorem paper_conclusion_scan_budget_codim_duality
    (D : conclusion_scan_budget_codim_duality_data) :
    conclusion_scan_budget_codim_duality_statement D := by
  have hlog_ne : Real.log 2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [conclusion_scan_budget_codim_duality_codimension]
    field_simp [hlog_ne]
  · intro n
    rw [conclusion_scan_budget_codim_duality_scanThreshold,
      conclusion_scan_budget_codim_duality_codimThreshold]
    congr 1
    rw [conclusion_scan_budget_codim_duality_codimension]
    field_simp [hlog_ne]
  · intro n
    rw [conclusion_scan_budget_codim_duality_scanThreshold,
      conclusion_scan_budget_codim_duality_codimension]
    congr 1
    field_simp [hlog_ne]

end

end Omega.Conclusion
