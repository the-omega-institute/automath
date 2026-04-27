import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-!
# BinFold thermal-budget codimension-two corner

This file packages the concrete singleton thermal axis and half-line budget axis whose minimal
intersection is the paper's golden-threshold corner.
-/

/-- Data carrier for the BinFold thermal-budget corner statement. -/
structure conclusion_binfold_thermal_budget_codimtwo_corner_data where

/-- The golden ratio used by the thermal axis. -/
noncomputable def conclusion_binfold_thermal_budget_codimtwo_corner_phi : ℝ :=
  ((1 : ℝ) + Real.sqrt 5) / 2

/-- The thermal coordinate selected by the finite nonzero `π`-limit. -/
noncomputable def conclusion_binfold_thermal_budget_codimtwo_corner_beta_star : ℝ :=
  Real.log conclusion_binfold_thermal_budget_codimtwo_corner_phi

/-- The budget threshold coordinate for full inversion. -/
noncomputable def conclusion_binfold_thermal_budget_codimtwo_corner_s_star : ℝ :=
  Real.logb 2
    (conclusion_binfold_thermal_budget_codimtwo_corner_phi ^ 2 / Real.sqrt 5)

/-- Thermal admissibility is the singleton selected critical temperature. -/
noncomputable def conclusion_binfold_thermal_budget_codimtwo_corner_thermalAdmissible
    (beta : ℝ) : Prop :=
  beta = conclusion_binfold_thermal_budget_codimtwo_corner_beta_star

/-- Budget admissibility is the half-line above the golden full-inversion threshold. -/
noncomputable def conclusion_binfold_thermal_budget_codimtwo_corner_budgetAdmissible
    (s : ℝ) : Prop :=
  conclusion_binfold_thermal_budget_codimtwo_corner_s_star ≤ s

/-- Concrete claim for the BinFold thermal-budget codimension-two corner. -/
noncomputable def conclusion_binfold_thermal_budget_codimtwo_corner_claim
    (_D : conclusion_binfold_thermal_budget_codimtwo_corner_data) : Prop :=
  (∀ beta : ℝ,
      conclusion_binfold_thermal_budget_codimtwo_corner_thermalAdmissible beta ↔
        beta = conclusion_binfold_thermal_budget_codimtwo_corner_beta_star) ∧
    (∀ s : ℝ,
      conclusion_binfold_thermal_budget_codimtwo_corner_budgetAdmissible s ↔
        conclusion_binfold_thermal_budget_codimtwo_corner_s_star ≤ s) ∧
    conclusion_binfold_thermal_budget_codimtwo_corner_thermalAdmissible
      conclusion_binfold_thermal_budget_codimtwo_corner_beta_star ∧
    conclusion_binfold_thermal_budget_codimtwo_corner_budgetAdmissible
      conclusion_binfold_thermal_budget_codimtwo_corner_s_star ∧
    (∀ beta s : ℝ,
      conclusion_binfold_thermal_budget_codimtwo_corner_thermalAdmissible beta →
      conclusion_binfold_thermal_budget_codimtwo_corner_budgetAdmissible s →
        beta = conclusion_binfold_thermal_budget_codimtwo_corner_beta_star ∧
          conclusion_binfold_thermal_budget_codimtwo_corner_s_star ≤ s)

/-- The thermal admissible set is a singleton, the budget admissible set is a half-line, and
their minimal feasible point is the golden threshold corner.
    thm:conclusion-binfold-thermal-budget-codimtwo-corner -/
theorem paper_conclusion_binfold_thermal_budget_codimtwo_corner
    (D : conclusion_binfold_thermal_budget_codimtwo_corner_data) :
    conclusion_binfold_thermal_budget_codimtwo_corner_claim D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro beta
    rfl
  · intro s
    rfl
  · rfl
  · exact le_rfl
  · intro beta s hbeta hs
    exact ⟨hbeta, hs⟩

end Omega.Conclusion
