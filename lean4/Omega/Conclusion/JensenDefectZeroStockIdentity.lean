import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.JensenDefectEnergyReverseklIdentity

namespace Omega.Conclusion

/-- Concrete bookkeeping for the zero-stock refinement of the Jensen defect identity. Besides the
energy/reverse-KL package, we record the Jensen zero stock and its nonnegativity. -/
structure conclusion_jensen_defect_zero_stock_identity_data where
  averageLogDensity : ℝ
  averageLogNorm : ℝ
  energyRatio : ℝ
  energyTerm : ℝ
  reverseKL : ℝ
  jensenDefect : ℝ
  zeroStockSum : ℝ
  averageLogDensity_eq : averageLogDensity = 2 * averageLogNorm - Real.log energyRatio
  reverseKL_eq : reverseKL = -averageLogDensity
  jensenDefect_eq : jensenDefect = averageLogNorm
  energyTerm_eq : energyTerm = Real.log energyRatio
  jensenFormula_eq : jensenDefect = zeroStockSum
  zeroStockSum_nonneg : 0 ≤ zeroStockSum

/-- The energy-minus-reverse-KL quantity is exactly twice the Jensen defect and hence twice the
Jensen zero stock. -/
def conclusion_jensen_defect_zero_stock_identity_statement
    (D : conclusion_jensen_defect_zero_stock_identity_data) : Prop :=
  D.energyTerm - D.reverseKL = 2 * D.jensenDefect ∧
    D.energyTerm - D.reverseKL = 2 * D.zeroStockSum ∧
    0 ≤ D.energyTerm - D.reverseKL

/-- The zero-stock data induces the previously formalized energy/reverse-KL package by forgetting
the extra Jensen-formula bookkeeping. -/
def conclusion_jensen_defect_zero_stock_identity_to_reversekl_identity_data
    (D : conclusion_jensen_defect_zero_stock_identity_data) :
    conclusion_jensen_defect_energy_reversekl_identity_data where
  averageLogDensity := D.averageLogDensity
  averageLogNorm := D.averageLogNorm
  energyRatio := D.energyRatio
  reverseKL := D.reverseKL
  jensenDefect := D.jensenDefect
  averageLogDensity_eq := D.averageLogDensity_eq
  reverseKL_eq := D.reverseKL_eq
  jensenDefect_eq := D.jensenDefect_eq

/-- Paper label: `thm:conclusion-jensen-defect-zero-stock-identity`. Combining the
energy/reverse-KL identity with Jensen's zero-stock formula yields the exact zero-stock
representation of the energy gap. -/
theorem paper_conclusion_jensen_defect_zero_stock_identity
    (D : conclusion_jensen_defect_zero_stock_identity_data) :
    conclusion_jensen_defect_zero_stock_identity_statement D := by
  have hbase :=
    paper_conclusion_jensen_defect_energy_reversekl_identity
      (conclusion_jensen_defect_zero_stock_identity_to_reversekl_identity_data D)
  have hbase' :
      D.jensenDefect = (1 / 2 : ℝ) * Real.log D.energyRatio - (1 / 2 : ℝ) * D.reverseKL := by
    simpa [conclusion_jensen_defect_zero_stock_identity_to_reversekl_identity_data] using hbase
  have henergy : D.energyTerm - D.reverseKL = 2 * D.jensenDefect := by
    rw [D.energyTerm_eq]
    nlinarith [hbase']
  refine ⟨henergy, ?_, ?_⟩
  · calc
      D.energyTerm - D.reverseKL = 2 * D.jensenDefect := henergy
      _ = 2 * D.zeroStockSum := by rw [D.jensenFormula_eq]
  · calc
      0 ≤ 2 * D.zeroStockSum := by nlinarith [D.zeroStockSum_nonneg]
      _ = D.energyTerm - D.reverseKL := by
        calc
          2 * D.zeroStockSum = 2 * D.jensenDefect := by rw [D.jensenFormula_eq]
          _ = D.energyTerm - D.reverseKL := by linarith [henergy]

end Omega.Conclusion
