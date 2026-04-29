import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-local-entropy-tax-pressure-representation`. -/
theorem paper_conclusion_local_entropy_tax_pressure_representation {ι : Type*} [Fintype ι]
    (m : ℕ) (q : ℝ) (d HA HB : ι → ℝ) (hd : ∀ x, 0 < d x) (hq : 1 < q)
    (hH : ∀ x, HA x ≤ HB x) :
    (∑ x, Real.exp (q * Real.log (d x) - (q - 1) * HB x)) ≤
      (∑ x, Real.exp (q * Real.log (d x) - (q - 1) * HA x)) := by
  classical
  let _ := m
  let _ := hd
  refine Finset.sum_le_sum ?_
  intro x _hx
  refine Real.exp_le_exp.mpr ?_
  have hq_nonneg : 0 ≤ q - 1 := by linarith
  have hmul : (q - 1) * HA x ≤ (q - 1) * HB x :=
    mul_le_mul_of_nonneg_left (hH x) hq_nonneg
  linarith

end Omega.Conclusion
