import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter

/-- Tensor-product external budget on `m` copies. -/
def externalBudgetTensorBudget (b m : ℕ) : ℕ :=
  b ^ m

/-- Binary side-information cost attached to the tensor budget. -/
noncomputable def externalBudgetTensorRate (b m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) * Real.logb 2 (b : ℝ))

/-- Multiplicativity of the tensor budget. -/
def externalBudgetTensorBudgetLaw (b : ℕ) : Prop :=
  ∀ m : ℕ, externalBudgetTensorBudget b m = b ^ m

/-- Exact bit-cost formula together with the asymptotic entropy-rate limit. -/
def externalBudgetTensorRateLaw (b : ℕ) : Prop :=
  (∀ m : ℕ, externalBudgetTensorRate b m = Nat.ceil (Real.logb 2 ((b : ℝ) ^ m))) ∧
    Tendsto (fun m : ℕ => (externalBudgetTensorRate b m : ℝ) / m)
      atTop (nhds (Real.logb 2 (b : ℝ)))

/-- The standard ceiling rounding window for the tensor bit-cost. -/
def externalBudgetTensorRoundingErrorLaw (b : ℕ) : Prop :=
  ∀ m : ℕ,
    let x : ℝ := (m : ℝ) * Real.logb 2 (b : ℝ)
    0 ≤ (externalBudgetTensorRate b m : ℝ) - x ∧
      (externalBudgetTensorRate b m : ℝ) - x < 1

theorem externalBudgetTensorRate_formula (b m : ℕ) :
    externalBudgetTensorRate b m = Nat.ceil (Real.logb 2 ((b : ℝ) ^ m)) := by
  rw [externalBudgetTensorRate, Real.logb_pow]

theorem externalBudgetTensorRate_limit (b : ℕ) (hb : 1 ≤ b) :
    Tendsto (fun m : ℕ => (externalBudgetTensorRate b m : ℝ) / m)
      atTop (nhds (Real.logb 2 (b : ℝ))) := by
  have hlog_nonneg : 0 ≤ Real.logb 2 (b : ℝ) := by
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hb)
  simpa [externalBudgetTensorRate, mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := Real.logb 2 (b : ℝ)) hlog_nonneg).comp
      tendsto_natCast_atTop_atTop

theorem externalBudgetTensorRoundingErrorLaw_true (b : ℕ) (hb : 1 ≤ b) :
    externalBudgetTensorRoundingErrorLaw b := by
  intro m
  dsimp [externalBudgetTensorRoundingErrorLaw]
  let x : ℝ := (m : ℝ) * Real.logb 2 (b : ℝ)
  have hlog_nonneg : 0 ≤ Real.logb 2 (b : ℝ) := by
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hb)
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (Nat.cast_nonneg m) hlog_nonneg
  constructor
  · change 0 ≤ (externalBudgetTensorRate b m : ℝ) - x
    exact sub_nonneg.mpr (Nat.le_ceil x)
  · change (externalBudgetTensorRate b m : ℝ) - x < 1
    simpa [externalBudgetTensorRate, x] using
      (sub_lt_iff_lt_add'.2 (Nat.ceil_lt_add_one hx_nonneg))

/-- Paper-facing package for tensor-budget multiplicativity, entropy rate, and ceiling error.
    thm:conclusion-external-budget-tensor-entropy-rate -/
theorem paper_conclusion_external_budget_tensor_entropy_rate (b : ℕ) (hb : 1 ≤ b) :
    externalBudgetTensorBudgetLaw b ∧
      externalBudgetTensorRateLaw b ∧
      externalBudgetTensorRoundingErrorLaw b := by
  refine ⟨?_, ?_, externalBudgetTensorRoundingErrorLaw_true b hb⟩
  · intro m
    rfl
  · exact ⟨externalBudgetTensorRate_formula b, externalBudgetTensorRate_limit b hb⟩

end Omega.Conclusion
