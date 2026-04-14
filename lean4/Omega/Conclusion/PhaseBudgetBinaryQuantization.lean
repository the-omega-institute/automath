import Mathlib.Tactic

namespace Omega.Conclusion

/-- Feasible phase budgets are the integer phases `k ≥ 1` satisfying the halfspace
    constraint `α ≤ k + c`.
    cor:conclusion-phase-budget-binary-quantization -/
def phaseBudgetFeasible (α c : ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧ α ≤ (k : ℝ) + c

/-- In the regime `1 < α < 2`, the only candidate minimal phase counts are `1` and `2`.
    cor:conclusion-phase-budget-binary-quantization -/
noncomputable def phaseBudgetMin (α c : ℝ) : ℕ :=
  if α - 1 ≤ c then 1 else 2

/-- Feasibility of one phase is exactly the threshold `c ≥ α - 1`.
    cor:conclusion-phase-budget-binary-quantization -/
theorem phaseBudgetFeasible_one_iff (α c : ℝ) :
    phaseBudgetFeasible α c 1 ↔ α - 1 ≤ c := by
  constructor
  · rintro ⟨_, hαc⟩
    have hαc' : α ≤ c + 1 := by simpa [add_comm] using hαc
    linarith
  · intro h
    refine ⟨by norm_num, ?_⟩
    have hαc : α ≤ c + 1 := by linarith
    simpa [add_comm] using hαc

/-- Two phases are always feasible once `c ≥ 0` and `α < 2`.
    cor:conclusion-phase-budget-binary-quantization -/
theorem phaseBudgetFeasible_two {α c : ℝ} (hα : α < 2) (hc : 0 ≤ c) :
    phaseBudgetFeasible α c 2 := by
  refine ⟨by norm_num, ?_⟩
  have hαc : α ≤ c + 2 := by linarith
  simpa [add_comm] using hαc

/-- The piecewise definition really is the least feasible phase count.
    cor:conclusion-phase-budget-binary-quantization -/
theorem phaseBudgetMin_isLeast {α c : ℝ}
    (hα₂ : α < 2) (hc : 0 ≤ c) :
    phaseBudgetFeasible α c (phaseBudgetMin α c) ∧
      ∀ {k : ℕ}, phaseBudgetFeasible α c k → phaseBudgetMin α c ≤ k := by
  by_cases hcut : α - 1 ≤ c
  · refine ⟨?_, ?_⟩
    · simpa [phaseBudgetMin, hcut] using (phaseBudgetFeasible_one_iff α c).2 hcut
    · intro y hy
      simpa [phaseBudgetMin, hcut] using hy.1
  · refine ⟨?_, ?_⟩
    · simpa [phaseBudgetMin, hcut] using phaseBudgetFeasible_two hα₂ hc
    · intro y hy
      have hy₁ : 1 ≤ y := hy.1
      by_cases hylt : y < 2
      · have hyEq : y = 1 := by omega
        have hyOne : phaseBudgetFeasible α c 1 := by simpa [hyEq] using hy
        have : α - 1 ≤ c := (phaseBudgetFeasible_one_iff α c).1 hyOne
        exact False.elim (hcut this)
      · simpa [phaseBudgetMin, hcut] using (show 2 ≤ y by omega)

/-- Paper seed for the binary quantization of the integer phase budget:
    the minimum feasible phase count is `1` exactly above the threshold `α - 1`,
    and otherwise it is `2`.
    cor:conclusion-phase-budget-binary-quantization -/
theorem paper_conclusion_phase_budget_binary_quantization_seeds {α c : ℝ}
    (hα₂ : α < 2) (hc : 0 ≤ c) :
    (phaseBudgetMin α c = 1 ↔ α - 1 ≤ c) ∧
    (phaseBudgetMin α c = 2 ↔ c < α - 1) ∧
    phaseBudgetFeasible α c (phaseBudgetMin α c) ∧
      ∀ {k : ℕ}, phaseBudgetFeasible α c k → phaseBudgetMin α c ≤ k := by
  refine ⟨?_, ?_, phaseBudgetMin_isLeast hα₂ hc⟩
  · by_cases hcut : α - 1 ≤ c <;> simp [phaseBudgetMin, hcut]
  · by_cases hcut : α - 1 ≤ c
    · have : ¬ c < α - 1 := by linarith
      simp [phaseBudgetMin, hcut, this]
    · have : c < α - 1 := by linarith
      simp [phaseBudgetMin, hcut, this]

end Omega.Conclusion
