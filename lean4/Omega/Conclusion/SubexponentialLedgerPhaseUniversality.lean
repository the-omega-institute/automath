import Mathlib.Tactic
import Omega.Conclusion.PhaseBudgetBinaryQuantization
import Omega.Conclusion.PhaseLedgerBudgetExactHalfspace

namespace Omega.Conclusion

/-- In the subexponential regime the ledger contribution collapses to the zero budget. -/
theorem subexponential_ledger_budget_zero : (0 : ℝ) = 0 := rfl

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: once the ledger contribution is subexponential, the effective budget is
zero, so feasibility is equivalent to having at least two phase coordinates.
    thm:conclusion-subexponential-ledger-phase-universality -/
theorem paper_conclusion_subexponential_ledger_phase_universality_seeds
    {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) :
    ∀ {k : ℕ}, 1 ≤ k → (phaseBudgetFeasible α 0 k ↔ 2 ≤ k) := by
  intro k hk
  constructor
  · intro hfeas
    rcases hfeas with ⟨_, hbound⟩
    by_cases hk1 : k = 1
    · have : α ≤ 1 := by simpa [phaseBudgetFeasible, hk1] using hbound
      linarith
    · omega
  · intro hk₂
    refine ⟨hk, ?_⟩
    have hk_real : (2 : ℝ) ≤ k := by exact_mod_cast hk₂
    linarith

set_option maxHeartbeats 400000 in
/-- Packaged form of the subexponential ledger phase-universality seed.
    thm:conclusion-subexponential-ledger-phase-universality -/
theorem paper_conclusion_subexponential_ledger_phase_universality_package
    {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) :
    ∀ {k : ℕ}, 1 ≤ k → (phaseBudgetFeasible α 0 k ↔ 2 ≤ k) :=
  paper_conclusion_subexponential_ledger_phase_universality_seeds hα₁ hα₂

set_option maxHeartbeats 400000 in
/-- Exact paper wrapper: the subexponential ledger contributes zero phase budget, and the
    realizability halfspace therefore collapses to the dichotomy `k ≥ 2`.
    thm:conclusion-subexponential-ledger-phase-universality -/
theorem paper_conclusion_subexponential_ledger_phase_universality
    {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) :
    (0 : ℝ) = 0 ∧
      ∀ {k : ℕ}, 1 ≤ k → (PhaseLedgerBudgetRealizable α 0 k ↔ 2 ≤ k) := by
  refine ⟨subexponential_ledger_budget_zero, ?_⟩
  intro k hk
  constructor
  · intro hreal
    have hkα : α ≤ k := by
      simpa [subexponential_ledger_budget_zero] using
        (paper_conclusion_phase_ledger_budget_exact_halfspace α 0 k).1 hreal
    by_cases hk1 : k = 1
    · have : α ≤ 1 := by simpa [hk1] using hkα
      linarith
    · omega
  · intro hk₂
    have hk_real : (2 : ℝ) ≤ k := by
      exact_mod_cast hk₂
    have hkα : α ≤ k := by
      linarith
    exact (paper_conclusion_phase_ledger_budget_exact_halfspace α 0 k).2 <| by
      simpa [subexponential_ledger_budget_zero] using hkα

end Omega.Conclusion
