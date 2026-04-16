import Mathlib.Tactic
import Omega.Conclusion.PhaseBudgetBinaryQuantization

namespace Omega.Conclusion

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

end Omega.Conclusion
