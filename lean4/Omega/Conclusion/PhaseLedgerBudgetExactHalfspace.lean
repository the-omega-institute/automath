import Mathlib.Tactic
import Omega.Conclusion.AffineRegisterBudget
import Omega.Conclusion.PhaseBudgetBinaryQuantization

namespace Omega.Conclusion

/-- A paper-facing register family witness for `k` phase coordinates. -/
def PhaseLedgerRegisterFamily (k : ℕ) : Prop :=
  ∃ f : Fin k → Fin k, Function.Injective f

theorem phaseLedgerRegisterFamily_self (k : ℕ) : PhaseLedgerRegisterFamily k := by
  exact ⟨id, fun _ _ h => h⟩

/-- Realizability of the phase-ledger budget region. For `k = 0` this is the degenerate boundary
    case `α ≤ c`; for `k ≥ 1` it is the existing halfspace predicate together with a concrete
    register-family witness. -/
def PhaseLedgerBudgetRealizable (α c : ℝ) (k : ℕ) : Prop :=
  if _hk : k = 0 then α ≤ c ∧ PhaseLedgerRegisterFamily k
  else phaseBudgetFeasible α c k ∧ PhaseLedgerRegisterFamily k

/-- The paper realizability region is exactly the halfspace `α ≤ k + c`.
    thm:conclusion-phase-ledger-budget-exact-halfspace -/
theorem paper_conclusion_phase_ledger_budget_exact_halfspace (α c : ℝ) (k : ℕ) :
    PhaseLedgerBudgetRealizable α c k ↔ α ≤ k + c := by
  cases k with
  | zero =>
      simp [PhaseLedgerBudgetRealizable, phaseLedgerRegisterFamily_self]
  | succ k =>
      cases k with
      | zero =>
          constructor
          · intro h
            exact h.1.2
          · intro h
            have h' : α ≤ c + 1 := by
              simpa [add_comm, add_left_comm, add_assoc] using h
            have hcut : α - 1 ≤ c := by
              linarith
            refine ⟨(phaseBudgetFeasible_one_iff α c).2 hcut, phaseLedgerRegisterFamily_self 1⟩
      | succ k =>
          constructor
          · intro h
            exact h.1.2
          · intro h
            refine ⟨?_, phaseLedgerRegisterFamily_self _⟩
            exact ⟨by omega, h⟩

end Omega.Conclusion
