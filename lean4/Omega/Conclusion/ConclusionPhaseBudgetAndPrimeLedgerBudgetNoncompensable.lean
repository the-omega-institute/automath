import Mathlib.Tactic

namespace Omega.Conclusion

/-- A constant invariant on finite supports cannot recover the support injectively.
    cor:conclusion-phase-budget-and-prime-ledger-budget-noncompensable -/
theorem paper_conclusion_phase_budget_and_prime_ledger_budget_noncompensable
    (I : Finset ℕ → ℕ)
    (hI : ∀ S T : Finset ℕ, I S = I T) :
    ¬ Function.Injective I := by
  intro hInjective
  have hEq : (∅ : Finset ℕ) = {2} := hInjective (hI ∅ {2})
  have hMem : 2 ∈ (∅ : Finset ℕ) := by
    simp [hEq]
  simp at hMem

end Omega.Conclusion
