import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite counting core for the visible-phase/register budget inequality.
    thm:conclusion-rate-cdim-budget-inequality -/
theorem paper_conclusion_rate_cdim_budget_inequality
    (Micro Stable Reg : ℕ → Type*)
    (hMicro : ∀ m, Fintype (Micro m))
    (hStable : ∀ m, Fintype (Stable m))
    (hReg : ∀ m, Fintype (Reg m))
    (k : ℕ)
    (hE : ∀ m, ∃ E : Micro m → ((Fin k → Stable m) × Reg m), Function.Injective E) :
    ∀ m,
      @Fintype.card (Micro m) (hMicro m) ≤
        (@Fintype.card (Stable m) (hStable m)) ^ k *
          @Fintype.card (Reg m) (hReg m) := by
  intro m
  classical
  rcases hE m with ⟨E, hEinj⟩
  simpa [Fintype.card_prod, Fintype.card_fun] using Fintype.card_le_of_injective E hEinj

end Omega.Conclusion
