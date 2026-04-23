import Mathlib.Tactic
import Omega.Conclusion.AffineRegisterBudget

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-rate-cdim-achievability`. The publication-facing achievability
statement is exactly the conjunction of the two explicit injection constructions already proved
for the zero-ledger two-phase model and the minimal-ledger one-phase model. -/
theorem paper_conclusion_rate_cdim_achievability (m : ℕ) :
    (2 ^ m ≤ Fintype.card (X m) ^ 2 → ∃ f : Fin (2 ^ m) → X m × X m, Function.Injective f) ∧
      (∃ f : Fin (2 ^ m) → X m ×
        Fin ((2 ^ m + Fintype.card (X m) - 1) / Fintype.card (X m)), Function.Injective f) := by
  constructor
  · intro hcap
    exact twoPhase_zeroLedger_achievable m hcap
  · exact onePhase_minLedger_achievable m

end Omega.Conclusion
