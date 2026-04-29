import Omega.DerivedConsequences.DerivedFiniteAnomalyLedgerNoFaithfulMultiplicativeSkeleton
import Omega.GU.TerminalCutProjectToFoldHist

namespace Omega.DerivedConsequences

/-- Paper label: `cor:derived-parity-complete-not-multiplicative-faithful`. The audited
window-`6` parity-complete ledger has the concrete carrier size `|X_6| = 21`, and any additive
multiplicative anomaly ledger still fails to be faithful. -/
theorem paper_derived_parity_complete_not_multiplicative_faithful
    (e : ℕ → ℤ)
    (hmul : ∀ a b : ℕ, 1 <= a → 1 <= b → e (a * b) = e a + e b) :
    Omega.GU.terminalCutProjectWindow6Invariant ∧ ¬ Function.Injective e := by
  refine ⟨Omega.GU.paper_terminal_cut_project_to_fold_hist.2, ?_⟩
  intro hinj
  exact paper_derived_finite_anomaly_ledger_no_faithful_multiplicative_skeleton e hmul hinj

end Omega.DerivedConsequences
