import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.Window6AuditBudgetSplit
import Omega.TypedAddressBiaxialCompletion.Window6ExplicitFibers

namespace Omega.Zeta

open Omega.TypedAddressBiaxialCompletion

/-- Concrete audit package comparing the exact inversion endpoint against the anomaly-bit census in
the window-`6` ledger. -/
def xi_window6_exact_inversion_vs_anomaly_audit_statement : Prop :=
  window6ReplayBudget = 2 ∧
    Omega.cBinFiberHist 6 2 = 8 ∧
    Omega.cBinFiberHist 6 3 = 4 ∧
    Omega.cBinFiberHist 6 4 = 9 ∧
    window6AnomalyBudget = 21 ∧
    window6ReplayBudget < window6AnomalyBudget ∧
    window6AnomalyBudget - window6ReplayBudget = 19

/-- Paper label: `prop:xi-window6-exact-inversion-vs-anomaly-audit`. The exact inversion endpoint
is the audited `2`-bit replay budget, the window-`6` bin-fold gauge decomposition contributes the
fiber counts `8,4,9`, and the anomaly-bit census is therefore `21`, strictly separated from the
exact inversion axis by `19` bits. -/
theorem paper_xi_window6_exact_inversion_vs_anomaly_audit :
    xi_window6_exact_inversion_vs_anomaly_audit_statement := by
  rcases paper_typed_address_biaxial_completion_window6_audit_budget_split with
    ⟨_, _, _, _, _, hReplay, _, hAnomaly, _, hGap, _⟩
  rcases paper_typed_address_biaxial_completion_window6_explicit_fibers 0 with
    ⟨_, h2, h3, h4, _⟩
  have hsep : window6ReplayBudget < window6AnomalyBudget := by
    rw [hReplay, hAnomaly]
    decide
  exact ⟨hReplay, h2, h3, h4, hAnomaly, hsep, hGap⟩

end Omega.Zeta
