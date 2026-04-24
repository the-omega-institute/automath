import Mathlib.Tactic
import Omega.POM.KLLedgerTelescope

namespace Omega.POM

/-- Rewriting the KL ledger telescope isolates the residual sum as the exact difference of the
endpoint KL terms.
    cor:pom-ledger-residual-telescoping -/
theorem paper_pom_ledger_residual_telescoping (R : ResolutionReflectorData) {M : ℕ} (hM : 1 ≤ M)
    (μ : R.Distrib M) :
    (Finset.Icc 2 M).sum (fun m => R.kl (M := M) (R.reflect m μ) (R.reflect (m - 1) μ)) =
      R.kl (M := M) μ (R.reflect 1 μ) - R.kl (M := M) μ (R.reflect M μ) := by
  have htel := paper_pom_kl_ledger_telescope (R := R) (M := M) hM μ
  linarith

end Omega.POM
