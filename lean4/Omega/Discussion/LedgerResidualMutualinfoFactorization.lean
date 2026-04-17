import Mathlib.Tactic

namespace Omega.Discussion

/-- Paper wrapper for the residual-KL / mutual-information factorization identity.
    thm:discussion-ledger-residual-mutualinfo-factorization -/
theorem paper_discussion_ledger_residual_mutualinfo_factorization
    (posteriorFactorization : Prop) (expectedResidualKL mutualInfo mixtureKL : ℝ)
    (hPosterior : posteriorFactorization)
    (hKL : expectedResidualKL = mutualInfo + mixtureKL) :
    posteriorFactorization ∧ expectedResidualKL = mutualInfo + mixtureKL := by
  exact ⟨hPosterior, hKL⟩

end Omega.Discussion
