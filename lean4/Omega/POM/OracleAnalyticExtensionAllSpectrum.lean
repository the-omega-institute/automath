import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.OracleSigmaDeterminesTauOn01

namespace Omega.POM

/-- cor:pom-oracle-analytic-extension-all-spectrum -/
theorem paper_pom_oracle_analytic_extension_all_spectrum
    (tau1 tau2 Lambda1 Lambda2 : ℝ → ℝ) (U : Set ℝ)
    (hTau1 : tau1 1 = Real.log 2)
    (hTau2 : tau2 1 = Real.log 2)
    (hLambda1 : ∀ q ∈ Set.Icc (0 : ℝ) 1, Lambda1 (q - 1) = tau1 q - tau1 1)
    (hLambda2 : ∀ q ∈ Set.Icc (0 : ℝ) 1, Lambda2 (q - 1) = tau2 q - tau2 1)
    (hSame : ∀ θ ∈ Set.Icc (-1 : ℝ) 0, Lambda1 θ = Lambda2 θ)
    (hAnalyticUnique :
      (∀ q ∈ Set.Icc (0 : ℝ) 1, tau1 q = tau2 q) → ∀ q ∈ U, tau1 q = tau2 q) :
    ∀ q ∈ U, tau1 q = tau2 q := by
  exact hAnalyticUnique
    (paper_pom_oracle_sigma_determines_tau_on_01 tau1 tau2 Lambda1 Lambda2 hTau1 hTau2
      hLambda1 hLambda2 hSame)

end Omega.POM
