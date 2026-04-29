import Omega.POM.ParryOnesCLT

namespace Omega.POM

/-- Concrete local-limit package for the uniform legal-word windows in the golden-mean shift.
The limiting two-point cylinder masses and covariances are the explicit Parry formulas already
recorded in the audited two-point and CLT wrappers. -/
def pom_unif_xn_local_limit_parry_statement : Prop :=
  (∀ k : ℕ,
    parryJointOneOne k =
      (let pi1 : Real := 1 / (Real.goldenRatio ^ 2 + 1)
       let pi0 : Real := Real.goldenRatio ^ 2 / (Real.goldenRatio ^ 2 + 1)
       let lam2 : Real := -(1 / (Real.goldenRatio ^ 2))
       pi1 ^ 2 + pi0 * pi1 * lam2 ^ k)) ∧
    (∀ k : ℕ,
      parryCovariance k =
        (let pi1 : Real := 1 / (Real.goldenRatio ^ 2 + 1)
         let pi0 : Real := Real.goldenRatio ^ 2 / (Real.goldenRatio ^ 2 + 1)
         let lam2 : Real := -(1 / (Real.goldenRatio ^ 2))
         pi0 * pi1 * lam2 ^ k)) ∧
    pom_parry_ones_clt_statement

/-- Paper label: `prop:pom-unif-xn-local-limit-parry`. The explicit Parry two-point law supplies
the local two-cylinder limit for the uniform legal-word model, and the one-marginal fluctuation
package is the already audited Parry-ones CLT statement. -/
theorem paper_pom_unif_xn_local_limit_parry : pom_unif_xn_local_limit_parry_statement := by
  refine ⟨?_, ?_, paper_pom_parry_ones_clt⟩
  · intro k
    exact (paper_pom_parry_two_point_alternating k).1
  · intro k
    exact (paper_pom_parry_two_point_alternating k).2

end Omega.POM
