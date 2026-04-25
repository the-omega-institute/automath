import Omega.StatisticalStability.PeriodicDirichletSeriesHurwitzDecomposition

open scoped BigOperators
open Omega.StatisticalStability

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-periodic-dirichlet-shadow-hurwitz-finite-closure`. A finite
periodic Dirichlet shadow with a common Hurwitz prefactor factors through the residue sum. -/
theorem paper_conclusion_periodic_dirichlet_shadow_hurwitz_finite_closure
    (d : Nat) (kappa hurwitz : Nat -> Complex) (dnegS Z : Complex)
    (hsplit :
      Z = Finset.sum (periodicDirichletResidues d) (fun r => kappa r * (dnegS * hurwitz r))) :
    Z = dnegS * Finset.sum (periodicDirichletResidues d) (fun r => kappa r * hurwitz r) := by
  rw [hsplit, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  ring

end Omega.Conclusion
