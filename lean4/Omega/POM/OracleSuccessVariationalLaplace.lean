import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.POM

/-- Paper label: `thm:pom-oracle-success-variational-laplace`. -/
theorem paper_pom_oracle_success_variational_laplace
    (Sigma branch left right : Real -> Real)
    (hVaradhan : forall a, 0 <= a -> a <= Real.log 2 -> Sigma a = branch a)
    (hSplit : forall a, 0 <= a -> a <= Real.log 2 -> branch a = max (left a) (right a)) :
    forall a, 0 <= a -> a <= Real.log 2 -> Sigma a = max (left a) (right a) := by
  intro a ha0 ha1
  rw [hVaradhan a ha0 ha1, hSplit a ha0 ha1]

end Omega.POM
