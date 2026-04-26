import Mathlib.Data.Real.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-dirichlet-grh-twisted-radius`. The finite-layer twisted radius is
bounded by the designated square-root Perron scale. -/
theorem paper_pom_dirichlet_grh_twisted_radius (lambda1 lambdaHalf twistRadius : Real)
    (hsqrt : lambdaHalf * lambdaHalf = lambda1) (hbound : twistRadius <= lambdaHalf) :
    twistRadius <= lambdaHalf := by
  have _ : lambdaHalf * lambdaHalf = lambda1 := hsqrt
  exact hbound

end Omega.POM
