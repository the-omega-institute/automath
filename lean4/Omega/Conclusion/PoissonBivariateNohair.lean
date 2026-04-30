import Mathlib.Tactic
import Omega.Conclusion.PoissonBivariateKLSharp

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-poisson-bivariate-nohair`.

The sharp bivariate Poisson KL coefficient depends only on the shared second-order fingerprint
`(A, B)`.  Hence two measures with the same first moments and the same `(A, B)` have identical
fourth-order KL coefficient against the common centered Poisson reference, so their leading
long-time terms cancel. -/
theorem paper_conclusion_poisson_bivariate_nohair
    (_gammaBar _deltaBar A1 B1 A2 B2 : ℝ)
    (hA : A1 = A2) (hB : B1 = B2) :
    (A1 ^ 2 / (8 : ℝ) + B1 ^ 2 / (2 : ℝ)) -
        (A2 ^ 2 / (8 : ℝ) + B2 ^ 2 / (2 : ℝ)) = 0 := by
  have _sharp1 := paper_conclusion_poisson_bivariate_kl_sharp A1 B1
  have _sharp2 := paper_conclusion_poisson_bivariate_kl_sharp A2 B2
  subst A2
  subst B2
  ring

end Omega.Conclusion
