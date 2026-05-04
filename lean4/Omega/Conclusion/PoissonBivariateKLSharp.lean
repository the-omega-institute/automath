import Omega.CircleDimension.PoissonBivariateFdivFourthOrderConstant

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-bivariate-kl-sharp`. -/
theorem paper_conclusion_poisson_bivariate_kl_sharp (A B : ℝ) :
    Omega.CircleDimension.PoissonBivariateFdivFourthOrderConstant 1 A 0 B := by
  simpa using
    (Omega.CircleDimension.paper_cdim_poisson_bivariate_fdiv_fourth_order_constant 1 A 0 B)

end Omega.Conclusion
