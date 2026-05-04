import Omega.CircleDimension.PoissonBivariateFdivFourthOrderConstant

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-bivariate-fdiv-sharp`. -/
theorem paper_conclusion_poisson_bivariate_fdiv_sharp (fpp A B : ℝ) :
    Omega.CircleDimension.PoissonBivariateFdivFourthOrderConstant fpp A 0 B := by
  simpa using
    (Omega.CircleDimension.paper_cdim_poisson_bivariate_fdiv_fourth_order_constant fpp A 0 B)

end Omega.Conclusion
