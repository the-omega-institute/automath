import Omega.Conclusion.PoissonCauchyTVSecondOrderNorm

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-poisson-bivariate-tv-sharp`. -/
theorem paper_conclusion_poisson_bivariate_tv_sharp
    (D : Omega.Conclusion.conclusion_poisson_cauchy_tv_second_order_norm_data) :
    0 ≤ Omega.Conclusion.conclusion_poisson_cauchy_tv_second_order_norm_tv D.A D.B ∧
      Omega.Conclusion.conclusion_poisson_cauchy_tv_second_order_norm_tv D.A 0 =
        Omega.Conclusion.conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * |D.A| ∧
        Omega.Conclusion.conclusion_poisson_cauchy_tv_second_order_norm_tv 0 D.B =
          Omega.Conclusion.conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * |D.B| := by
  have h := Omega.Conclusion.paper_conclusion_poisson_cauchy_tv_second_order_norm D
  exact ⟨h.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end

end Omega.Conclusion
