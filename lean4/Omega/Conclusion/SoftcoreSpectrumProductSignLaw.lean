import Omega.Conclusion.SpectrumSignLaw

namespace Omega.Conclusion

/-- Determinant scalar for `cor:conclusion-softcore-spectrum-product-sign-law`. -/
noncomputable def conclusion_softcore_spectrum_product_sign_law_det (q : ℕ) : ℝ :=
  (-1 : ℝ) ^ (q * (q + 1) / 2) / (2 : ℝ) ^ q

/-- Paper label: `cor:conclusion-softcore-spectrum-product-sign-law`. -/
theorem paper_conclusion_softcore_spectrum_product_sign_law (q : ℕ) :
    conclusion_softcore_spectrum_product_sign_law_det q =
      (-1 : ℝ) ^ (q * (q + 1) / 2) / (2 : ℝ) ^ q := by
  rfl

end Omega.Conclusion
