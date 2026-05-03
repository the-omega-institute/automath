import Omega.Conclusion.FibadicFiniteLayerGcdInvertibilityMobiusInverse

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-fibadic-finite-layer-gcd-kernel-image-spectrum-closedform`. -/
theorem paper_conclusion_fibadic_finite_layer_gcd_kernel_image_spectrum_closedform
    (D : conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data) :
    (∀ d, d ∈ D.active →
        conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar D d =
          D.blockScalar d) ∧
      (∀ d, d ∉ D.active →
        conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar D d =
          1) ∧
      ((D.active.filter fun d => D.blockScalar d ≠ 0).card +
          (D.active.filter fun d => D.blockScalar d = 0).card =
        D.active.card) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar, hd]
  · intro d hd
    simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar, hd]
  · simpa [not_ne_iff] using
      (D.active.card_filter_add_card_filter_not fun d => D.blockScalar d ≠ 0)

end Omega.Conclusion
