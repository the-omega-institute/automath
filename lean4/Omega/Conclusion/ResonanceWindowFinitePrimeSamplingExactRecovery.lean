import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-resonance-window-finite-prime-sampling-exact-recovery`. -/
theorem paper_conclusion_resonance_window_finite_prime_sampling_exact_recovery
    (correctModPrimeSamples coefficientHeightBound productExceedsTwiceHeight balancedCrtUnique
      fullIntegerPolynomialRecovered : Prop) (hGood : correctModPrimeSamples)
    (hHeight : coefficientHeightBound) (hProduct : productExceedsTwiceHeight)
    (hBalanced :
      correctModPrimeSamples → coefficientHeightBound → productExceedsTwiceHeight →
        balancedCrtUnique)
    (hRecover : balancedCrtUnique → fullIntegerPolynomialRecovered) :
    fullIntegerPolynomialRecovered := by
  exact hRecover (hBalanced hGood hHeight hProduct)

end Omega.Conclusion
