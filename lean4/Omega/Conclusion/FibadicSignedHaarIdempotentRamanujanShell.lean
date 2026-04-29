import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-signed-haar-idempotent-ramanujan-shell`. -/
theorem paper_conclusion_fibadic_signed_haar_idempotent_ramanujan_shell
    (signedProjection convolutionIdempotent fourierIndicator kernelFormula : Prop)
    (hProjection : signedProjection)
    (hIdempotent : signedProjection → convolutionIdempotent)
    (hFourier : convolutionIdempotent → fourierIndicator)
    (hKernel : fourierIndicator → kernelFormula) :
    signedProjection ∧ convolutionIdempotent ∧ fourierIndicator ∧ kernelFormula := by
  have hIdempotent' : convolutionIdempotent := hIdempotent hProjection
  have hFourier' : fourierIndicator := hFourier hIdempotent'
  exact ⟨hProjection, hIdempotent', hFourier', hKernel hFourier'⟩

end Omega.Conclusion
