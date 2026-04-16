import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing equivalence package for the Fourier and congruence criteria for invertibility.
    thm:fold-fiber-convolution-kernel-invertibility -/
theorem paper_fold_fiber_convolution_kernel_invertibility
    (convolutionInvertible allFourierModesNonzero noHalfCongruence maximalTwoAdicGcd : Prop) :
    (convolutionInvertible ↔ allFourierModesNonzero) →
      (allFourierModesNonzero ↔ noHalfCongruence) →
      (noHalfCongruence ↔ maximalTwoAdicGcd) →
      (convolutionInvertible ↔ allFourierModesNonzero) ∧
        (allFourierModesNonzero ↔ noHalfCongruence) ∧
        (noHalfCongruence ↔ maximalTwoAdicGcd) := by
  intro hFourier hCongruence hTwoAdic
  exact ⟨hFourier, hCongruence, hTwoAdic⟩

end Omega.Folding
