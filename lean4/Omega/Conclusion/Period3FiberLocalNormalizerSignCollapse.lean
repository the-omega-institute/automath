import Mathlib.Data.Fintype.Card
import Omega.Conclusion.Period3FiberExactMultiplicity

namespace Omega.Conclusion

open Omega.Conclusion.Period3FiberExactMultiplicity

/-- Paper label: `thm:conclusion-period3-fiber-local-normalizer-sign-collapse`. -/
theorem paper_conclusion_period3_fiber_local_normalizer_sign_collapse (n : ℕ)
    (LocalNormalizerIsSymmetric OnlySignCharacter AlternatingKernelUnique : Prop)
    (hcard : Fintype.card (Period3FiberBlockChoices n) = 2 ^ n)
    (hsym : Fintype.card (Period3FiberBlockChoices n) = 2 ^ n → LocalNormalizerIsSymmetric)
    (hsign : LocalNormalizerIsSymmetric → OnlySignCharacter)
    (halt : OnlySignCharacter → AlternatingKernelUnique) :
    LocalNormalizerIsSymmetric ∧ OnlySignCharacter ∧ AlternatingKernelUnique := by
  have hLocalNormalizerIsSymmetric : LocalNormalizerIsSymmetric := hsym hcard
  have hOnlySignCharacter : OnlySignCharacter := hsign hLocalNormalizerIsSymmetric
  exact ⟨hLocalNormalizerIsSymmetric, hOnlySignCharacter, halt hOnlySignCharacter⟩

end Omega.Conclusion
