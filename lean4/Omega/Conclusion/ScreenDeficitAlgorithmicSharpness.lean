import Mathlib
import Omega.Conclusion.ScreenMaxConditionalComplexityEqualsRank

namespace Omega.Conclusion

/-- Concrete audit datum for the exact screen-deficit splitting and its sharp residual-bit count. -/
structure ScreenDeficitAuditDatum where
  V : Type
  instVAddCommGroup : AddCommGroup V
  instVModule : Module (ZMod 2) V
  instVFiniteDimensional : FiniteDimensional (ZMod 2) V
  W : Type
  instWAddCommGroup : AddCommGroup W
  instWModule : Module (ZMod 2) W
  f : V →ₗ[ZMod 2] W

namespace ScreenDeficitAuditDatum

/-- Sharp algorithmic deficit means that the exact kernel splitting exhibits an `r`-bit residual
fiber and the maximal conditional complexity over that fiber is exactly `r`. -/
def HasSharpAlgorithmicDeficit (D : ScreenDeficitAuditDatum) : Prop :=
  let _ : AddCommGroup D.V := D.instVAddCommGroup
  let _ : Module (ZMod 2) D.V := D.instVModule
  let _ : FiniteDimensional (ZMod 2) D.V := D.instVFiniteDimensional
  let _ : AddCommGroup D.W := D.instWAddCommGroup
  let _ : Module (ZMod 2) D.W := D.instWModule
  ∃ r : Nat,
    Nonempty (D.V ≃ₗ[ZMod 2] (LinearMap.range D.f × (Fin r → ZMod 2))) ∧
      screenMaxConditionalComplexity r = r

end ScreenDeficitAuditDatum

open ScreenDeficitAuditDatum

/-- Paper label: `thm:conclusion-screen-deficit-algorithmic-sharpness`. The screen-kernel
splitting identifies the residual fiber with an `r`-bit coordinate cube, and the previously
verified maximal conditional complexity computation shows that this `r`-bit deficit is sharp. -/
theorem paper_conclusion_screen_deficit_algorithmic_sharpness
    (D : ScreenDeficitAuditDatum) : D.HasSharpAlgorithmicDeficit := by
  let _ : AddCommGroup D.V := D.instVAddCommGroup
  let _ : Module (ZMod 2) D.V := D.instVModule
  let _ : FiniteDimensional (ZMod 2) D.V := D.instVFiniteDimensional
  let _ : AddCommGroup D.W := D.instWAddCommGroup
  let _ : Module (ZMod 2) D.W := D.instWModule
  simpa [ScreenDeficitAuditDatum.HasSharpAlgorithmicDeficit] using
    paper_conclusion_screen_max_conditional_complexity_equals_rank D.f

end Omega.Conclusion
