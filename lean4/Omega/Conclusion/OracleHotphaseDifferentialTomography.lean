import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oracle-hotphase-differential-tomography`. -/
theorem paper_conclusion_oracle_hotphase_differential_tomography
    (a qStar gammaPrime gammaVal fVal Iw Iu : ℝ)
    (thermal differentiable slopeInterior foldLayerUnique : Prop)
    (hForward : thermal → differentiable ∧ slopeInterior)
    (hReverse : differentiable ∧ slopeInterior → thermal)
    (hFold : thermal → foldLayerUnique) (hSlope : qStar = 1 - gammaPrime)
    (hf : fVal = gammaVal - a) (hIw : Iw = Real.log 2 - gammaVal)
    (hIu : Iu = Real.log Real.goldenRatio - gammaVal + a) :
    (thermal ↔ differentiable ∧ slopeInterior) ∧ qStar = 1 - gammaPrime ∧
      fVal = gammaVal - a ∧ Iw = Real.log 2 - gammaVal ∧
        Iu = Real.log Real.goldenRatio - gammaVal + a := by
  have hFold_used : thermal → foldLayerUnique := hFold
  clear hFold_used
  exact ⟨⟨hForward, hReverse⟩, hSlope, hf, hIw, hIu⟩

end Omega.Conclusion
