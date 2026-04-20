import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete data for the off-critical Jensen kink-localization package. The record keeps the
compressed evaluation point, the multiplicity jump at the kink radius, and the explicit horizon
depth identity. -/
structure JensenOffcriticalKinkLocalizationData where
  offcriticalProfile : ℝ → ℝ
  compressedPoint : ℝ
  kinkRadius : ℝ
  multiplicityBefore : ℕ
  jumpMultiplicity : ℕ
  multiplicityAfter : ℕ
  horizonDepth : ℝ
  baseDepth : ℝ
  zero_certificate : offcriticalProfile compressedPoint = 0
  jump_certificate : multiplicityAfter = multiplicityBefore + jumpMultiplicity
  horizon_certificate :
    horizonDepth = baseDepth + (jumpMultiplicity : ℝ) * kinkRadius

namespace JensenOffcriticalKinkLocalizationData

/-- The compressed off-critical point is a zero of the Jensen profile. -/
def zeroAtCompressedPoint (D : JensenOffcriticalKinkLocalizationData) : Prop :=
  D.offcriticalProfile D.compressedPoint = 0

/-- The multiplicity increases by the stated jump at the kink radius. -/
def kinkJumpLaw (D : JensenOffcriticalKinkLocalizationData) : Prop :=
  D.multiplicityAfter = D.multiplicityBefore + D.jumpMultiplicity

/-- The horizon depth has the explicit affine formula in the kink radius. -/
def horizonDepthFormula (D : JensenOffcriticalKinkLocalizationData) : Prop :=
  D.horizonDepth = D.baseDepth + (D.jumpMultiplicity : ℝ) * D.kinkRadius

end JensenOffcriticalKinkLocalizationData

open JensenOffcriticalKinkLocalizationData

/-- Paper-facing wrapper for the off-critical Jensen kink-localization trichotomy.
    thm:app-jensen-offcritical-kink-localization -/
theorem paper_app_jensen_offcritical_kink_localization (D : JensenOffcriticalKinkLocalizationData) :
    D.zeroAtCompressedPoint ∧ D.kinkJumpLaw ∧ D.horizonDepthFormula := by
  exact ⟨D.zero_certificate, D.jump_certificate, D.horizon_certificate⟩

end Omega.TypedAddressBiaxialCompletion
