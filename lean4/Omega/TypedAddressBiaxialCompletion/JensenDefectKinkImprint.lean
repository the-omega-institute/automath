import Omega.TypedAddressBiaxialCompletion.JensenDefectKinkStructure
import Omega.TypedAddressBiaxialCompletion.JensenOffcriticalKinkLocalization

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing composition of the Jensen-defect kink structure with the off-critical
localization package.
    prop:typed-address-biaxial-completion-jensen-defect-kink-imprint -/
theorem paper_typed_address_biaxial_completion_jensen_defect_kink_imprint
    (J : Omega.TypedAddressBiaxialCompletion.JensenDefectKinkProfile)
    (D : Omega.TypedAddressBiaxialCompletion.JensenOffcriticalKinkLocalizationData)
    (r : ℝ) :
    J.slopeJump r = (J.shellMultiplicity r : ℝ) ∧
      J.countJump r = J.shellMultiplicity r ∧
      (J.hasKink r ↔ J.shellMultiplicity r ≠ 0) ∧
      D.zeroAtCompressedPoint ∧ D.kinkJumpLaw ∧ D.horizonDepthFormula := by
  rcases paper_app_jensen_defect_kink_structure J r with ⟨hSlope, hCount, hKink⟩
  rcases paper_app_jensen_offcritical_kink_localization D with
    ⟨hZero, hJump, hDepth⟩
  exact ⟨hSlope, hCount, hKink, hZero, hJump, hDepth⟩

end Omega.TypedAddressBiaxialCompletion
