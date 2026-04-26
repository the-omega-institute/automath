import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.JensenOffcriticalKinkLocalization

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete finite-sampling data for the Jensen kink undetectability threshold. The finite sample
grid sits below a common cutoff, and that cutoff lies strictly below the true kink radius coming
from the off-critical localization package. -/
structure app_jensen_kink_undetectable_threshold_data where
  localizationData : JensenOffcriticalKinkLocalizationData
  sampledRadii : Finset ℝ
  sampleCutoff : ℝ
  sampleRadius_le_cutoff : ∀ ρ ∈ sampledRadii, ρ ≤ sampleCutoff
  cutoff_lt_kink : sampleCutoff < localizationData.kinkRadius

/-- Every sampled radius stays below the true kink radius. -/
def app_jensen_kink_undetectable_threshold_sampleBlindness
    (D : app_jensen_kink_undetectable_threshold_data) : Prop :=
  ∀ ρ ∈ D.sampledRadii, ρ < D.localizationData.kinkRadius

/-- Paper-facing finite-sampling blindness package: the off-critical zero/kink/horizon data hold,
every sampled radius stays below the true kink radius, and consequently no sampled radius reaches
the kink layer. -/
def app_jensen_kink_undetectable_threshold_statement
    (D : app_jensen_kink_undetectable_threshold_data) : Prop :=
  D.localizationData.zeroAtCompressedPoint ∧
    D.localizationData.kinkJumpLaw ∧
    D.localizationData.horizonDepthFormula ∧
    app_jensen_kink_undetectable_threshold_sampleBlindness D ∧
    ∀ ρ ∈ D.sampledRadii, ¬ D.localizationData.kinkRadius ≤ ρ

/-- Paper label: `cor:app-jensen-kink-undetectable-threshold`. -/
theorem paper_app_jensen_kink_undetectable_threshold
    (D : app_jensen_kink_undetectable_threshold_data) :
    app_jensen_kink_undetectable_threshold_statement D := by
  rcases paper_app_jensen_offcritical_kink_localization D.localizationData with
    ⟨hZero, hJump, hDepth⟩
  refine ⟨hZero, hJump, hDepth, ?_, ?_⟩
  · intro ρ hρ
    exact lt_of_le_of_lt (D.sampleRadius_le_cutoff ρ hρ) D.cutoff_lt_kink
  · intro ρ hρ hreach
    have hlt : ρ < D.localizationData.kinkRadius :=
      lt_of_le_of_lt (D.sampleRadius_le_cutoff ρ hρ) D.cutoff_lt_kink
    exact (not_le_of_gt hlt) hreach

end Omega.TypedAddressBiaxialCompletion
