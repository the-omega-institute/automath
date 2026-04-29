import Omega.Zeta.XiCdimLocalizationSolenoidContinuousHomClassification

namespace Omega.Zeta

/-- Paper-facing wrapper for
`thm:xi-time-part60f2-countable-solenoid-morphism-classification`. In the chapter-local
localized-solenoid surrogate, continuous morphisms `Σ_T → Σ_S` are classified by the existing
localized cross-hom package with reversed dual arguments. -/
def xi_time_part60f2_countable_solenoid_morphism_classification_statement : Prop :=
  ∀ S T : Finset ℕ, XiCdimLocalizationSolenoidContinuousHomClassification T S

theorem paper_xi_time_part60f2_countable_solenoid_morphism_classification :
    xi_time_part60f2_countable_solenoid_morphism_classification_statement := by
  intro S T
  exact paper_xi_cdim_localization_solenoid_continuous_hom_classification T S

end Omega.Zeta
