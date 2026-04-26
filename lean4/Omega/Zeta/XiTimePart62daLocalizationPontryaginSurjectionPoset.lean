import Omega.CircleDimension.SolenoidOverTMorphismClassification
import Omega.Zeta.XiCdimLocalizationQuotientSolenoidSurjections

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62da-localization-pontryagin-surjection-poset`. The compact-side
Pontryagin surjection order is exactly the inclusion order on the finite prime supports, and once
`S ⊆ T` the quotient-solenoid package supplies the explicit finite-prime kernel. -/
theorem paper_xi_time_part62da_localization_pontryagin_surjection_poset
    (D : Omega.CircleDimension.LocalizedGsEmbeddingOrderData) :
    (Omega.CircleDimension.LocalizedGsEmbeddingOrderData.compatibleDualSurjection D.S D.T ↔
      D.S ⊆ D.T) ∧
      (D.S ⊆ D.T →
        xiSolenoidSurjectionKernel D.S D.T 1 1 =
          List.replicate (xiLocalizationQuotientPrueferRank D.S D.T) 1) := by
  have hOrder := Omega.CircleDimension.paper_cdim_solenoid_over_t_morphism_classification D
  refine ⟨hOrder.1, ?_⟩
  intro hST
  rcases paper_xi_cdim_localization_quotient_solenoid_surjections D.S D.T hST 1 1 with
    ⟨_, _, _, _, hKernel⟩
  simp [xiSolenoidSurjectionKernel, xiLocalizationQuotientPrueferRank] at hKernel ⊢

end Omega.Zeta
