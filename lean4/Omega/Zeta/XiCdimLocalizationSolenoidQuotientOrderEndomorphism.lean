import Omega.Zeta.LocalizedSolenoidEndomorphismRing
import Omega.Zeta.LocalizedUnitAutomorphismGroupClassification
import Omega.Zeta.XiCdimLocalizationSolenoidContinuousHomClassification

namespace Omega.Zeta

/-- Paper-facing package for the localized-solenoid quotient order. The existence of a compact-side
surjection `Σ_S ↠ Σ_T` is represented on the dual side by an injective cross-hom `G_T ↪ G_S`. The
continuous endomorphism ring and automorphism group are recorded by the existing explicit
localization packages. -/
def xi_cdim_localization_solenoid_quotient_order_endomorphism_statement
    (S T : Finset ℕ) : Prop :=
  ((∃ φ : XiLocalizedSolenoidContinuousHomModel S T, xiLocalizedDiscreteMapInjective φ) ↔ T ⊆ S) ∧
    LocalizedSolenoidEndomorphismRing S ∧
    LocalizedUnitAutomorphismGroupClassification S

/-- The identity scalar on the dual localized group, viewed as the compact-side quotient witness
when `T ⊆ S`. -/
private def xi_cdim_localization_solenoid_quotient_order_endomorphism_identity
    {S T : Finset ℕ} (hTS : T ⊆ S) : XiLocalizedSolenoidContinuousHomModel S T :=
  ⟨
    { toFun := fun z => z
      map_zero' := rfl
      map_add' := by
        intro x y
        rfl },
    by
      intro hMissing
      rcases hMissing with ⟨p, hpT, hpNotS⟩
      exact (hpNotS (hTS hpT)).elim
  ⟩

/-- Paper label: `cor:xi-cdim-localization-solenoid-quotient-order-endomorphism`. -/
theorem paper_xi_cdim_localization_solenoid_quotient_order_endomorphism
    (S T : Finset ℕ) : xi_cdim_localization_solenoid_quotient_order_endomorphism_statement S T := by
  rcases paper_xi_cdim_localization_solenoid_continuous_hom_classification S T with
    ⟨hSubset, hNotSubset, _hInj⟩
  refine ⟨?_, ⟨paper_xi_time_part69d_localized_solenoid_endomorphism_ring S,
    paper_xi_time_part69_localized_unit_automorphism_group_classification S⟩⟩
  constructor
  · rintro ⟨φ, hφinj⟩
    by_contra hTS
    have hzero0 : φ.1 0 = 0 := hNotSubset hTS φ 0
    have hzero1 : φ.1 1 = 0 := hNotSubset hTS φ 1
    have hEq : φ.1 0 = φ.1 1 := by rw [hzero0, hzero1]
    have h01 : (0 : LocalizedIntegerGroup T) = 1 := hφinj hEq
    exact zero_ne_one h01
  · intro hTS
    refine ⟨xi_cdim_localization_solenoid_quotient_order_endomorphism_identity hTS, ?_⟩
    intro x y hxy
    simpa using hxy

end Omega.Zeta
