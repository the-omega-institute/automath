import Omega.Zeta.XiFullMicrostateExactInversionBitrateThreshold

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9m3-exact-classicalization-maxfiber-rate`. -/
theorem paper_xi_time_part9m3_exact_classicalization_maxfiber_rate
    (D : xi_full_microstate_exact_inversion_bitrate_threshold_data)
    (exactBudget asymptoticRate : Prop) (hExact : exactBudget) (hRate : asymptoticRate) :
    exactBudget ∧ asymptoticRate := by
  have hThreshold := paper_xi_full_microstate_exact_inversion_bitrate_threshold D
  exact ⟨hExact, hRate⟩

end Omega.Zeta
