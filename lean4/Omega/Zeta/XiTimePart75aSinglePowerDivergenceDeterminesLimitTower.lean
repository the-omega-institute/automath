import Omega.Conclusion.Chi2RecoversFullPowerDivergenceFamily

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part75a-single-power-divergence-determines-limit-tower`. -/
theorem paper_xi_time_part75a_single_power_divergence_determines_limit_tower
    (D : Omega.Conclusion.conclusion_chi2_recovers_full_power_divergence_family_data) :
    D.conclusion_chi2_recovers_full_power_divergence_family_phi_recovered ∧
      D.conclusion_chi2_recovers_full_power_divergence_family_full_family_recovered := by
  rcases Omega.Conclusion.paper_conclusion_chi2_recovers_full_power_divergence_family D with
    ⟨_, hphi, hfamily⟩
  exact ⟨hphi, hfamily⟩

end Omega.Zeta
