import Omega.Zeta.XiDefectEntropyMassPeakDecoupling
import Omega.Zeta.XiHankelHsEnergyClosedFormMassEnergy

namespace Omega.Zeta

/-- Paper label: `cor:xi-peak-vs-energy-audit-independence`. -/
theorem paper_xi_peak_vs_energy_audit_independence
    (κ : ℕ) (S : ℝ) (a z : ℂ) (hκ : 0 < κ) (hS0 : 0 < S) (hSκ : S < κ) (hz : ‖z‖ < 1) :
    xiPeakCompressibility κ S ≤ 8 / (κ + 1 : ℝ) ∧
      xiHankelSingleModeMass a ≤ xiHankelSingleModeHsEnergyClosedForm a z := by
  rcases paper_xi_hankel_hs_energy_closed_form_mass_energy a z hz with ⟨_, _, _, hmass⟩
  exact ⟨paper_xi_defect_entropy_mass_peak_decoupling κ S hκ hS0 hSκ, hmass⟩

end Omega.Zeta
