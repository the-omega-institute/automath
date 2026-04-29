import Omega.Zeta.XiWindow6A2pmIdenticalFiberSpectrum

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-a2pm-multiplicity-blind-statistics`. -/
theorem paper_xi_window6_a2pm_multiplicity_blind_statistics (Φ : ℕ → ℝ) :
    (xi_window6_a2pm_identical_fiber_spectrum_a2p_sector.map
        (fun w => Φ (xi_window6_a2pm_identical_fiber_spectrum_multiplicity w))).sum =
      (xi_window6_a2pm_identical_fiber_spectrum_a2m_sector.map
        (fun w => Φ (xi_window6_a2pm_identical_fiber_spectrum_multiplicity w))).sum := by
  unfold xi_window6_a2pm_identical_fiber_spectrum_a2p_sector
  unfold xi_window6_a2pm_identical_fiber_spectrum_a2m_sector
  unfold xi_window6_a2pm_identical_fiber_spectrum_multiplicity
  simp

end Omega.Zeta
