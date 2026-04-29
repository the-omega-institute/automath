import Omega.SyncKernelWeighted.PressureUnitRootModulusThreshold

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper label: `cor:sync-kernel-unit-root-twist-threshold`.
With the audited radius `R_θ = π / 3`, the strict cutoff `2π / p < R_θ` is equivalent to
`p > 6`. -/
theorem paper_sync_kernel_unit_root_twist_threshold (D : PressureAnalyticRadiusData) :
    D.R_theta = Real.pi / 3 ∧ ∀ p : ℕ, 5 ≤ p → (2 * Real.pi / p < D.R_theta ↔ 6 < p) := by
  rcases paper_pressure_unit_root_modulus_threshold D with ⟨hR, hthreshold⟩
  refine ⟨hR, ?_⟩
  intro p hp
  constructor
  · intro hlt
    have hnot : ¬ D.R_theta ≤ 2 * Real.pi / p := not_le.mpr hlt
    have hpnot : ¬ p ≤ 6 := by
      intro hp6
      exact hnot ((hthreshold p hp).2 hp6)
    omega
  · intro hp6
    have hge7 : 7 ≤ p := by omega
    have hmono : 2 * Real.pi / p ≤ 2 * Real.pi / 7 := by
      simpa using pressure_two_pi_div_antitone (p := 7) (q := p) (by norm_num) hge7
    calc
      2 * Real.pi / p ≤ 2 * Real.pi / 7 := hmono
      _ < Real.pi / 3 := pressure_two_pi_div_seven_lt_pi_div_three
      _ = D.R_theta := hR.symm

end

end Omega.SyncKernelWeighted
