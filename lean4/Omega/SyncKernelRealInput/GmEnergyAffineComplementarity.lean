import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-energy-affine-complementarity`. Once the analytic Perron-root
estimates are expressed in logarithmic form, the energy and affine bounds are complementary by
linear arithmetic. -/
theorem paper_gm_energy_affine_complementarity
    (logAlpha logBeta logChi kappa : ℝ)
    (hBeta : logBeta ≤ 3 * logAlpha) (hChi : logChi ≤ logAlpha)
    (hkappa : kappa = logAlpha + 2 * (logAlpha - logChi)) :
    logBeta + 2 * logChi ≤ 6 * logAlpha - kappa ∧ logAlpha ≤ kappa := by
  constructor
  · rw [hkappa]
    linarith
  · rw [hkappa]
    linarith

end Omega.SyncKernelRealInput
