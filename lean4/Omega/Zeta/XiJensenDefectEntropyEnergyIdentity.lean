import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-jensen-defect-entropy-energy-identity`. -/
theorem paper_xi_jensen_defect_entropy_energy_identity {D logZ logF0 KL : ℝ}
    (h : 2 * D = logZ - KL - 2 * logF0) :
    D = (1 / 2) * (logZ - 2 * logF0) - (1 / 2) * KL := by
  linarith

end Omega.Zeta
