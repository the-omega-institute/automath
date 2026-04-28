import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9ze-index-spectral-radius-consistency`. -/
theorem paper_xi_time_part9ze_index_spectral_radius_consistency
    (ppIndex rhoC rhoJ : ℝ) (hC : rhoC = 4) (hJ : rhoJ = rhoC) (hInd : ppIndex = 4) :
    ppIndex = rhoC ∧ rhoC = rhoJ ∧ rhoJ = 4 := by
  refine ⟨hInd.trans hC.symm, hJ.symm, hJ.trans hC⟩

end Omega.Zeta
