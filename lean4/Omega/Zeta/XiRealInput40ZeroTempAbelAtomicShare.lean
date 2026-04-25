import Mathlib.Tactic

namespace Omega.Zeta

/-- The atomic and core normalized shares add to one after substituting the core split.
    prop:xi-real-input40-zero-temp-abel-atomic-share -/
theorem paper_xi_real_input40_zero_temp_abel_atomic_share
    {logM b logCore atomShare coreShare : Real}
    (hlogM : logM ≠ 0)
    (hcore : logCore = logM - b)
    (hatom : atomShare = b / logM)
    (hcoreShare : coreShare = logCore / logM) :
    atomShare + coreShare = 1 := by
  rw [hatom, hcoreShare, hcore]
  field_simp [hlogM]
  ring

end Omega.Zeta
