import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the intrinsic `Y_m` zeta leading pole: the intrinsic zeta radius is
the entropy radius, and the cover-side entropy identity rewrites that radius as the reciprocal of
the Perron root.
    prop:Ym-zeta-leading-pole -/
theorem paper_Ym_zeta_leading_pole (hTop rhoAm RYm : ℝ) (hRho : 0 < rhoAm)
    (hRadius : RYm = Real.exp (-hTop)) (hEntropy : hTop = Real.log rhoAm) :
    RYm = rhoAm⁻¹ := by
  rw [hRadius, hEntropy, Real.exp_neg, Real.exp_log hRho]

end Omega.Folding
