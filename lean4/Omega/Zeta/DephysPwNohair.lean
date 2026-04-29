import Omega.Zeta.XiPwNoContinuousHair

namespace Omega.Zeta

/-- Paper label: `thm:dephys-pw-nohair`. -/
theorem paper_dephys_pw_nohair (D : Omega.Zeta.XiPwTypeSafetyNullData)
    (register : ℝ × ℝ → ℝ)
    (hphase : ∀ radius phase1 phase2, register (radius, phase1) = register (radius, phase2))
    (hmono : StrictMono (fun radius => register (radius, 0))) :
    (D.modeAxisCompleteness ↔ D.hankelRanksUniformlyBounded) ∧
      Omega.Zeta.xiFactorsThroughRadius register ∧
      Omega.Zeta.xiUniqueUpToMonotoneReparam register := by
  exact paper_xi_pw_no_continuous_hair D register hphase hmono

end Omega.Zeta
