import Omega.Zeta.XiPwTypeSafetyNull
import Omega.Zeta.XiUniqueContinuousTransverseRegister

namespace Omega.Zeta

/-- Paper label: `thm:xi-pw-no-continuous-hair`. -/
theorem paper_xi_pw_no_continuous_hair (D : Omega.Zeta.XiPwTypeSafetyNullData)
    (register : ℝ × ℝ → ℝ)
    (hphase : ∀ radius phase1 phase2, register (radius, phase1) = register (radius, phase2))
    (hmono : StrictMono (fun radius => register (radius, 0))) :
    (D.modeAxisCompleteness ↔ D.hankelRanksUniformlyBounded) ∧
      Omega.Zeta.xiFactorsThroughRadius register ∧
      Omega.Zeta.xiUniqueUpToMonotoneReparam register := by
  have hBound := paper_xi_completeness_iff_hankel_bounded D
  have hRegister := paper_xi_unique_continuous_transverse_register register hphase hmono
  exact ⟨hBound, hRegister.1, hRegister.2⟩

end Omega.Zeta
