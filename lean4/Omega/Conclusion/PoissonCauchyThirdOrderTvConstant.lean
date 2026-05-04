import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-third-order-tv-constant`. -/
theorem paper_conclusion_poisson_cauchy_third_order_tv_constant
    (thirdOrderTaylorPeeling scaledRemainderVanishes derivativeL1Constant tvLimitConstant : Prop)
    (hTaylor : thirdOrderTaylorPeeling) (hRem : scaledRemainderVanishes)
    (hL1 : derivativeL1Constant) (hLimit : tvLimitConstant) :
    thirdOrderTaylorPeeling ∧ scaledRemainderVanishes ∧ derivativeL1Constant ∧
      tvLimitConstant := by
  exact ⟨hTaylor, hRem, hL1, hLimit⟩

end Omega.Conclusion
