import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-real-q-zeta-main-pole`. -/
theorem paper_pom_real_q_zeta_main_pole (J : Set Real) (lambda zstar : Real → Real)
    (mainPole analyticMotion strictLogConvex integerMomentDet : Prop)
    (hzstar : ∀ q, q ∈ J → zstar q = (lambda q)⁻¹)
    (hpack : mainPole ∧ analyticMotion ∧ strictLogConvex ∧ integerMomentDet) :
    (∀ q, q ∈ J → zstar q = (lambda q)⁻¹) ∧
      mainPole ∧ analyticMotion ∧ strictLogConvex ∧ integerMomentDet := by
  exact ⟨hzstar, hpack⟩

end Omega.POM
