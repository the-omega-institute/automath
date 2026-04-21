import Omega.Zeta.XiFoldLocalInformationDensityFirstOrderDiscreteLaw

namespace Omega.Zeta

/-- Concrete package for the escort two-state limit law in part `54ab`. -/
structure XiEscortTwoStateDatum where
  limitLaw : Bool → ℝ
  scaledMean : ℝ
  scaledVariance : ℝ
  limitLaw_eq : limitLaw = xiFoldBernoulliLaw
  scaledMean_eq : scaledMean = xiFoldFirstMoment
  scaledVariance_eq : scaledVariance = xiFoldSecondMoment

namespace XiEscortTwoStateDatum

/-- The two-state limit law records the limiting Bernoulli law together with its first two centered
scaled moments. -/
def HasTwoStateLimitLaw (D : XiEscortTwoStateDatum) : Prop :=
  D.limitLaw = xiFoldBernoulliLaw ∧
    D.scaledMean = xiFoldFirstMoment ∧
    D.scaledVariance = xiFoldSecondMoment

end XiEscortTwoStateDatum

open XiEscortTwoStateDatum

/-- Paper label: `thm:xi-time-part54ab-escort-two-state-limit-law`. This is the concrete
two-state Bernoulli limit package obtained by reusing the already verified first-order
local-information-density law. -/
theorem paper_xi_time_part54ab_escort_two_state_limit_law
    (D : XiEscortTwoStateDatum) : D.HasTwoStateLimitLaw := by
  let D' : XiFoldLocalInformationDensityData :=
    { limitLaw := D.limitLaw
      scaledMean := D.scaledMean
      scaledVariance := D.scaledVariance
      limitLaw_eq := D.limitLaw_eq
      scaledMean_eq := D.scaledMean_eq
      scaledVariance_eq := D.scaledVariance_eq }
  simpa [XiEscortTwoStateDatum.HasTwoStateLimitLaw] using
    paper_xi_fold_local_information_density_first_order_discrete_law D'

end Omega.Zeta
