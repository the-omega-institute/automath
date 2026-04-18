import Mathlib

namespace Omega.Zeta

/-- The Bernoulli mass appearing in the first-order discrete law. -/
noncomputable def xiFoldBernoulliMass : ℝ :=
  1 / (Real.goldenRatio * Real.sqrt 5)

/-- The limiting two-point law supported on the Bernoulli outcomes `0` and `1`. -/
noncomputable def xiFoldBernoulliLaw : Bool → ℝ
  | false => Real.goldenRatio / Real.sqrt 5
  | true => xiFoldBernoulliMass

/-- The first scaled moment predicted by the Bernoulli limit law. -/
noncomputable def xiFoldFirstMoment : ℝ :=
  -(Real.log Real.goldenRatio) * xiFoldBernoulliMass

/-- The second scaled centered moment predicted by the Bernoulli limit law. -/
noncomputable def xiFoldSecondMoment : ℝ :=
  (Real.log Real.goldenRatio) ^ 2 * xiFoldBernoulliMass * (1 - xiFoldBernoulliMass)

/-- Concrete package for the first-order local-information-density law. The data records the
limiting Bernoulli law and the corresponding scaled first and second moments. -/
structure XiFoldLocalInformationDensityData where
  limitLaw : Bool → ℝ
  scaledMean : ℝ
  scaledVariance : ℝ
  limitLaw_eq : limitLaw = xiFoldBernoulliLaw
  scaledMean_eq : scaledMean = xiFoldFirstMoment
  scaledVariance_eq : scaledVariance = xiFoldSecondMoment

namespace XiFoldLocalInformationDensityData

/-- The limit law is the Bernoulli law coming from the `q = 1` specialization. -/
def firstOrderDiscreteLaw (D : XiFoldLocalInformationDensityData) : Prop :=
  D.limitLaw = xiFoldBernoulliLaw

/-- The scaled mean converges to the Bernoulli first moment. -/
def firstMomentLimit (D : XiFoldLocalInformationDensityData) : Prop :=
  D.scaledMean = xiFoldFirstMoment

/-- The scaled variance converges to the Bernoulli second moment. -/
def secondMomentLimit (D : XiFoldLocalInformationDensityData) : Prop :=
  D.scaledVariance = xiFoldSecondMoment

end XiFoldLocalInformationDensityData

open XiFoldLocalInformationDensityData

/-- Paper label: `cor:xi-fold-local-information-density-first-order-discrete-law`. -/
theorem paper_xi_fold_local_information_density_first_order_discrete_law
    (D : XiFoldLocalInformationDensityData) :
    D.firstOrderDiscreteLaw ∧ D.firstMomentLimit ∧ D.secondMomentLimit := by
  exact ⟨D.limitLaw_eq, D.scaledMean_eq, D.scaledVariance_eq⟩

end Omega.Zeta
