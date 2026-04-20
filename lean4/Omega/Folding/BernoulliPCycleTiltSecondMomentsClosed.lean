import Mathlib.Tactic

namespace Omega.Folding

/-- Closed-form mean of the tilted geometric law on `ℕ`. -/
def tiltedGeometricMean (q : ℚ) : ℚ :=
  q / (1 - q)

/-- Closed-form variance of the tilted geometric law on `ℕ`. -/
def tiltedGeometricVariance (q : ℚ) : ℚ :=
  q / (1 - q) ^ 2

/-- Closed-form second moment of the tilted geometric law on `ℕ`. -/
def tiltedGeometricSecondMoment (q : ℚ) : ℚ :=
  q * (1 + q) / (1 - q) ^ 2

/-- Chapter-local data for the Bernoulli-`p` cycle tilt second-moment package. -/
structure BernoulliPCycleTiltSecondMomentsData where
  qM : ℚ
  qK : ℚ
  qN : ℚ
  xIntercept : ℚ
  xSlope : ℚ
  lIntercept : ℚ
  lSlope : ℚ

/-- Closed-form mean of the tilted block count `K`. -/
def cycleTiltKMean (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  tiltedGeometricMean D.qK

/-- Closed-form mean of the tilted gap count `N`. -/
def cycleTiltNMean (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  tiltedGeometricMean D.qN

/-- The total mean block contribution coming from `K` and `N`. -/
def cycleTiltBlockMean (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  cycleTiltKMean D + cycleTiltNMean D

/-- Conditional affine mean of `X₀` after averaging over the tilted `M` law. -/
def cycleTiltX0Mean (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  D.xIntercept + D.xSlope * tiltedGeometricMean D.qM

/-- Conditional affine mean of `L₀` after averaging over the tilted `M` law. -/
def cycleTiltL0Mean (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  D.lIntercept + D.lSlope * tiltedGeometricMean D.qM

/-- Random-sum variance contribution for `X₀`. -/
def cycleTiltX0Variance (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  D.xSlope ^ 2 * tiltedGeometricVariance D.qM

/-- Random-sum variance contribution for `L₀`. -/
def cycleTiltL0Variance (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  D.lSlope ^ 2 * tiltedGeometricVariance D.qM

/-- Random-sum covariance contribution between `X₀` and `L₀`. -/
def cycleTiltCovariance (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  D.xSlope * D.lSlope * tiltedGeometricVariance D.qM

/-- Expanded second derivative of the pressure obtained from the second moments. -/
def cycleTiltPressureSecondDerivative (D : BernoulliPCycleTiltSecondMomentsData) : ℚ :=
  cycleTiltX0Variance D + 2 * cycleTiltCovariance D + cycleTiltL0Variance D

/-- Geometric-law closure for the tilted `M`, `K`, and `N` variables. -/
def BernoulliPCycleTiltSecondMomentsData.geometricClosure
    (D : BernoulliPCycleTiltSecondMomentsData) : Prop :=
  tiltedGeometricSecondMoment D.qM = D.qM * (1 + D.qM) / (1 - D.qM) ^ 2 ∧
    tiltedGeometricSecondMoment D.qK = D.qK * (1 + D.qK) / (1 - D.qK) ^ 2 ∧
    tiltedGeometricSecondMoment D.qN = D.qN * (1 + D.qN) / (1 - D.qN) ^ 2

/-- Closed forms for the `X₀` and `L₀` means, variances, and covariance obtained by conditioning
on the tilted geometric block count `M`. -/
def BernoulliPCycleTiltSecondMomentsData.blockMomentClosedForms
    (D : BernoulliPCycleTiltSecondMomentsData) : Prop :=
  cycleTiltKMean D = tiltedGeometricMean D.qK ∧
    cycleTiltNMean D = tiltedGeometricMean D.qN ∧
    cycleTiltBlockMean D = tiltedGeometricMean D.qK + tiltedGeometricMean D.qN ∧
    cycleTiltX0Mean D = D.xIntercept + D.xSlope * tiltedGeometricMean D.qM ∧
    cycleTiltL0Mean D = D.lIntercept + D.lSlope * tiltedGeometricMean D.qM ∧
    cycleTiltX0Variance D = D.xSlope ^ 2 * tiltedGeometricVariance D.qM ∧
    cycleTiltL0Variance D = D.lSlope ^ 2 * tiltedGeometricVariance D.qM ∧
    cycleTiltCovariance D = D.xSlope * D.lSlope * tiltedGeometricVariance D.qM

/-- The pressure second derivative closes after expanding the centered second-moment identity. -/
def BernoulliPCycleTiltSecondMomentsData.pressureSecondDerivativeClosed
    (D : BernoulliPCycleTiltSecondMomentsData) : Prop :=
  cycleTiltPressureSecondDerivative D =
    (D.xSlope + D.lSlope) ^ 2 * tiltedGeometricVariance D.qM

/-- Paper-facing package for the tilted geometric closures and second-moment formulas.
    prop:fold-bernoulli-p-cycle-tilt-second-moments-closed -/
theorem paper_fold_bernoulli_p_cycle_tilt_second_moments_closed
    (D : BernoulliPCycleTiltSecondMomentsData) :
    D.geometricClosure ∧ D.blockMomentClosedForms ∧ D.pressureSecondDerivativeClosed := by
  refine ⟨?_, ?_, ?_⟩
  · simp [BernoulliPCycleTiltSecondMomentsData.geometricClosure, tiltedGeometricSecondMoment]
  · simp [BernoulliPCycleTiltSecondMomentsData.blockMomentClosedForms, cycleTiltKMean,
      cycleTiltNMean, cycleTiltBlockMean, cycleTiltX0Mean, cycleTiltL0Mean,
      cycleTiltX0Variance, cycleTiltL0Variance, cycleTiltCovariance]
  · unfold BernoulliPCycleTiltSecondMomentsData.pressureSecondDerivativeClosed
      cycleTiltPressureSecondDerivative cycleTiltX0Variance cycleTiltCovariance cycleTiltL0Variance
      tiltedGeometricVariance
    ring

end Omega.Folding
