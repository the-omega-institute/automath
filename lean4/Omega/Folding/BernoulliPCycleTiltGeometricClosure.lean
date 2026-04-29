import Mathlib.Tactic
import Omega.Folding.BernoulliPCycleTiltSecondMomentsClosed

namespace Omega.Folding

/-- Power-weighting a geometric block with weight `w` rescales its ratio by `w`. -/
def powerWeightedGeometricRatio (weight q : ℚ) : ℚ :=
  weight * q

/-- Closed-form second-moment identity for a power-weighted geometric law. -/
def powerWeightedGeometricClosed (weight q : ℚ) : Prop :=
  tiltedGeometricSecondMoment (powerWeightedGeometricRatio weight q) =
    powerWeightedGeometricRatio weight q * (1 + powerWeightedGeometricRatio weight q) /
      (1 - powerWeightedGeometricRatio weight q) ^ 2

/-- Chapter-local package for the Bernoulli-`p` cycle-tilt geometric closure data: the `K` and
`N` block ratios, their power weights, and the spectral parameter `ρ` used for the Doob
specialization `z = ρ⁻¹`. -/
structure CycleTiltGeometricClosureData where
  qK : ℚ
  qN : ℚ
  kWeight : ℚ
  nWeight : ℚ
  rho : ℚ

/-- Tilted geometric ratio for the `K` blocks. -/
def cycleTiltKRatio (D : CycleTiltGeometricClosureData) : ℚ :=
  powerWeightedGeometricRatio D.kWeight D.qK

/-- Tilted geometric ratio for the `N` blocks. -/
def cycleTiltNRatio (D : CycleTiltGeometricClosureData) : ℚ :=
  powerWeightedGeometricRatio D.nWeight D.qN

/-- The induced geometric ratio for the `M` marginal comes from multiplying the weighted `K` and
`N` ratios. -/
def cycleTiltMRatio (D : CycleTiltGeometricClosureData) : ℚ :=
  cycleTiltKRatio D * cycleTiltNRatio D

/-- Specializing the cycle tilt at `z = ρ⁻¹` gives the Doob-transform ratio. -/
def cycleTiltDoobSpecialization (D : CycleTiltGeometricClosureData) : ℚ :=
  powerWeightedGeometricRatio (1 / D.rho) D.qK *
    powerWeightedGeometricRatio (1 / D.rho) D.qN

/-- Closed form of the Doob-transform ratio obtained after the `z = ρ⁻¹` specialization. -/
def cycleTiltDoobClosedForm (D : CycleTiltGeometricClosureData) : ℚ :=
  D.qK * D.qN / D.rho ^ 2

/-- Power-weighting preserves the geometric family for the `K` blocks. -/
def CycleTiltGeometricClosureData.kFamilyClosed (D : CycleTiltGeometricClosureData) : Prop :=
  cycleTiltKRatio D = D.kWeight * D.qK ∧ powerWeightedGeometricClosed D.kWeight D.qK

/-- Power-weighting preserves the geometric family for the `N` blocks. -/
def CycleTiltGeometricClosureData.nFamilyClosed (D : CycleTiltGeometricClosureData) : Prop :=
  cycleTiltNRatio D = D.nWeight * D.qN ∧ powerWeightedGeometricClosed D.nWeight D.qN

/-- The induced `M` marginal is again geometric, with ratio equal to the product of the weighted
`K` and `N` ratios. -/
def CycleTiltGeometricClosureData.mMarginalClosed (D : CycleTiltGeometricClosureData) : Prop :=
  cycleTiltMRatio D = D.kWeight * D.nWeight * D.qK * D.qN ∧
    tiltedGeometricSecondMoment (cycleTiltMRatio D) =
      cycleTiltMRatio D * (1 + cycleTiltMRatio D) / (1 - cycleTiltMRatio D) ^ 2

/-- The `z = ρ⁻¹` specialization matches the closed-form Doob ratio. -/
def CycleTiltGeometricClosureData.doobConsistency (D : CycleTiltGeometricClosureData) : Prop :=
  cycleTiltDoobSpecialization D = cycleTiltDoobClosedForm D

/-- The regeneration/power-weight decomposition preserves the geometric laws of the `K` and `N`
blocks, induces the expected geometric ratio for `M`, and the `z = ρ⁻¹` specialization agrees
with the closed-form Doob-transform ratio.
    prop:fold-bernoulli-p-cycle-tilt-geometric-closure -/
theorem paper_fold_bernoulli_p_cycle_tilt_geometric_closure
    (D : CycleTiltGeometricClosureData) :
    D.kFamilyClosed ∧ D.nFamilyClosed ∧ D.mMarginalClosed ∧ D.doobConsistency := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      ⟨rfl, by
        simp [powerWeightedGeometricClosed, powerWeightedGeometricRatio,
          tiltedGeometricSecondMoment]⟩
  · exact
      ⟨rfl, by
        simp [powerWeightedGeometricClosed, powerWeightedGeometricRatio,
          tiltedGeometricSecondMoment]⟩
  · constructor
    · unfold cycleTiltMRatio cycleTiltKRatio cycleTiltNRatio powerWeightedGeometricRatio
      ring
    · simp [cycleTiltMRatio, cycleTiltKRatio, cycleTiltNRatio, powerWeightedGeometricRatio,
        tiltedGeometricSecondMoment]
  · unfold CycleTiltGeometricClosureData.doobConsistency cycleTiltDoobSpecialization
      cycleTiltDoobClosedForm powerWeightedGeometricRatio
    by_cases hrho : D.rho = 0
    · simp [hrho]
    · field_simp [hrho]

end Omega.Folding
