import Mathlib.Tactic
import Omega.Folding.BernoulliPCycleTiltSecondMomentsClosed
import Omega.Folding.BernoulliPRegenerationPGF

namespace Omega.Folding

/-- The denominator of the explicit Bernoulli-`p` regeneration equation. -/
def bernoulliPPressureCycleDeterminant (u z : ℚ) : ℚ :=
  u ^ 3 * z ^ 3 - 2 * u * z ^ 3 + 4 * u * z ^ 2 + 4 * z - 8

/-- The numerator of the explicit Bernoulli-`p` regeneration equation. -/
def bernoulliPPressureCycleNumerator (u z : ℚ) : ℚ :=
  u * z ^ 4 - 2 * z ^ 2

/-- Concrete cycle-tilt data built from the affine `X₀` and `L₀` laws and the three geometric
tilt parameters. -/
def bernoulliPCycleMomentWitness
    (qM qK qN xIntercept xSlope lIntercept lSlope : ℚ) :
    BernoulliPCycleTiltSecondMomentsData where
  qM := qM
  qK := qK
  qN := qN
  xIntercept := xIntercept
  xSlope := xSlope
  lIntercept := lIntercept
  lSlope := lSlope

/-- The first derivative proxy obtained from the cycle-tilted means of `X₀` and `L₀`. -/
def bernoulliPPressureCycleFirstDerivative
    (qM xIntercept xSlope lIntercept lSlope : ℚ) : ℚ :=
  xIntercept + lIntercept + (xSlope + lSlope) * tiltedGeometricMean qM

/-- The second derivative proxy obtained from the centered second moments of the cycle tilt. -/
def bernoulliPPressureCycleSecondDerivative (qM xSlope lSlope : ℚ) : ℚ :=
  (xSlope + lSlope) ^ 2 * tiltedGeometricVariance qM

/-- Paper-facing wrapper for the Bernoulli-`p` pressure cycle equation: the regeneration PGF has
the explicit numerator/determinant form, the root equation `Φ_p = 1` is the corresponding
determinant equation when the denominator is nonzero, and the cycle-tilted law of `(L₀, X₀)`
produces the first- and second-derivative closed forms.
    thm:fold-bernoulli-p-pressure-cycle-equation -/
theorem paper_fold_bernoulli_p_pressure_cycle_equation
    (u z qM qK qN xIntercept xSlope lIntercept lSlope : ℚ)
    (hdet : bernoulliPPressureCycleDeterminant u z ≠ 0) :
    bernoulliGaugeRegenerationPGF u z =
      bernoulliPPressureCycleNumerator u z / bernoulliPPressureCycleDeterminant u z ∧
      (bernoulliGaugeRegenerationPGF u z = 1 ↔
        bernoulliPPressureCycleNumerator u z = bernoulliPPressureCycleDeterminant u z) ∧
      cycleTiltBlockMean
          (bernoulliPCycleMomentWitness qM qK qN xIntercept xSlope lIntercept lSlope) =
        tiltedGeometricMean qK + tiltedGeometricMean qN ∧
      cycleTiltX0Mean
          (bernoulliPCycleMomentWitness qM qK qN xIntercept xSlope lIntercept lSlope) +
          cycleTiltL0Mean
            (bernoulliPCycleMomentWitness qM qK qN xIntercept xSlope lIntercept lSlope) =
        bernoulliPPressureCycleFirstDerivative qM xIntercept xSlope lIntercept lSlope ∧
      cycleTiltPressureSecondDerivative
          (bernoulliPCycleMomentWitness qM qK qN xIntercept xSlope lIntercept lSlope) =
        bernoulliPPressureCycleSecondDerivative qM xSlope lSlope := by
  let D := bernoulliPCycleMomentWitness qM qK qN xIntercept xSlope lIntercept lSlope
  rcases paper_fold_gauge_anomaly_regeneration_pgf u z with
    ⟨_, _, _, _, _, hPGF, _, _, _, _, _, _, _, _⟩
  have hPGF' :
      bernoulliGaugeRegenerationPGF u z =
        bernoulliPPressureCycleNumerator u z / bernoulliPPressureCycleDeterminant u z := by
    simpa [bernoulliPPressureCycleNumerator, bernoulliPPressureCycleDeterminant] using hPGF
  have hRoot :
      bernoulliGaugeRegenerationPGF u z = 1 ↔
        bernoulliPPressureCycleNumerator u z = bernoulliPPressureCycleDeterminant u z := by
    constructor
    · intro hroot
      rw [hPGF'] at hroot
      simpa using (div_eq_iff hdet).mp hroot
    · intro hroot
      rw [hPGF']
      exact (div_eq_iff hdet).2 (by simpa using hroot)
  have hBlock :
      cycleTiltBlockMean D = tiltedGeometricMean qK + tiltedGeometricMean qN := by
    simp [D, bernoulliPCycleMomentWitness, cycleTiltBlockMean, cycleTiltKMean, cycleTiltNMean]
  have hFirst :
      cycleTiltX0Mean D + cycleTiltL0Mean D =
        bernoulliPPressureCycleFirstDerivative qM xIntercept xSlope lIntercept lSlope := by
    simp [D, bernoulliPCycleMomentWitness, bernoulliPPressureCycleFirstDerivative,
      cycleTiltX0Mean, cycleTiltL0Mean]
    ring
  have hSecondPkg := paper_fold_bernoulli_p_cycle_tilt_second_moments_closed D
  rcases hSecondPkg with ⟨_, _, hSecond⟩
  have hSecond' :
      cycleTiltPressureSecondDerivative D =
        bernoulliPPressureCycleSecondDerivative qM xSlope lSlope := by
    simpa [D, bernoulliPCycleMomentWitness, bernoulliPPressureCycleSecondDerivative] using hSecond
  exact ⟨hPGF', hRoot, hBlock, hFirst, hSecond'⟩

end Omega.Folding
