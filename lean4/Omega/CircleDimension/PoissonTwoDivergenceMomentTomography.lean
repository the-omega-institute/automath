import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.PoissonEntropyTomography

namespace Omega.CircleDimension

/-- Scaled fourth-order total-variation coefficient. -/
noncomputable def poissonTvFourthScaled (sigmaSq mu3Sq mu4 : ℝ) : ℝ :=
  2 * mu3Sq / sigmaSq - 3 * mu4

/-- Scaled sixth-order KL coefficient. -/
def poissonKlSixthScaled (sigmaSq mu3Sq mu4 : ℝ) : ℝ :=
  sigmaSq ^ 3 + 6 * mu3Sq - 8 * sigmaSq * mu4

/-- The two divergence coefficients recover the fourth moment and the squared third moment by
solving the resulting `2 × 2` linear system.
    prop:cdim-poisson-two-divergence-moment-tomography -/
theorem paper_cdim_poisson_two_divergence_moment_tomography
    {sigmaSq mu3Sq mu4 K L : ℝ} (hsigma : sigmaSq ≠ 0)
    (hK : K = poissonTvFourthScaled sigmaSq mu3Sq mu4)
    (hL : L = poissonKlSixthScaled sigmaSq mu3Sq mu4) :
    K = 2 * mu3Sq / sigmaSq - 3 * mu4 ∧
      L = sigmaSq ^ 3 + 6 * mu3Sq - 8 * sigmaSq * mu4 ∧
      mu4 = L / sigmaSq - sigmaSq ^ 2 - 3 * K ∧
      mu3Sq = sigmaSq / 2 * (3 * mu4 + K) := by
  have hKmul : K * sigmaSq = 2 * mu3Sq - 3 * mu4 * sigmaSq := by
    rw [hK, poissonTvFourthScaled]
    field_simp [hsigma]
  have hmu3 : mu3Sq = sigmaSq / 2 * (3 * mu4 + K) := by
    nlinarith [hKmul]
  have hmu3six : 6 * mu3Sq = 3 * sigmaSq * (3 * mu4 + K) := by
    nlinarith [hmu3]
  have hL' : L = sigmaSq ^ 3 + sigmaSq * mu4 + 3 * sigmaSq * K := by
    rw [hL, poissonKlSixthScaled] at *
    nlinarith [hmu3six]
  have hdiv : L / sigmaSq = sigmaSq ^ 2 + mu4 + 3 * K := by
    apply (div_eq_iff hsigma).2
    nlinarith [hL']
  have hmu4 : mu4 = L / sigmaSq - sigmaSq ^ 2 - 3 * K := by
    nlinarith [hdiv]
  exact
    ⟨by simpa [poissonTvFourthScaled] using hK, by simpa [poissonKlSixthScaled] using hL, hmu4,
      hmu3⟩

end Omega.CircleDimension
