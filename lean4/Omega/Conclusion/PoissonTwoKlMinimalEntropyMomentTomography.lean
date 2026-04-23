import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.PoissonEntropyTomography

namespace Omega.Conclusion

/-- The two KL asymptotic coefficients together with the second-order matched benchmark recover the
variance, squared skewness, and fourth moment by the closed-form inversion already formalized in
the CircleDimension chapter.
    thm:conclusion-poisson-two-kl-minimal-entropy-moment-tomography -/
theorem paper_conclusion_poisson_two_kl_minimal_entropy_moment_tomography
    {A4 A6 B6 sigmaSq mu3Sq mu4 : ℝ}
    (hsigma_nonneg : 0 ≤ sigmaSq) (hsigma : sigmaSq ≠ 0)
    (hA4 : 8 * A4 = sigmaSq ^ 2)
    (hA6 : 64 * A6 = sigmaSq ^ 3 - 8 * sigmaSq * mu4 + 6 * mu3Sq)
    (hB6 : 32 * B6 = 3 * mu3Sq) :
    sigmaSq = Real.sqrt (8 * A4) ∧
      mu3Sq = (32 / 3) * B6 ∧
      mu4 = (sigmaSq ^ 3 + 6 * mu3Sq - 64 * A6) / (8 * sigmaSq) := by
  rcases
      Omega.CircleDimension.paper_cdim_poisson_entropy_moment_tomography
        (A4 := A4) (A6 := A6) (B6 := B6) (sigmaSq := sigmaSq) (mu3Sq := mu3Sq) (mu4 := mu4)
        hsigma hA4 hA6 hB6 with
    ⟨hsigma_sq, hmu3Sq, hmu4⟩
  have hsigma_eq : sigmaSq = Real.sqrt (8 * A4) := by
    rw [← hsigma_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsigma_nonneg]
  exact ⟨hsigma_eq, hmu3Sq, hmu4⟩

end Omega.Conclusion
