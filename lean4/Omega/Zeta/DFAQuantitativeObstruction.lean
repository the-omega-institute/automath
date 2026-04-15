import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: if recall and precision stay uniformly positive, then the accepted mass
    stays trapped between constant multiples of the prime mass.
    prop:dfa-quantitative-obstruction -/
theorem paper_prime_languages_dfa_quantitative_obstruction_seeds
    {δ primeCount acceptCount hitCount : ℝ}
    (hδ : 0 < δ)
    (hrec : δ * primeCount ≤ hitCount)
    (hsubAccept : hitCount ≤ acceptCount)
    (hsubPrime : hitCount ≤ primeCount)
    (hprec : δ * acceptCount ≤ hitCount) :
    δ * primeCount ≤ hitCount ∧
      hitCount ≤ acceptCount ∧
      acceptCount ≤ δ⁻¹ * hitCount ∧
      δ⁻¹ * hitCount ≤ δ⁻¹ * primeCount := by
  refine ⟨hrec, hsubAccept, ?_, ?_⟩
  · have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    have hscaled := mul_le_mul_of_nonneg_left hprec hδinv_nonneg
    simpa [mul_assoc, hδ.ne', mul_comm, mul_left_comm, mul_assoc] using hscaled
  · have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hsubPrime hδinv_nonneg)

/-- Wrapper theorem matching the paper-facing quantitative obstruction package.
    prop:dfa-quantitative-obstruction -/
theorem paper_prime_languages_dfa_quantitative_obstruction_package
    {δ primeCount acceptCount hitCount : ℝ}
    (hδ : 0 < δ)
    (hrec : δ * primeCount ≤ hitCount)
    (hsubAccept : hitCount ≤ acceptCount)
    (hsubPrime : hitCount ≤ primeCount)
    (hprec : δ * acceptCount ≤ hitCount) :
    δ * primeCount ≤ hitCount ∧
      hitCount ≤ acceptCount ∧
      acceptCount ≤ δ⁻¹ * hitCount ∧
      δ⁻¹ * hitCount ≤ δ⁻¹ * primeCount :=
  paper_prime_languages_dfa_quantitative_obstruction_seeds
    hδ hrec hsubAccept hsubPrime hprec

end Omega.Zeta
