import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper label: `thm:poisson-defect-amplification`. Defining the sixth-order and eighth-order
defects exactly as in the paper and substituting the already normalized coefficient identities
isolates a manifestly nonnegative remainder. -/
theorem paper_poisson_defect_amplification
    (sigma C6 C8 beta3 kappa q3sq : ℝ) (h_sigma : 0 < sigma) (h_kappa : 0 <= kappa)
    (h_q3sq : 0 <= q3sq)
    (hC6 : 64 / sigma ^ 6 * C6 = -7 - 2 * beta3 ^ 2 - 8 * kappa)
    (hC8 :
      256 / sigma ^ 8 * C8 =
        23 + 12 * q3sq + 32 * kappa ^ 2 + (61 / 4) * beta3 ^ 2 * kappa + 52 * kappa +
          2 * beta3 ^ 4 + 13 * beta3 ^ 2) :
    let Delta6 : ℝ := -((7 : ℝ) / 64) * sigma ^ 6 - C6
    let Delta8 : ℝ := C8 - ((23 : ℝ) / 256) * sigma ^ 8
    And
      (Delta8 =
        (13 * sigma ^ 2 / 8) * Delta6 +
          sigma ^ 8 / 256 * (12 * q3sq + 32 * kappa ^ 2 + (61 / 4) * beta3 ^ 2 * kappa +
            2 * beta3 ^ 4))
      (Delta8 >= (13 * sigma ^ 2 / 8) * Delta6) := by
  have hsigma6 : sigma ^ 6 ≠ 0 := by positivity
  have hsigma8 : sigma ^ 8 ≠ 0 := by positivity
  have hsigma8_nonneg : 0 ≤ sigma ^ 8 := by positivity
  have hC6_scaled : 64 * C6 = sigma ^ 6 * (-7 - 2 * beta3 ^ 2 - 8 * kappa) := by
    have hC6' := hC6
    field_simp [hsigma6] at hC6'
    nlinarith
  have hC8_scaled :
      256 * C8 =
        sigma ^ 8 *
          (23 + 12 * q3sq + 32 * kappa ^ 2 + (61 / 4) * beta3 ^ 2 * kappa + 52 * kappa +
            2 * beta3 ^ 4 + 13 * beta3 ^ 2) := by
    have hC8' := hC8
    field_simp [hsigma8] at hC8'
    nlinarith
  have hbetaSq : 0 ≤ beta3 ^ 2 := sq_nonneg beta3
  have hkappaSq : 0 ≤ kappa ^ 2 := sq_nonneg kappa
  have hbetaFourth : 0 ≤ beta3 ^ 4 := by nlinarith [hbetaSq]
  have hbetaSqKappa : 0 ≤ beta3 ^ 2 * kappa := by nlinarith [hbetaSq, h_kappa]
  have hremainder :
      0 ≤
        12 * q3sq + 32 * kappa ^ 2 + (61 / 4) * beta3 ^ 2 * kappa + 2 * beta3 ^ 4 := by
    nlinarith
  dsimp
  constructor
  · nlinarith [hC6_scaled, hC8_scaled]
  · have hmain :
        C8 - (23 : ℝ) / 256 * sigma ^ 8 =
          (13 * sigma ^ 2 / 8) * (-((7 : ℝ) / 64) * sigma ^ 6 - C6) +
            sigma ^ 8 / 256 *
              (12 * q3sq + 32 * kappa ^ 2 + (61 / 4) * beta3 ^ 2 * kappa + 2 * beta3 ^ 4) := by
      nlinarith [hC6_scaled, hC8_scaled]
    nlinarith [hmain, hremainder, hsigma8_nonneg]

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for defect amplification in the Poisson entropy expansion.
    thm:poisson-defect-amplification -/
theorem paper_circle_dimension_poisson_defect_amplification
    (sigma Delta6 Delta8 beta3 kappa remainder : ℝ)
    (twoPointLaw : Prop)
    (hDelta6 :
      Delta6 = sigma ^ 6 / 32 * beta3 ^ 2 + sigma ^ 6 / 8 * kappa)
    (hAmplification :
      Delta8 = (13 * sigma ^ 2 / 8) * Delta6 + remainder)
    (hRemainder : 0 ≤ remainder)
    (hEquality : remainder = 0 ↔ twoPointLaw) :
    (Delta6 = sigma ^ 6 / 32 * beta3 ^ 2 + sigma ^ 6 / 8 * kappa) ∧
      (Delta8 = (13 * sigma ^ 2 / 8) * Delta6 + remainder) ∧
      Delta8 ≥ (13 * sigma ^ 2 / 8) * Delta6 ∧
      (Delta8 = (13 * sigma ^ 2 / 8) * Delta6 ↔ twoPointLaw) := by
  have hEqRemainder : Delta8 = (13 * sigma ^ 2 / 8) * Delta6 ↔ remainder = 0 := by
    constructor
    · intro hEq
      rw [hAmplification] at hEq
      nlinarith
    · intro hZero
      simpa [hZero] using hAmplification
  refine ⟨hDelta6, hAmplification, ?_, hEqRemainder.trans hEquality⟩
  rw [hAmplification]
  nlinarith

end Omega.CircleDimension
