import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper label: `thm:poisson-defect-ladder`. The explicit normalized eighth-order coefficient is
bounded below by its symmetric two-point value because the correction terms are manifestly
nonnegative. -/
theorem paper_poisson_defect_ladder
    (sigma C6 C8 beta3 kappa q3sq : ℝ) (h_sigma : 0 < sigma) (h_kappa : 0 ≤ kappa)
    (h_q3sq : 0 ≤ q3sq) (hC6 : 64 / sigma ^ 6 * C6 = -7 - 2 * beta3 ^ 2 - 8 * kappa)
    (hC8 :
      256 / sigma ^ 8 * C8 =
        23 + 12 * q3sq + 32 * kappa ^ 2 + (61 / 4) * beta3 ^ 2 * kappa + 52 * kappa +
          2 * beta3 ^ 4 + 13 * beta3 ^ 2) :
    C8 ≥ (23 / 256 : ℝ) * sigma ^ 8 := by
  let _ := hC6
  have hRest :
      0 ≤
        12 * q3sq + 32 * kappa ^ 2 +
          (61 / 4) * beta3 ^ 2 * kappa + 52 * kappa + 2 * beta3 ^ 4 + 13 * beta3 ^ 2 := by
    have hbetaSq : 0 ≤ beta3 ^ 2 := sq_nonneg beta3
    have hkappaSq : 0 ≤ kappa ^ 2 := sq_nonneg kappa
    have hbetaFourth : 0 ≤ beta3 ^ 4 := by
      nlinarith [hbetaSq]
    nlinarith
  have hsigma8 : 0 < sigma ^ 8 := by
    positivity
  have hsigma8_ne : sigma ^ 8 ≠ 0 := by
    positivity
  have hScaled := hC8
  field_simp [hsigma8_ne] at hScaled
  nlinarith [hScaled, hRest, hsigma8]

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the two-level defect ladder in the Poisson
    entropy expansion.
    thm:poisson-defect-ladder -/
theorem paper_circle_dimension_poisson_defect_ladder
    (sigma C6 C8 beta3 kappa q3sq : ℝ)
    (twoPointLaw : Prop)
    (hσ : 0 < sigma)
    (hkappa : 0 ≤ kappa)
    (hq3sq : 0 ≤ q3sq)
    (hC6 : 64 / sigma ^ 6 * C6 = -7 - 2 * beta3 ^ 2 - 8 * kappa)
    (hC8 :
      256 / sigma ^ 8 * C8 =
        23 + 12 * q3sq + 32 * kappa ^ 2 +
          (61 / 4) * beta3 ^ 2 * kappa + 52 * kappa + 2 * beta3 ^ 4 + 13 * beta3 ^ 2)
    (hEquality : C8 = 23 / 256 * sigma ^ 8 ↔ twoPointLaw) :
    (64 / sigma ^ 6 * C6 = -7 - 2 * beta3 ^ 2 - 8 * kappa) ∧
      (256 / sigma ^ 8 * C8 =
        23 + 12 * q3sq + 32 * kappa ^ 2 +
          (61 / 4) * beta3 ^ 2 * kappa + 52 * kappa + 2 * beta3 ^ 4 + 13 * beta3 ^ 2) ∧
      C8 ≥ 23 / 256 * sigma ^ 8 ∧
      (C8 = 23 / 256 * sigma ^ 8 ↔ twoPointLaw) := by
  have hRest :
      0 ≤
        12 * q3sq + 32 * kappa ^ 2 +
          (61 / 4) * beta3 ^ 2 * kappa + 52 * kappa + 2 * beta3 ^ 4 + 13 * beta3 ^ 2 := by
    have hbetaSq : 0 ≤ beta3 ^ 2 := sq_nonneg beta3
    have hkappaSq : 0 ≤ kappa ^ 2 := sq_nonneg kappa
    have hbetaFourth : 0 ≤ beta3 ^ 4 := by nlinarith [hbetaSq]
    nlinarith
  have hLower : C8 ≥ 23 / 256 * sigma ^ 8 := by
    have hsigma8 : 0 < sigma ^ 8 := by positivity
    have hsigma8_ne : sigma ^ 8 ≠ 0 := by positivity
    have hScaled := hC8
    field_simp [hsigma8_ne] at hScaled
    nlinarith [hScaled, hRest]
  exact ⟨hC6, hC8, hLower, hEquality⟩

end Omega.CircleDimension
