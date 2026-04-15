import Mathlib.Tactic
import Omega.Experiments.TVCertificateHist

namespace Omega.Experiments.RotationMicrostateKLCertificate

/-- A monotone-arithmetic helper for the rotation microstate KL certificate once the
    total-variation side is known to be nonnegative. -/
theorem rotation_microstate_kl_certificate_of_nonneg
    (m : ℕ) (dKL dTV qMin star : ℝ) (hq : 0 < qMin) (hStar : 0 ≤ star) (hTV0 : 0 ≤ dTV)
    (hTV : dTV <= (m + 1 : ℝ) * star) (hKL : dKL <= 2 * dTV ^ 2 / qMin) :
    dKL <= 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin := by
  have hm : 0 ≤ (m + 1 : ℝ) := by
    positivity
  have hUpper : 0 ≤ (m + 1 : ℝ) * star := mul_nonneg hm hStar
  have hSq : dTV ^ 2 ≤ ((m + 1 : ℝ) * star) ^ 2 := by
    nlinarith
  have hScaled : 2 * dTV ^ 2 / qMin ≤ 2 * (((m + 1 : ℝ) * star) ^ 2) / qMin := by
    have hMul : 2 * dTV ^ 2 ≤ 2 * (((m + 1 : ℝ) * star) ^ 2) := by
      nlinarith
    exact div_le_div_of_nonneg_right hMul (le_of_lt hq)
  exact le_trans hKL hScaled

/-- A paper-facing corollary: once KL is monotone under the folding pushforward, the microstate
    certificate immediately transfers to the folded distribution.
    cor:rotation-folded-kl-certificate -/
theorem paper_rotation_folded_kl_certificate
    (m : ℕ) (dKlMicro dKlFold star qMin : ℝ) (hPush : dKlFold ≤ dKlMicro)
    (hMicro : dKlMicro ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin) :
    dKlFold ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin := by
  exact le_trans hPush hMicro

end Omega.Experiments.RotationMicrostateKLCertificate
