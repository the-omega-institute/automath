import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionMod3ZeroOneDefectSharp

open Filter
open scoped Topology

namespace Omega.Conclusion

noncomputable section

/-- The common exponential barrier read from the scan-negative asymptotic. -/
def conclusion_negative_sign_same_barrier_different_residue_scan_barrier
    (lambda0 lambda1 : ℝ) : ℝ :=
  Real.log (lambda1 / lambda0)

/-- The common exponential barrier read from the time-reversal-negative asymptotic. -/
def conclusion_negative_sign_same_barrier_different_residue_time_reversal_barrier
    (lambda0 lambda1 : ℝ) : ℝ :=
  Real.log (lambda1 / lambda0)

/-- The scan-negative residue constant. -/
def conclusion_negative_sign_same_barrier_different_residue_scan_prefactor
    (mu0 mu1 cc : ℝ) : ℝ :=
  mu1 * cc / mu0 ^ 2

/-- The time-reversal-negative residue constant. -/
def conclusion_negative_sign_same_barrier_different_residue_time_reversal_prefactor
    (mu0 mu1 ciota : ℝ) : ℝ :=
  mu1 * ciota / mu0 ^ 2

/-- The sharp scan-negative asymptotic template. Using `L + 1` avoids the trivial zero at the
origin while preserving the same barrier and residue ratio. -/
def conclusion_negative_sign_same_barrier_different_residue_scan_main_term
    (lambda0 lambda1 mu0 mu1 cc : ℝ) (L : ℕ) : ℝ :=
  conclusion_negative_sign_same_barrier_different_residue_scan_prefactor mu0 mu1 cc *
    ((L + 1 : ℕ) : ℝ) * (lambda0 / lambda1) ^ (L + 1)

/-- The sharp time-reversal-negative asymptotic template. -/
def conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
    (lambda0 lambda1 mu0 mu1 ciota : ℝ) (L : ℕ) : ℝ :=
  conclusion_negative_sign_same_barrier_different_residue_time_reversal_prefactor mu0 mu1 ciota *
    ((L + 1 : ℕ) : ℝ) * (lambda0 / lambda1) ^ (L + 1)

private lemma conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term_ne
    (lambda0 lambda1 mu0 mu1 ciota : ℝ) (L : ℕ) (hlambda0 : lambda0 ≠ 0) (hlambda1 : lambda1 ≠ 0)
    (hmu0 : mu0 ≠ 0) (hmu1 : mu1 ≠ 0) (hciota : ciota ≠ 0) :
    conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
        lambda0 lambda1 mu0 mu1 ciota L ≠ 0 := by
  unfold conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
    conclusion_negative_sign_same_barrier_different_residue_time_reversal_prefactor
  refine mul_ne_zero ?_ (pow_ne_zero (L + 1) (div_ne_zero hlambda0 hlambda1))
  refine mul_ne_zero ?_ ?_
  · exact div_ne_zero (mul_ne_zero hmu1 hciota) (pow_ne_zero 2 hmu0)
  · exact_mod_cast (Nat.succ_ne_zero L)

/-- Paper label: `thm:conclusion-negative-sign-same-barrier-different-residue`. If the scan- and
time-reversal-negative events satisfy sharp asymptotics with the same exponential scale
`(λ₀ / λ₁)^L`, then the logarithmic barrier is common and the event ratio converges to the ratio of
the residue constants. -/
theorem paper_conclusion_negative_sign_same_barrier_different_residue
    (scanNegative timeReversalNegative : ℕ → ℝ)
    (lambda0 lambda1 mu0 mu1 cc ciota : ℝ)
    (hlambda0 : lambda0 ≠ 0) (hlambda1 : lambda1 ≠ 0)
    (hmu0 : mu0 ≠ 0) (hmu1 : mu1 ≠ 0) (hcc : cc ≠ 0) (hciota : ciota ≠ 0)
    (htime_nonzero : ∀ L, timeReversalNegative L ≠ 0)
    (hscan :
      Omega.POM.SharpAsymptotic scanNegative
        (conclusion_negative_sign_same_barrier_different_residue_scan_main_term
          lambda0 lambda1 mu0 mu1 cc))
    (htime :
      Omega.POM.SharpAsymptotic timeReversalNegative
        (conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
          lambda0 lambda1 mu0 mu1 ciota)) :
    conclusion_negative_sign_same_barrier_different_residue_scan_barrier lambda0 lambda1 =
      Real.log (lambda1 / lambda0) ∧
      conclusion_negative_sign_same_barrier_different_residue_time_reversal_barrier lambda0 lambda1 =
        Real.log (lambda1 / lambda0) ∧
      Tendsto (fun L => scanNegative L / timeReversalNegative L) atTop (𝓝 (cc / ciota)) := by
  have htimeInv :
      Tendsto
        (fun L =>
          (timeReversalNegative L /
              conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
                lambda0 lambda1 mu0 mu1 ciota L)⁻¹)
        atTop (𝓝 1) := by
    simpa [Omega.POM.SharpAsymptotic] using htime.inv₀ one_ne_zero
  have hcore :
      Tendsto
        (fun L =>
          (scanNegative L /
              conclusion_negative_sign_same_barrier_different_residue_scan_main_term
                lambda0 lambda1 mu0 mu1 cc L) *
            (timeReversalNegative L /
                conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
                  lambda0 lambda1 mu0 mu1 ciota L)⁻¹)
        atTop (𝓝 1) := by
    simpa [Omega.POM.SharpAsymptotic] using hscan.mul htimeInv
  have hratioEq :
      (fun L => scanNegative L / timeReversalNegative L) =
        fun L =>
          (cc / ciota) *
            ((scanNegative L /
                conclusion_negative_sign_same_barrier_different_residue_scan_main_term
                  lambda0 lambda1 mu0 mu1 cc L) *
              (timeReversalNegative L /
                  conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
                    lambda0 lambda1 mu0 mu1 ciota L)⁻¹) := by
    funext L
    have hmain_ne :
        conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
            lambda0 lambda1 mu0 mu1 ciota L ≠ 0 :=
      conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term_ne
        lambda0 lambda1 mu0 mu1 ciota L hlambda0 hlambda1 hmu0 hmu1 hciota
    unfold conclusion_negative_sign_same_barrier_different_residue_scan_main_term
      conclusion_negative_sign_same_barrier_different_residue_time_reversal_main_term
      conclusion_negative_sign_same_barrier_different_residue_scan_prefactor
      conclusion_negative_sign_same_barrier_different_residue_time_reversal_prefactor
    field_simp [hmu0, hmu1, hcc, hciota, hlambda0, hlambda1, htime_nonzero L, hmain_ne]
  refine ⟨rfl, rfl, ?_⟩
  rw [hratioEq]
  simpa using Filter.Tendsto.const_mul (cc / ciota) hcore

end

end Omega.Conclusion
