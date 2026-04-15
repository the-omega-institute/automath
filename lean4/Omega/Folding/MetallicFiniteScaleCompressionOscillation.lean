import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.MetallicBinetClosedForm
import Omega.Folding.MetallicCompressionLockingLambda2

namespace Omega.Folding

open Omega.Folding.OstrowskiDenominators

/-- The finite-scale metallic compression observable from the paper. -/
noncomputable def metallicFiniteScaleCompression (A m : ℕ) : ℝ :=
  Real.log (((A + 1 : ℝ) ^ m) / metallicDenom A (m + 1))

/-- The affine constant `γ_A = log ((λ_A^2 + 1) / λ_A^3)` appearing in the finite-scale
compression law, written as a function of the Perron root `λ_A`. -/
noncomputable def metallicAffineConstant (lam : ℝ) : ℝ :=
  Real.log ((lam ^ 2 + 1) / lam ^ 3)

lemma metallicPerronRoot_one_lt_nat (A : ℕ) (hA : 1 ≤ A) :
    1 < metallicPerronRoot (A : ℝ) := by
  have hA_real : (1 : ℝ) ≤ A := by
    exact_mod_cast hA
  unfold metallicPerronRoot
  have hsqrt_sq : Real.sqrt ((A : ℝ) ^ 2 + 4) ^ 2 = (A : ℝ) ^ 2 + 4 := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt ((A : ℝ) ^ 2 + 4) := by
    have hlt : (1 : ℝ) ^ 2 < (A : ℝ) ^ 2 + 4 := by
      nlinarith
    nlinarith [Real.sqrt_nonneg ((A : ℝ) ^ 2 + 4), hsqrt_sq]
  nlinarith

/-- Paper-facing finite-scale metallic compression oscillation formula.
    thm:metallic-finite-scale-compression-oscillation -/
theorem paper_metallic_finite_scale_compression_oscillation (A : ℕ) (hA : 1 ≤ A) :
    let lam : ℝ := metallicPerronRoot (A : ℝ)
    (∀ m : ℕ,
      metallicFiniteScaleCompression A m =
        m * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
          Real.log (1 + (-1 : ℝ) ^ (m + 1) * lam ^ (-((2 * m + 4 : ℕ) : ℤ)))) ∧
    (∀ n : ℕ,
      metallicFiniteScaleCompression A (2 * n) =
        (2 * n : ℝ) * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
          Real.log (1 - lam ^ (-((4 * n + 4 : ℕ) : ℤ)))) ∧
    (∀ n : ℕ,
      metallicFiniteScaleCompression A (2 * n + 1) =
        (2 * n + 1 : ℝ) * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
          Real.log (1 + lam ^ (-((4 * n + 6 : ℕ) : ℤ)))) := by
  dsimp
  set lam : ℝ := metallicPerronRoot (A : ℝ)
  have hA1_ne : (A + 1 : ℝ) ≠ 0 := by positivity
  have hA_real : (1 : ℝ) ≤ A := by
    exact_mod_cast hA
  have hlam_pos : 0 < lam := by
    simpa [lam] using metallicPerronRoot_pos hA_real
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hlam_gt_one : 1 < lam := by
    simpa [lam] using metallicPerronRoot_one_lt_nat A hA
  have hden_ne : lam ^ 2 + 1 ≠ 0 := by positivity
  have hdenom_pos : ∀ m : ℕ, 0 < (metallicDenom A (m + 1) : ℝ) := by
    intro m
    have hnat : 0 < metallicDenom A (m + 1) := by
      simpa [metallicDenom] using ostrowskiDenom_pos (fun _ => A) hA (m + 1)
    exact_mod_cast hnat
  have hcorr_pos :
      ∀ m : ℕ, 0 < 1 + (-1 : ℝ) ^ (m + 1) * lam ^ (-((2 * m + 4 : ℕ) : ℤ)) := by
    intro m
    rcases Nat.even_or_odd m with hm_even | hm_odd
    · rcases hm_even with ⟨n, rfl⟩
      have hpow_gt_one : 1 < lam ^ (4 * n + 4) := by
        exact one_lt_pow₀ hlam_gt_one (by omega)
      have hinv_lt_one : lam ^ (-((4 * n + 4 : ℕ) : ℤ)) < 1 := by
        rw [zpow_neg, zpow_natCast]
        exact inv_lt_one_of_one_lt₀ hpow_gt_one
      have hpow_pos : 0 < lam ^ (-((4 * n + 4 : ℕ) : ℤ)) := by
        exact zpow_pos hlam_pos _
      have hsign : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
        rw [show 2 * n + 1 = 2 * n + 1 by omega, pow_add, pow_mul]
        norm_num
      have haux : 0 < 1 - lam ^ (-((4 * n + 4 : ℕ) : ℤ)) := by
        linarith
      have hsign' : (-1 : ℝ) ^ (n + n + 1) = -1 := by
        simpa [two_mul, add_assoc] using hsign
      have hexp' : (-((2 * (n + n) + 4 : ℕ) : ℤ)) = -((4 * n + 4 : ℕ) : ℤ) := by
        omega
      rw [hsign', hexp']
      convert haux using 1
      ring
    · rcases hm_odd with ⟨n, rfl⟩
      have hpow_pos : 0 < lam ^ (-((4 * n + 6 : ℕ) : ℤ)) := by
        exact zpow_pos hlam_pos _
      have hsign : (-1 : ℝ) ^ (2 * n + 2) = 1 := by
        rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul]
        norm_num
      have haux : 0 < 1 + lam ^ (-((4 * n + 6 : ℕ) : ℤ)) := by
        linarith
      have hsign' : (-1 : ℝ) ^ (2 * n + 1 + 1) = 1 := by
        simpa [add_assoc] using hsign
      have hexp' : (-((2 * (2 * n + 1) + 4 : ℕ) : ℤ)) = -((4 * n + 6 : ℕ) : ℤ) := by
        omega
      rw [hsign', hexp']
      convert haux using 1
      ring
  have hmain :
      ∀ m : ℕ,
        metallicFiniteScaleCompression A m =
          m * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
            Real.log (1 + (-1 : ℝ) ^ (m + 1) * lam ^ (-((2 * m + 4 : ℕ) : ℤ))) := by
    intro m
    let corr : ℝ := 1 + (-1 : ℝ) ^ (m + 1) * lam ^ (-((2 * m + 4 : ℕ) : ℤ))
    have hcorr_ne : corr ≠ 0 := (hcorr_pos m).ne'
    have hfactor :
        (metallicDenom A (m + 1) : ℝ) = (lam ^ (m + 3) * corr) / (lam ^ 2 + 1) := by
      have hclosed := paper_metallic_binet_closed_form A (m + 1) hA
      dsimp at hclosed
      have hpow :
          lam ^ (m + 3) * lam ^ (-((2 * m + 4 : ℕ) : ℤ)) = lam ^ (-((m + 1 : ℕ) : ℤ)) := by
        calc
          lam ^ (m + 3) * lam ^ (-((2 * m + 4 : ℕ) : ℤ))
              = lam ^ (((m + 3 : ℕ) : ℤ) + (-((2 * m + 4 : ℕ) : ℤ))) := by
                  rw [← zpow_natCast, ← zpow_add₀ hlam_ne]
          _ = lam ^ (-((m + 1 : ℕ) : ℤ)) := by
                congr 1
                omega
      calc
        (metallicDenom A (m + 1) : ℝ)
            = (lam ^ (m + 3) + (-1 : ℝ) ^ (m + 1) * lam ^ (-((m + 1 : ℕ) : ℤ))) /
                (lam ^ 2 + 1) := by
                  simpa [Nat.add_assoc, lam] using hclosed
        _ = (lam ^ (m + 3) * corr) / (lam ^ 2 + 1) := by
              congr 1
              have hnum :
                  lam ^ (m + 3) + (-1 : ℝ) ^ (m + 1) * lam ^ (-((m + 1 : ℕ) : ℤ)) =
                    lam ^ (m + 3) * corr := by
                dsimp [corr]
                calc
                  lam ^ (m + 3) + (-1 : ℝ) ^ (m + 1) * lam ^ (-((m + 1 : ℕ) : ℤ))
                      = lam ^ (m + 3) +
                          (-1 : ℝ) ^ (m + 1) *
                            (lam ^ (m + 3) * lam ^ (-((2 * m + 4 : ℕ) : ℤ))) := by
                              rw [hpow]
                  _ = lam ^ (m + 3) *
                        (1 + (-1 : ℝ) ^ (m + 1) * lam ^ (-((2 * m + 4 : ℕ) : ℤ))) := by
                          ring
              exact hnum
    have hlog_denom :
        Real.log (metallicDenom A (m + 1)) =
          Real.log (lam ^ (m + 3)) + Real.log corr - Real.log (lam ^ 2 + 1) := by
      rw [hfactor, Real.log_div (mul_ne_zero (pow_ne_zero _ hlam_ne) hcorr_ne) hden_ne]
      rw [Real.log_mul (pow_ne_zero _ hlam_ne) hcorr_ne]
    unfold metallicFiniteScaleCompression
    rw [Real.log_div (pow_ne_zero _ hA1_ne) (hdenom_pos m).ne', hlog_denom]
    unfold metallicCompressionSlope metallicAffineConstant
    rw [Real.log_div hA1_ne hlam_ne, Real.log_div hden_ne (pow_ne_zero 3 hlam_ne)]
    rw [Real.log_pow, Real.log_pow, Real.log_pow]
    dsimp [corr]
    norm_num [Nat.cast_add]
    ring
  refine ⟨hmain, ?_, ?_⟩
  · intro n
    have hsign : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
      rw [show 2 * n + 1 = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    calc
      metallicFiniteScaleCompression A (2 * n)
          = (2 * n : ℝ) * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
              Real.log
                (1 + (-1 : ℝ) ^ (2 * n + 1) * lam ^ (-((2 * (2 * n) + 4 : ℕ) : ℤ))) := by
                  simpa using hmain (2 * n)
      _ = (2 * n : ℝ) * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
            Real.log (1 - lam ^ (-((4 * n + 4 : ℕ) : ℤ))) := by
              have hexp : (-((2 * (2 * n) + 4 : ℕ) : ℤ)) = -((4 * n + 4 : ℕ) : ℤ) := by
                omega
              rw [hsign, hexp]
              congr 2
              ring
  · intro n
    have hsign : (-1 : ℝ) ^ (2 * n + 2) = 1 := by
      rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul]
      norm_num
    calc
      metallicFiniteScaleCompression A (2 * n + 1)
          = (2 * n + 1 : ℝ) * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
              Real.log
                (1 + (-1 : ℝ) ^ (2 * n + 2) * lam ^ (-((2 * (2 * n + 1) + 4 : ℕ) : ℤ))) := by
                  simpa using hmain (2 * n + 1)
      _ = (2 * n + 1 : ℝ) * metallicCompressionSlope (A : ℝ) + metallicAffineConstant lam -
            Real.log (1 + lam ^ (-((4 * n + 6 : ℕ) : ℤ))) := by
              have hexp : (-((2 * (2 * n + 1) + 4 : ℕ) : ℤ)) = -((4 * n + 6 : ℕ) : ℤ) := by
                omega
              rw [hsign, hexp]
              congr 2
              ring

end Omega.Folding
