import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Data.Nat.Choose.Central
import Omega.POM

open scoped BigOperators
open intervalIntegral

namespace Omega.Conclusion

private lemma arcsineAverage_nat_moment_closed_form (r : ℕ) :
    Omega.POM.arcsineAverage (fun μ => μ ^ r) =
      (4 : ℝ) ^ r * ∏ i ∈ Finset.range r, (2 * (i : ℝ) + 1) / (2 * i + 2) := by
  have hcomp :
      (2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi / 2, (2 * (1 - Real.cos (2 * x))) ^ r =
        ∫ x in (0 : ℝ)..Real.pi, (2 * (1 - Real.cos x)) ^ r := by
    simpa [two_mul] using
      (mul_integral_comp_mul_left
        (f := fun x : ℝ => (2 * (1 - Real.cos x)) ^ r) (a := (0 : ℝ)) (b := Real.pi / 2)
        (c := (2 : ℝ)))
  have hpow :
      ∫ x in (0 : ℝ)..Real.pi / 2, (2 * (1 - Real.cos (2 * x))) ^ r =
        (4 : ℝ) ^ r * ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * r) := by
    calc
      ∫ x in (0 : ℝ)..Real.pi / 2, (2 * (1 - Real.cos (2 * x))) ^ r
          = ∫ x in (0 : ℝ)..Real.pi / 2, ((4 : ℝ) * Real.sin x ^ 2) ^ r := by
              refine integral_congr_ae ?_
              filter_upwards with x
              intro _
              have hx : 2 * (1 - Real.cos (2 * x)) = (4 : ℝ) * Real.sin x ^ 2 := by
                nlinarith [Real.sin_sq_eq_half_sub x]
              rw [hx]
      _ = ∫ x in (0 : ℝ)..Real.pi / 2, (4 : ℝ) ^ r * Real.sin x ^ (2 * r) := by
            refine integral_congr_ae ?_
            filter_upwards with x
            intro _
            rw [mul_pow]
            have hsq : (Real.sin x ^ (2 : ℕ)) ^ r = Real.sin x ^ (2 * r) := by rw [pow_mul]
            simpa [sq] using congrArg (fun y : ℝ => (4 : ℝ) ^ r * y) hsq
      _ = (4 : ℝ) ^ r * ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * r) := by
            rw [intervalIntegral.integral_const_mul]
  have hsymm :
      ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * r) =
        ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ (2 * r) := by
    simpa [Real.sin_pi_div_two_sub] using
      (intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => Real.sin x ^ (2 * r)) (a := (0 : ℝ)) (b := Real.pi / 2)
        (d := Real.pi / 2)).symm
  have hhalf :
      (2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * r) =
        ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * r) := by
    calc
      (2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * r)
          = (2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ (2 * r) := by rw [hsymm]
      _ = (2 : ℝ) * ((1 / 2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * r)) := by
            rw [EulerSine.integral_cos_pow_eq]
      _ = ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * r) := by
            ring
  calc
    Omega.POM.arcsineAverage (fun μ => μ ^ r)
        = (1 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi, (2 * (1 - Real.cos x)) ^ r := by
            simp [Omega.POM.arcsineAverage]
    _ = (1 / Real.pi) * ((2 : ℝ) *
          ∫ x in (0 : ℝ)..Real.pi / 2, (2 * (1 - Real.cos (2 * x))) ^ r) := by rw [hcomp.symm]
    _ = (1 / Real.pi) * ((2 : ℝ) *
          ((4 : ℝ) ^ r * ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * r))) := by rw [hpow]
    _ = (1 / Real.pi) * ((4 : ℝ) ^ r * ((2 : ℝ) *
          ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ (2 * r))) := by ring
    _ = (1 / Real.pi) * ((4 : ℝ) ^ r * ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * r)) := by
          rw [hhalf]
    _ = (1 / Real.pi) * ((4 : ℝ) ^ r *
          (Real.pi * ∏ i ∈ Finset.range r, (2 * (i : ℝ) + 1) / (2 * i + 2))) := by
          rw [integral_sin_pow_even]
    _ = (4 : ℝ) ^ r * ∏ i ∈ Finset.range r, (2 * (i : ℝ) + 1) / (2 * i + 2) := by
          field_simp [Real.pi_ne_zero]

private lemma four_pow_mul_wallis_prod_eq_central_binomial (r : ℕ) :
    (4 : ℝ) ^ r * ∏ i ∈ Finset.range r, (2 * (i : ℝ) + 1) / (2 * i + 2) =
      (Nat.choose (2 * r) r : ℝ) := by
  induction r with
  | zero =>
      simp
  | succ r ihr =>
      have hrecNat := Nat.succ_mul_centralBinom_succ r
      have hrec :
          ((r + 1 : ℝ) * (Nat.choose (2 * (r + 1)) (r + 1) : ℝ)) =
            (2 : ℝ) * (2 * r + 1) * (Nat.choose (2 * r) r : ℝ) := by
        exact_mod_cast hrecNat
      have hr1 : (r + 1 : ℝ) ≠ 0 := by positivity
      have hr2 : (2 * (r : ℝ) + 2) ≠ 0 := by positivity
      have hchooseDiv :
          (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) =
            ((4 : ℝ) * (2 * r + 1) * (Nat.choose (2 * r) r : ℝ)) / (2 * r + 2) := by
        apply (eq_div_iff hr2).2
        have hrec' :
            (2 * (r : ℝ) + 2) * (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) =
              (4 : ℝ) * (2 * r + 1) * (Nat.choose (2 * r) r : ℝ) := by
          nlinarith [hrec]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hrec'
      have hchoose :
          (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) =
            (4 : ℝ) * ((2 * (r : ℝ) + 1) / (2 * r + 2)) * (Nat.choose (2 * r) r : ℝ) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hchooseDiv
      calc
        (4 : ℝ) ^ (r + 1) * ∏ i ∈ Finset.range (r + 1), (2 * (i : ℝ) + 1) / (2 * i + 2)
            = (4 : ℝ) * ((2 * (r : ℝ) + 1) / (2 * r + 2)) *
                ((4 : ℝ) ^ r * ∏ i ∈ Finset.range r, (2 * (i : ℝ) + 1) / (2 * i + 2)) := by
                  rw [pow_succ', Finset.prod_range_succ_comm]
                  ring
        _ = (4 : ℝ) * ((2 * (r : ℝ) + 1) / (2 * r + 2)) * (Nat.choose (2 * r) r : ℝ) := by
              rw [ihr]
        _ = (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) := by rw [hchoose]

/-- Paper label: `cor:conclusion-Lk-central-binomial-catalan-moments`. -/
theorem paper_conclusion_lk_central_binomial_catalan_moments (r : ℕ) :
    Omega.POM.arcsineAverage (fun μ => μ ^ r) = (Nat.choose (2 * r) r : ℝ) ∧
      (r + 2) * Omega.POM.CatalanMoments.catalanNumber (r + 1) = Nat.choose (2 * r + 2) (r + 1) := by
  constructor
  · rw [arcsineAverage_nat_moment_closed_form r, four_pow_mul_wallis_prod_eq_central_binomial]
  · unfold Omega.POM.CatalanMoments.catalanNumber
    have hdvd : r + 2 ∣ Nat.choose (2 * (r + 1)) (r + 1) := by
      simpa [Nat.centralBinom_eq_two_mul_choose, two_mul, add_assoc, add_left_comm, add_comm] using
        Nat.succ_dvd_centralBinom (r + 1)
    calc
      (r + 2) * (Nat.choose (2 * (r + 1)) (r + 1) / (r + 2))
          = Nat.choose (2 * (r + 1)) (r + 1) := Nat.mul_div_cancel' hdvd
      _ = Nat.choose (2 * r + 2) (r + 1) := by ring_nf

end Omega.Conclusion
