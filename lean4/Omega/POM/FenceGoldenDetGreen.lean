import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.Entropy
import Omega.POM.GreenKernelEntries

namespace Omega.POM

open scoped goldenRatio

private lemma goldenRatio_inv_eq_neg_goldenConj : (Real.goldenRatio : ℝ)⁻¹ = -Real.goldenConj := by
  simpa [one_div] using Real.inv_goldenRatio

private lemma fib_binet_mul_sqrt5 (n : ℕ) :
    Real.goldenRatio ^ n - Real.goldenConj ^ n = (Nat.fib n : ℝ) * Real.sqrt 5 := by
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  have hbinet := Omega.Entropy.binet_formula n
  field_simp [hsqrt5_ne] at hbinet
  linarith

private lemma goldenRatio_pow_inv_even (n : ℕ) :
    (Real.goldenRatio ^ (2 * n))⁻¹ = Real.goldenConj ^ (2 * n) := by
  calc
    (Real.goldenRatio ^ (2 * n))⁻¹ = (Real.goldenRatio⁻¹ : ℝ) ^ (2 * n) := by rw [inv_pow]
    _ = (-Real.goldenConj) ^ (2 * n) := by rw [goldenRatio_inv_eq_neg_goldenConj]
    _ = Real.goldenConj ^ (2 * n) := by simp

private lemma goldenRatio_pow_inv_odd (n : ℕ) :
    (Real.goldenRatio ^ (2 * n + 1))⁻¹ = -(Real.goldenConj ^ (2 * n + 1)) := by
  have hneg_even : (-Real.goldenConj) ^ (2 * n) = Real.goldenConj ^ (2 * n) := by
    have hsq : (-Real.goldenConj) ^ 2 = Real.goldenConj ^ 2 := by ring
    calc
      (-Real.goldenConj) ^ (2 * n) = ((-Real.goldenConj) ^ 2) ^ n := by
            rw [show 2 * n = 2 * n by rfl, pow_mul]
      _ = (Real.goldenConj ^ 2) ^ n := by rw [hsq]
      _ = Real.goldenConj ^ (2 * n) := by rw [← pow_mul]
  calc
    (Real.goldenRatio ^ (2 * n + 1))⁻¹ = (Real.goldenRatio⁻¹ : ℝ) ^ (2 * n + 1) := by rw [inv_pow]
    _ = (-Real.goldenConj) ^ (2 * n + 1) := by rw [goldenRatio_inv_eq_neg_goldenConj]
    _ = -(Real.goldenConj ^ (2 * n + 1)) := by
          rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_add, pow_one, hneg_even]
          ring

private lemma sinh_even_log_phi (n : ℕ) :
    Real.sinh ((2 * n : ℝ) * Real.log Real.goldenRatio) = (Nat.fib (2 * n) : ℝ) * (Real.sqrt 5 / 2) := by
  have hpow_pos : 0 < Real.goldenRatio ^ (2 * n : ℝ) := by positivity
  have hphi_nat : Real.goldenRatio ^ (2 * n : ℝ) = (Real.goldenRatio ^ (2 * n) : ℝ) := by
    rw [show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by exact_mod_cast rfl, Real.rpow_natCast]
  calc
    Real.sinh ((2 * n : ℝ) * Real.log Real.goldenRatio)
        = Real.sinh (Real.log (Real.goldenRatio ^ (2 * n : ℝ))) := by
            congr 1
            rw [Real.log_rpow Real.goldenRatio_pos]
    _ = ((Real.goldenRatio ^ (2 * n : ℝ)) - (Real.goldenRatio ^ (2 * n : ℝ))⁻¹) / 2 := by
          rw [Real.sinh_log hpow_pos]
    _ = ((Real.goldenRatio ^ (2 * n)) - Real.goldenConj ^ (2 * n)) / 2 := by
          rw [hphi_nat, goldenRatio_pow_inv_even]
    _ = (Nat.fib (2 * n) : ℝ) * (Real.sqrt 5 / 2) := by
          rw [fib_binet_mul_sqrt5]
          ring

private lemma cosh_odd_log_phi (n : ℕ) :
    Real.cosh ((2 * n + 1 : ℝ) * Real.log Real.goldenRatio) =
      (Nat.fib (2 * n + 1) : ℝ) * (Real.sqrt 5 / 2) := by
  have hpow_pos : 0 < Real.goldenRatio ^ (2 * n + 1 : ℝ) := by positivity
  have hphi_nat : Real.goldenRatio ^ (2 * n + 1 : ℝ) = (Real.goldenRatio ^ (2 * n + 1) : ℝ) := by
    rw [show (2 * n + 1 : ℝ) = ((2 * n + 1 : ℕ) : ℝ) by exact_mod_cast rfl, Real.rpow_natCast]
  calc
    Real.cosh ((2 * n + 1 : ℝ) * Real.log Real.goldenRatio)
        = Real.cosh (Real.log (Real.goldenRatio ^ (2 * n + 1 : ℝ))) := by
            congr 1
            rw [Real.log_rpow Real.goldenRatio_pos]
    _ = ((Real.goldenRatio ^ (2 * n + 1 : ℝ)) + (Real.goldenRatio ^ (2 * n + 1 : ℝ))⁻¹) / 2 := by
          rw [Real.cosh_log hpow_pos]
    _ = ((Real.goldenRatio ^ (2 * n + 1)) - Real.goldenConj ^ (2 * n + 1)) / 2 := by
          rw [hphi_nat, goldenRatio_pow_inv_odd]
          ring
    _ = (Nat.fib (2 * n + 1) : ℝ) * (Real.sqrt 5 / 2) := by
          rw [fib_binet_mul_sqrt5]
          ring

/-- Paper label: `cor:pom-Lk-t1-fibonacci-det-green`. -/
theorem paper_pom_Lk_t1_fibonacci_det_green (k i j : ℕ)
    (hij : 1 ≤ i ∧ i ≤ j ∧ j ≤ k) :
    fenceDet k = Nat.fib (2 * k + 1) ∧
      pomLkGreenEntry k 1 i j =
        ((Nat.fib (2 * i) : ℝ) * Nat.fib (2 * (k - j) + 1)) / Nat.fib (2 * k + 1) := by
  refine ⟨fenceDet_eq_fib k, ?_⟩
  rcases hij with ⟨hi, hij', hjk⟩
  have hsinh_i := sinh_even_log_phi i
  have hsinh_one := sinh_even_log_phi 1
  have hsinh_base : Real.sinh (2 * Real.log Real.goldenRatio) = (1 : ℝ) * (Real.sqrt 5 / 2) := by
    simpa using hsinh_one
  have hcosh_tail := cosh_odd_log_phi (k - j)
  have hcosh_tail' :
      Real.cosh ((2 * ((k : ℝ) - j) + 1) * Real.log Real.goldenRatio) =
        (Nat.fib (2 * (k - j) + 1) : ℝ) * (Real.sqrt 5 / 2) := by
    simpa [Nat.cast_sub hjk] using hcosh_tail
  have hcosh_k := cosh_odd_log_phi k
  have hsqrt5_half_ne : (Real.sqrt 5 / 2 : ℝ) ≠ 0 := by positivity
  have hfibk_pos : 0 < Nat.fib (2 * k + 1) := Nat.fib_pos.mpr (by omega)
  have hfibk_ne : (Nat.fib (2 * k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfibk_pos
  calc
    pomLkGreenEntry k 1 i j
        = (Real.sinh ((2 * i : ℝ) * pomEta 1) * Real.cosh ((2 * (k - j) + 1 : ℝ) * pomEta 1)) /
            (Real.sinh (2 * pomEta 1) * Real.cosh ((2 * k + 1 : ℝ) * pomEta 1)) := by
              simpa using paper_pom_Lk_green_kernel_entries k i j 1 ⟨hi, hij', hjk⟩
    _ = (((Nat.fib (2 * i) : ℝ) * (Real.sqrt 5 / 2)) *
          ((Nat.fib (2 * (k - j) + 1) : ℝ) * (Real.sqrt 5 / 2))) /
          (((Nat.fib 2 : ℝ) * (Real.sqrt 5 / 2)) *
            ((Nat.fib (2 * k + 1) : ℝ) * (Real.sqrt 5 / 2))) := by
              dsimp [pomEta]
              simp only [one_mul]
              rw [hsinh_i, hsinh_base, hcosh_tail', hcosh_k]
              norm_num
    _ = ((Nat.fib (2 * i) : ℝ) * Nat.fib (2 * (k - j) + 1)) / Nat.fib (2 * k + 1) := by
          field_simp [hsqrt5_half_ne, hfibk_ne]
          ring

end Omega.POM
