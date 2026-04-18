import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Perturbing the Möbius-inverted divisor average by replacing `a` with `ahat` changes the output
by at most the divisor-average of the pointwise errors. This is the triangle inequality together
with `|μ(d)| ≤ 1`. -/
theorem paper_mobius_error_propagation (a ahat : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    let p := (1 / (n : ℝ)) *
      Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℝ) * a (n / d))
    let phat := (1 / (n : ℝ)) *
      Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℝ) * ahat (n / d))
    |p - phat| ≤
      (1 / (n : ℝ)) * Finset.sum (Nat.divisors n) (fun d => |a (n / d) - ahat (n / d)|) := by
  dsimp
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hfactor_nonneg : 0 ≤ (1 / (n : ℝ)) := by
    positivity
  rw [← mul_sub, abs_mul, abs_of_nonneg hfactor_nonneg, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hfactor_nonneg
  calc
    |Finset.sum (Nat.divisors n) (fun d =>
        (ArithmeticFunction.moebius d : ℝ) * a (n / d) -
          (ArithmeticFunction.moebius d : ℝ) * ahat (n / d))|
      ≤ Finset.sum (Nat.divisors n) (fun d =>
          |(ArithmeticFunction.moebius d : ℝ) * a (n / d) -
            (ArithmeticFunction.moebius d : ℝ) * ahat (n / d)|) := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (Nat.divisors n) (fun d => |a (n / d) - ahat (n / d)|) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        calc
          |(ArithmeticFunction.moebius d : ℝ) * a (n / d) -
              (ArithmeticFunction.moebius d : ℝ) * ahat (n / d)|
            = |(ArithmeticFunction.moebius d : ℝ) * (a (n / d) - ahat (n / d))| := by
                rw [mul_sub]
          _ = |(ArithmeticFunction.moebius d : ℝ)| * |a (n / d) - ahat (n / d)| := by
                rw [abs_mul]
          _ ≤ 1 * |a (n / d) - ahat (n / d)| := by
                exact mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
          _ = |a (n / d) - ahat (n / d)| := by
                simp

/-- If the pointwise errors satisfy an exponential envelope `ε * ρ^m` up to level `n`, then the
Möbius-inverted divisor average inherits the same exponential envelope, with the divisor count as
the only combinatorial loss. -/
theorem paper_mobius_exp_bound (a ahat : ℕ → ℝ) (ε ρ : ℝ) {n : ℕ} (hn : 1 ≤ n) (hρ : 1 ≤ ρ)
    (hbound : ∀ m, 1 ≤ m → m ≤ n → |a m - ahat m| ≤ ε * ρ ^ m) :
    let p := (1 / (n : ℝ)) *
      Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℝ) * a (n / d))
    let phat := (1 / (n : ℝ)) *
      Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℝ) * ahat (n / d))
    |p - phat| ≤ ε * (((Nat.divisors n).card : ℝ) / n) * ρ ^ n := by
  dsimp
  have hbase : |(a n) - ahat n| ≤ ε * ρ ^ n := hbound n hn le_rfl
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hρn_pos : 0 < ρ ^ n := by exact pow_pos hρpos _
  have hερ_nonneg : 0 ≤ ε * ρ ^ n := le_trans (abs_nonneg _) hbase
  have hε_nonneg : 0 ≤ ε := by
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hερ_nonneg) hρn_pos
  have hfactor_nonneg : 0 ≤ (1 / (n : ℝ)) := by positivity
  have herror := paper_mobius_error_propagation a ahat hn
  refine herror.trans ?_
  have hsum :
      Finset.sum (Nat.divisors n) (fun d => |a (n / d) - ahat (n / d)|) ≤
        Finset.sum (Nat.divisors n) (fun _ => ε * ρ ^ n) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    rcases hdvd with ⟨k, hk⟩
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hk0
      have hn0 : n ≠ 0 := by omega
      exact hn0 (by simp [hk, hk0])
    have hquot : n / d = k := by
      simpa [hk, Nat.mul_comm] using (Nat.mul_div_right k hdpos)
    have hdiv_le_n : n / d ≤ n := Nat.div_le_self n d
    have hk_le_n : k ≤ n := by
      simpa [hquot] using hdiv_le_n
    have hpow : ρ ^ (n / d) ≤ ρ ^ n := by
      rw [hquot]
      exact pow_le_pow_right₀ hρ hk_le_n
    calc
      |a (n / d) - ahat (n / d)| ≤ ε * ρ ^ (n / d) := by
        exact hbound (n / d) (by simpa [hquot] using hkpos) hdiv_le_n
      _ ≤ ε * ρ ^ n := by
        exact mul_le_mul_of_nonneg_left hpow hε_nonneg
  calc
    (1 / (n : ℝ)) * Finset.sum (Nat.divisors n) (fun d => |a (n / d) - ahat (n / d)|)
      ≤ (1 / (n : ℝ)) * Finset.sum (Nat.divisors n) (fun _ => ε * ρ ^ n) := by
        exact mul_le_mul_of_nonneg_left hsum hfactor_nonneg
    _ = ε * (((Nat.divisors n).card : ℝ) / n) * ρ ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Omega.SyncKernelWeighted
