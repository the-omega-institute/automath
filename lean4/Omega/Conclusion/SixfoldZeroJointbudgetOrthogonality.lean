import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing sharp-threshold inequalities for the probability that at least one of `N`
independent Bernoulli-`p` trials hits. The subcritical side is the union bound
`1 - (1 - p)^N ≤ N p`, and the supercritical side is the exponential lower estimate
`1 - exp(-Np) ≤ 1 - (1 - p)^N`.
    thm:conclusion-sixfold-zero-random-hit-sharp-threshold -/
theorem paper_conclusion_sixfold_zero_random_hit_sharp_threshold (M : ℕ) (p theta : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    let N : ℕ := Nat.floor (Real.rpow (M : ℝ) theta)
    1 - (1 - p) ^ N ≤ (N : ℝ) * p ∧ (1 - Real.exp (-((N : ℝ) * p)) ≤ 1 - (1 - p) ^ N) := by
  let N : ℕ := Nat.floor (Real.rpow (M : ℝ) theta)
  change 1 - (1 - p) ^ N ≤ (N : ℝ) * p ∧ (1 - Real.exp (-((N : ℝ) * p)) ≤ 1 - (1 - p) ^ N)
  let a : ℝ := 1 - p
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    linarith [hp.2]
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    linarith [hp.1]
  have h_union : 1 - a ^ N ≤ (N : ℝ) * p := by
    induction' N with n ihn
    · simp
    · have hpow_le_one : a ^ n ≤ 1 := by
        exact pow_le_one₀ ha_nonneg ha_le_one
      have hmul_le : a ^ n * p ≤ p := by
        simpa using mul_le_mul_of_nonneg_right hpow_le_one hp.1
      calc
        1 - a ^ (n + 1) = (1 - a ^ n) + a ^ n * p := by
          rw [pow_succ']
          dsimp [a]
          ring
        _ ≤ (n : ℝ) * p + p := add_le_add ihn hmul_le
        _ = ((n + 1 : ℕ) : ℝ) * p := by
          norm_num
          ring
  have h_exp : a ^ N ≤ Real.exp (-((N : ℝ) * p)) := by
    have hstep : a ≤ Real.exp (-p) := by
      simpa [a] using Real.one_sub_le_exp_neg p
    induction' N with n ihn
    · simp
    · calc
        a ^ (n + 1) = a ^ n * a := by rw [pow_succ, mul_comm]
        _ ≤ Real.exp (-((n : ℝ) * p)) * Real.exp (-p) := by
          exact mul_le_mul ihn hstep ha_nonneg (by positivity)
        _ = Real.exp (-(((n : ℝ) * p) + p)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ = Real.exp (-(p * (((n + 1 : ℕ) : ℝ))) ) := by
          congr 1
          rw [Nat.cast_add, Nat.cast_one]
          ring
        _ = Real.exp (-(((n + 1 : ℕ) : ℝ) * p)) := by
          congr 1
          ring
  constructor
  · simpa [N, a] using h_union
  · simpa [N, a] using sub_le_sub_left h_exp 1

/-- Paper-facing fixed-confidence squeeze: the subcritical half-rate witness is bounded above by
the union estimate, while the supercritical half-rate witness is bounded below by the exponential
estimate. -/
def conclusion_sixfold_zero_fixed_confidence_sample_complexity_statement : Prop :=
  ∀ (M : ℕ) (p ε : ℝ), 0 ≤ p ∧ p ≤ 1 →
    let Nsub : ℕ := Nat.floor (Real.rpow (M : ℝ) ((1 / 2 : ℝ) - ε))
    let Nsuper : ℕ := Nat.floor (Real.rpow (M : ℝ) ((1 / 2 : ℝ) + ε))
    1 - (1 - p) ^ Nsub ≤ (Nsub : ℝ) * p ∧
      1 - Real.exp (-((Nsuper : ℝ) * p)) ≤ 1 - (1 - p) ^ Nsuper

/-- Paper label:
`cor:conclusion-sixfold-zero-fixed-confidence-sample-complexity`. -/
theorem paper_conclusion_sixfold_zero_fixed_confidence_sample_complexity :
    conclusion_sixfold_zero_fixed_confidence_sample_complexity_statement := by
  intro M p ε hp
  dsimp only
  constructor
  · exact (paper_conclusion_sixfold_zero_random_hit_sharp_threshold
      M p ((1 / 2 : ℝ) - ε) hp).1
  · exact (paper_conclusion_sixfold_zero_random_hit_sharp_threshold
      M p ((1 / 2 : ℝ) + ε) hp).2

end Omega.Conclusion
