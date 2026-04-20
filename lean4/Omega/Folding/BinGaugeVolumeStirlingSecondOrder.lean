import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

open Finset

/-- The pointwise second-order Stirling residual for `log(n!)`. -/
noncomputable def stirlingSecondOrderResidual (n : ℕ) : ℝ :=
  Real.log ((Nat.factorial n : ℝ)) -
    ((n : ℝ) * Real.log n - (n : ℝ) + Real.log n / 2 + Real.log (2 * Real.pi) / 2)

lemma log_two_pi_ge_eleven_sixths : (11 : ℝ) / 6 ≤ Real.log (2 * Real.pi) := by
  have hExp : Real.exp ((11 : ℝ) / 6) < 2 * Real.pi := by
    have h56_le :
        Real.exp ((5 : ℝ) / 6) ≤
          (∑ m ∈ Finset.range 5, ((5 : ℝ) / 6) ^ m / m.factorial) +
            ((5 : ℝ) / 6) ^ 5 * (5 + 1) / ((Nat.factorial 5 : ℝ) * 5) := by
      exact Real.exp_bound' (by positivity) (by norm_num) (n := 5) (by norm_num)
    have h56_num :
        (∑ m ∈ Finset.range 5, ((5 : ℝ) / 6) ^ m / m.factorial) +
            ((5 : ℝ) / 6) ^ 5 * (5 + 1) / ((Nat.factorial 5 : ℝ) * 5) <
          2.3012 := by
      norm_num
    have h56 : Real.exp ((5 : ℝ) / 6) < 2.3012 := lt_of_le_of_lt h56_le h56_num
    have hExpNum : Real.exp ((11 : ℝ) / 6) < 6.28 := by
      calc
        Real.exp ((11 : ℝ) / 6) = Real.exp 1 * Real.exp (5 / 6 : ℝ) := by
          rw [show ((11 : ℝ) / 6) = 1 + 5 / 6 by norm_num, Real.exp_add]
        _ < 2.7182818286 * 2.3012 := by
          gcongr
          exact Real.exp_one_lt_d9
        _ < 6.28 := by norm_num
    have hPi : (6.28 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_d2]
    exact hExpNum.trans hPi
  exact (Real.lt_log_iff_exp_lt (by positivity)).2 hExp |>.le

lemma stirlingSecondOrderResidual_eq_log_stirlingSeq_sub_log_sqrt_pi {n : ℕ} (hn : 1 ≤ n) :
    stirlingSecondOrderResidual n =
      Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) := by
  have hn0 : n ≠ 0 := by omega
  have hn0R : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by positivity) Real.pi_pos.ne']
  unfold stirlingSecondOrderResidual
  rw [Stirling.log_stirlingSeq_formula]
  rw [Real.log_div hn0R (Real.exp_ne_zero 1), Real.log_exp]
  rw [Real.log_mul (by positivity) hn0R, Real.log_sqrt Real.pi_pos.le]
  rw [hlog2pi]
  ring_nf

lemma stirlingSecondOrderResidual_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ stirlingSecondOrderResidual n := by
  have hn0 : n ≠ 0 := by omega
  unfold stirlingSecondOrderResidual
  linarith [Stirling.le_log_factorial_stirling (n := n) hn0]

lemma stirlingSecondOrderResidual_le_one_twelfth {n : ℕ} (hn : 1 ≤ n) :
    stirlingSecondOrderResidual n ≤ 1 / 12 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsqrt : Real.sqrt Real.pi ≤ Stirling.stirlingSeq (1 + m) :=
    Stirling.sqrt_pi_le_stirlingSeq (by positivity)
  have hmono :
      Stirling.stirlingSeq (1 + m) ≤ Real.exp 1 / Real.sqrt 2 := by
    simpa [Nat.add_comm, Stirling.stirlingSeq_one] using
      Stirling.stirlingSeq'_antitone (show 0 ≤ m by exact Nat.zero_le _)
  have hlog :
      Real.log (Stirling.stirlingSeq (1 + m)) ≤ Real.log (Stirling.stirlingSeq 1) := by
    calc
      Real.log (Stirling.stirlingSeq (1 + m)) ≤ Real.log (Real.exp 1 / Real.sqrt 2) := by
        exact Real.log_le_log (by simpa [Nat.add_comm] using Stirling.stirlingSeq'_pos m) hmono
      _ = Real.log (Stirling.stirlingSeq 1) := by rw [Stirling.stirlingSeq_one]
  have hres :
      stirlingSecondOrderResidual (1 + m) =
        Real.log (Stirling.stirlingSeq (1 + m)) - Real.log (Real.sqrt Real.pi) := by
    exact stirlingSecondOrderResidual_eq_log_stirlingSeq_sub_log_sqrt_pi (by omega)
  have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by positivity) Real.pi_pos.ne']
  have hconst :
      Real.log (Stirling.stirlingSeq 1) - Real.log (Real.sqrt Real.pi) =
        1 - Real.log (2 * Real.pi) / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div, Real.log_exp, Real.log_sqrt (by positivity),
      Real.log_sqrt Real.pi_pos.le]
    · rw [hlog2pi]
      ring_nf
    · positivity
    · positivity
  calc
    stirlingSecondOrderResidual (1 + m)
        = Real.log (Stirling.stirlingSeq (1 + m)) - Real.log (Real.sqrt Real.pi) := hres
    _ ≤ Real.log (Stirling.stirlingSeq 1) - Real.log (Real.sqrt Real.pi) := by linarith
    _ = 1 - Real.log (2 * Real.pi) / 2 := hconst
    _ ≤ 1 / 12 := by linarith [log_two_pi_ge_eleven_sixths]

/-- Summing the pointwise Stirling lower bound over a finite index set yields a global second-order
expansion with a nonnegative remainder bounded by `|α| / 12`. -/
theorem paper_fold_bin_gauge_volume_stirling_second_order {alpha : Type} [Fintype alpha]
    (d : alpha → ℕ) (hd : ∀ a, 1 ≤ d a) :
    ∃ R : ℝ,
      0 ≤ R ∧
        R ≤ (Fintype.card alpha : ℝ) / 12 ∧
          (Finset.univ.sum fun a : alpha => Real.log ((Nat.factorial (d a) : ℝ))) =
            (Finset.univ.sum fun a : alpha => (d a : ℝ) * Real.log (d a) - (d a : ℝ)) +
              (1 / 2 : ℝ) *
                  ((Fintype.card alpha : ℝ) * Real.log (2 * Real.pi) +
                    Finset.univ.sum (fun a : alpha => Real.log (d a))) +
                R := by
  let R : ℝ := ∑ a : alpha, stirlingSecondOrderResidual (d a)
  refine ⟨R, ?_, ?_, ?_⟩
  · unfold R
    exact sum_nonneg fun a _ => stirlingSecondOrderResidual_nonneg (hd a)
  · unfold R
    calc
      (∑ a : alpha, stirlingSecondOrderResidual (d a)) ≤ ∑ a : alpha, (1 / 12 : ℝ) := by
        exact sum_le_sum fun a _ => stirlingSecondOrderResidual_le_one_twelfth (hd a)
      _ = (Fintype.card alpha : ℝ) / 12 := by
        rw [sum_const, nsmul_eq_mul, Finset.card_univ]
        ring_nf
  · have hhalf :
        (∑ a : alpha, (1 / 2 : ℝ) * (Real.log (2 * Real.pi) + Real.log (d a))) =
          (1 / 2 : ℝ) *
            ((Fintype.card alpha : ℝ) * Real.log (2 * Real.pi) +
              (∑ a : alpha, Real.log (d a))) := by
      rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, Finset.card_univ]
    calc
      (∑ a : alpha, Real.log ((Nat.factorial (d a) : ℝ)))
          = ∑ a : alpha,
              ((d a : ℝ) * Real.log (d a) - (d a : ℝ) +
                (1 / 2 : ℝ) * (Real.log (2 * Real.pi) + Real.log (d a)) +
                stirlingSecondOrderResidual (d a)) := by
              apply sum_congr rfl
              intro a ha
              unfold stirlingSecondOrderResidual
              ring
      _ = (∑ a : alpha, ((d a : ℝ) * Real.log (d a) - (d a : ℝ))) +
            (∑ a : alpha, (1 / 2 : ℝ) * (Real.log (2 * Real.pi) + Real.log (d a))) +
              ∑ a : alpha, stirlingSecondOrderResidual (d a) := by
            rw [sum_add_distrib, sum_add_distrib]
      _ = (∑ a : alpha, ((d a : ℝ) * Real.log (d a) - (d a : ℝ))) +
            (1 / 2 : ℝ) *
                ((Fintype.card alpha : ℝ) * Real.log (2 * Real.pi) +
                  (∑ a : alpha, Real.log (d a))) +
              R := by
            rw [hhalf]
      _ = (Finset.univ.sum fun a : alpha => (d a : ℝ) * Real.log (d a) - (d a : ℝ)) +
            (1 / 2 : ℝ) *
                ((Fintype.card alpha : ℝ) * Real.log (2 * Real.pi) +
                  Finset.univ.sum (fun a : alpha => Real.log (d a))) +
              R := by
            rfl

end Omega.Folding
