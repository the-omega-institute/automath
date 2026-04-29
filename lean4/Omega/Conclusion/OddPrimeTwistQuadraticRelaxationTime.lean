import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the odd-prime twist quadratic relaxation-time law. The log of the
normalized twisted spectral ratio is encoded by `logDecay`, and the relaxation time solves the
envelope inequality exactly after taking logarithms. -/
structure conclusion_odd_prime_twist_quadratic_relaxation_time_data where
  p : ℕ
  ε : ℝ
  Aphi : ℝ
  logDecay : ℝ
  inverseLogError : ℝ
  relaxationTime : ℝ
  hPrime : Nat.Prime p
  hOdd : p ≠ 2
  hEps : 0 < ε ∧ ε < 1
  hAphiPos : 0 < Aphi
  hLogDecayPos : 0 < logDecay
  hInverseLogErrorNonneg : 0 ≤ inverseLogError
  hRelaxationSolve :
    relaxationTime = Real.log ((p : ℝ) / ε) / logDecay
  hInverseLogApprox :
    |logDecay⁻¹ - (p : ℝ) ^ 2 / Aphi| ≤ inverseLogError

namespace conclusion_odd_prime_twist_quadratic_relaxation_time_data

/-- Main quadratic term `(p² / A_φ) log(p / ε)`. -/
noncomputable def conclusion_odd_prime_twist_quadratic_relaxation_time_main_term
    (D : conclusion_odd_prime_twist_quadratic_relaxation_time_data) : ℝ :=
  ((D.p : ℝ) ^ 2 / D.Aphi) * Real.log ((D.p : ℝ) / D.ε)

/-- The fixed-`ε` multiplier converting `log (p / ε)` into a multiple of `log p` for odd primes
`p ≥ 3`. -/
noncomputable def conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier
    (D : conclusion_odd_prime_twist_quadratic_relaxation_time_data) : ℝ :=
  1 + Real.log (1 / D.ε) / Real.log 3

/-- The relaxation time equals the quadratic main term up to an `O(log p)` remainder. -/
def quadratic_relaxation_asymptotic
    (D : conclusion_odd_prime_twist_quadratic_relaxation_time_data) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    |D.relaxationTime -
        D.conclusion_odd_prime_twist_quadratic_relaxation_time_main_term| ≤
      K * Real.log (D.p : ℝ)

end conclusion_odd_prime_twist_quadratic_relaxation_time_data

open conclusion_odd_prime_twist_quadratic_relaxation_time_data

/-- Paper label: `thm:conclusion-odd-prime-twist-quadratic-relaxation-time`. -/
theorem paper_conclusion_odd_prime_twist_quadratic_relaxation_time
    (D : conclusion_odd_prime_twist_quadratic_relaxation_time_data) :
    D.quadratic_relaxation_asymptotic := by
  have hp_ge_three : 3 ≤ D.p := by
    have hp_gt_two : 2 < D.p := lt_of_le_of_ne D.hPrime.two_le D.hOdd.symm
    omega
  have hp_pos : 0 < (D.p : ℝ) := by
    exact_mod_cast D.hPrime.pos
  have hp_ge_three_real : (3 : ℝ) ≤ D.p := by
    exact_mod_cast hp_ge_three
  have hlog3_pos : 0 < Real.log 3 := by
    exact Real.log_pos (by norm_num)
  have hlogp_ge_log3 : Real.log 3 ≤ Real.log (D.p : ℝ) := by
    exact Real.log_le_log (by norm_num) hp_ge_three_real
  have hlogp_nonneg : 0 ≤ Real.log (D.p : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast D.hPrime.one_lt.le)
  have hloginv_nonneg : 0 ≤ Real.log (1 / D.ε) := by
    have hInvGtOne : 1 < 1 / D.ε := by
      rw [one_lt_div D.hEps.1]
      simpa using D.hEps.2
    exact Real.log_nonneg hInvGtOne.le
  have hlog_multiplier_nonneg :
      0 ≤ D.conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier := by
    unfold conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier
    positivity
  have hloginv_le :
      Real.log (1 / D.ε) ≤
        (Real.log (1 / D.ε) / Real.log 3) * Real.log (D.p : ℝ) := by
    have hcoeff_nonneg : 0 ≤ Real.log (1 / D.ε) / Real.log 3 := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hlogp_ge_log3 hcoeff_nonneg
    calc
      Real.log (1 / D.ε)
          = (Real.log (1 / D.ε) / Real.log 3) * Real.log 3 := by
              field_simp [hlog3_pos.ne']
      _ ≤ (Real.log (1 / D.ε) / Real.log 3) * Real.log (D.p : ℝ) := hscaled
  have hlog_ratio :
      Real.log ((D.p : ℝ) / D.ε) = Real.log (D.p : ℝ) + Real.log (1 / D.ε) := by
    rw [div_eq_mul_inv, Real.log_mul]
    · ring
    · exact_mod_cast D.hPrime.ne_zero
    · exact inv_ne_zero D.hEps.1.ne'
  have hlog_ratio_nonneg : 0 ≤ Real.log ((D.p : ℝ) / D.ε) := by
    rw [hlog_ratio]
    linarith
  have hlog_ratio_le :
      Real.log ((D.p : ℝ) / D.ε) ≤
        D.conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier *
          Real.log (D.p : ℝ) := by
    rw [hlog_ratio,
      conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier]
    have hadd :=
      add_le_add_right hloginv_le (Real.log (D.p : ℝ))
    calc
      Real.log (D.p : ℝ) + Real.log (1 / D.ε)
          = Real.log (1 / D.ε) + Real.log (D.p : ℝ) := by ring
      _ ≤
          (Real.log (1 / D.ε) / Real.log 3) * Real.log (D.p : ℝ) +
            Real.log (D.p : ℝ) := by
              simpa [add_comm, add_left_comm, add_assoc] using hadd
      _ = (1 + Real.log (1 / D.ε) / Real.log 3) * Real.log (D.p : ℝ) := by ring
  have hMainDiff :
      D.relaxationTime -
          D.conclusion_odd_prime_twist_quadratic_relaxation_time_main_term =
        Real.log ((D.p : ℝ) / D.ε) *
          (D.logDecay⁻¹ - (D.p : ℝ) ^ 2 / D.Aphi) := by
    rw [D.hRelaxationSolve,
      conclusion_odd_prime_twist_quadratic_relaxation_time_main_term,
      div_eq_mul_inv]
    ring
  refine ⟨D.inverseLogError *
      D.conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier, ?_, ?_⟩
  · exact mul_nonneg D.hInverseLogErrorNonneg hlog_multiplier_nonneg
  · rw [hMainDiff, abs_mul, abs_of_nonneg hlog_ratio_nonneg]
    calc
      Real.log ((D.p : ℝ) / D.ε) * |D.logDecay⁻¹ - (D.p : ℝ) ^ 2 / D.Aphi|
          ≤ Real.log ((D.p : ℝ) / D.ε) * D.inverseLogError := by
              gcongr
              exact D.hInverseLogApprox
      _ ≤
          (D.conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier *
              Real.log (D.p : ℝ)) * D.inverseLogError := by
                exact mul_le_mul_of_nonneg_right hlog_ratio_le D.hInverseLogErrorNonneg
      _ =
          (D.inverseLogError *
              D.conclusion_odd_prime_twist_quadratic_relaxation_time_log_multiplier) *
            Real.log (D.p : ℝ) := by ring

end Omega.Conclusion
