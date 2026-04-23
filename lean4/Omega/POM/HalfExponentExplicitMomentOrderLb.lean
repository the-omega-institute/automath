import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

noncomputable def pom_half_exponent_explicit_moment_order_lb_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- Paper label: `prop:pom-half-exponent-explicit-moment-order-lb`. -/
theorem paper_pom_half_exponent_explicit_moment_order_lb :
    ∀ {a ε m n_m A_m Q_m : ℝ},
      0 < ε →
      Real.exp ((Real.log pom_half_exponent_explicit_moment_order_lb_phi - ε) * m) ≤ n_m →
      A_m ≤ Real.exp ((a / 2 + ε) * m) →
      n_m / Real.sqrt Q_m ≤ ε * A_m →
      0 < Q_m →
      (2 * Real.log pom_half_exponent_explicit_moment_order_lb_phi - a - 4 * ε) * m -
          2 * Real.log ε ≤
        Real.log Q_m := by
  intro a ε m n_m A_m Q_m hε hn hA happrox hQ
  have hn_pos : 0 < n_m := lt_of_lt_of_le (Real.exp_pos _) hn
  have hsqrtQ_pos : 0 < Real.sqrt Q_m := Real.sqrt_pos.2 hQ
  have hleft_pos : 0 < n_m / Real.sqrt Q_m := by positivity
  have hεA_pos : 0 < ε * A_m := lt_of_lt_of_le hleft_pos happrox
  have hA_pos : 0 < A_m := by
    by_contra hA_nonpos
    have hA_le : A_m ≤ 0 := le_of_not_gt hA_nonpos
    have : ε * A_m ≤ 0 := by nlinarith
    exact not_lt_of_ge this hεA_pos
  have hlog_rel : Real.log (n_m / Real.sqrt Q_m) ≤ Real.log (ε * A_m) :=
    Real.log_le_log hleft_pos happrox
  have hlog_n : (Real.log pom_half_exponent_explicit_moment_order_lb_phi - ε) * m ≤ Real.log n_m := by
    have := Real.log_le_log (Real.exp_pos _) hn
    simpa [Real.log_exp] using this
  have hlog_A : Real.log A_m ≤ (a / 2 + ε) * m := by
    have := Real.log_le_log hA_pos hA
    simpa [Real.log_exp] using this
  rw [Real.log_div hn_pos.ne' hsqrtQ_pos.ne', Real.log_mul hε.ne' hA_pos.ne'] at hlog_rel
  have hsqrt_log : Real.log (Real.sqrt Q_m) = (1 / 2 : ℝ) * Real.log Q_m := by
    rw [Real.log_sqrt hQ.le]
    ring
  rw [hsqrt_log] at hlog_rel
  linarith

end Omega.POM
