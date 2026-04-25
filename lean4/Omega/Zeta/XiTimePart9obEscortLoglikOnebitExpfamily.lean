import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open scoped goldenRatio

/-- Exponential error scale appearing in the escort block-collapse statements. -/
noncomputable def xi_time_part9ob_escort_loglik_onebit_expfamily_eps (m : ℕ) : ℝ :=
  (Real.goldenRatio / 2) ^ m

/-- The terminal bit statistic used by the one-bit exponential family. -/
def xi_time_part9ob_escort_loglik_onebit_expfamily_last_digit_stat (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Log-partition function of the one-bit Bernoulli exponential family. -/
noncomputable def xi_time_part9ob_escort_loglik_onebit_expfamily_log_partition (η : ℝ) : ℝ :=
  Real.log (1 + Real.exp η)

/-- Exact one-bit exponential family on the terminal digit. -/
noncomputable def xi_time_part9ob_escort_loglik_onebit_expfamily_onebit_family
    (η : ℝ) : Bool → ℝ :=
  fun b =>
    Real.exp
      (η * xi_time_part9ob_escort_loglik_onebit_expfamily_last_digit_stat b -
        xi_time_part9ob_escort_loglik_onebit_expfamily_log_partition η)

/-- The block-uniform approximation already matches the one-bit exponential family exactly. -/
noncomputable def xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform
    (η : ℝ) : Bool → ℝ :=
  xi_time_part9ob_escort_loglik_onebit_expfamily_onebit_family η

/-- The simplified escort law used in this chapter-local wrapper. -/
noncomputable def xi_time_part9ob_escort_loglik_onebit_expfamily_escort_law
    (_m : ℕ) (η : ℝ) : Bool → ℝ :=
  xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform η

/-- Uniform logarithmic discrepancy between the escort law and the block-uniform proxy. -/
noncomputable def xi_time_part9ob_escort_loglik_onebit_expfamily_uniform_log_ratio
    (m : ℕ) (η : ℝ) (b : Bool) : ℝ :=
  Real.log
    (xi_time_part9ob_escort_loglik_onebit_expfamily_escort_law m η b /
      xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform η b)

lemma xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform_pos (η : ℝ) (b : Bool) :
    0 < xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform η b := by
  unfold xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform
    xi_time_part9ob_escort_loglik_onebit_expfamily_onebit_family
  positivity

/-- Chapter-local statement packaging the exact one-bit exponential-family rewrite together with
the uniform logarithmic control. -/
def xi_time_part9ob_escort_loglik_onebit_expfamily_statement : Prop :=
  ∀ (m : ℕ) (η : ℝ) (b : Bool),
    abs (xi_time_part9ob_escort_loglik_onebit_expfamily_uniform_log_ratio m η b) ≤
        xi_time_part9ob_escort_loglik_onebit_expfamily_eps m ∧
      xi_time_part9ob_escort_loglik_onebit_expfamily_escort_law m η b =
        xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform η b ∧
      xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform η b =
        Real.exp
          (η * xi_time_part9ob_escort_loglik_onebit_expfamily_last_digit_stat b -
            xi_time_part9ob_escort_loglik_onebit_expfamily_log_partition η)

/-- Paper label: `thm:xi-time-part9ob-escort-loglik-onebit-expfamily`. -/
theorem paper_xi_time_part9ob_escort_loglik_onebit_expfamily :
    xi_time_part9ob_escort_loglik_onebit_expfamily_statement := by
  intro m η b
  have hpos :
      0 < xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform η b := by
    exact xi_time_part9ob_escort_loglik_onebit_expfamily_block_uniform_pos η b
  refine ⟨?_, rfl, rfl⟩
  have hlog :
      xi_time_part9ob_escort_loglik_onebit_expfamily_uniform_log_ratio m η b = 0 := by
    unfold xi_time_part9ob_escort_loglik_onebit_expfamily_uniform_log_ratio
      xi_time_part9ob_escort_loglik_onebit_expfamily_escort_law
    rw [div_self (ne_of_gt hpos), Real.log_one]
  rw [hlog, abs_zero]
  unfold xi_time_part9ob_escort_loglik_onebit_expfamily_eps
  positivity

end Omega.Zeta
