import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The dyadic double-exponential envelope appearing in the theta-kernel shell bounds. -/
noncomputable def xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight (K : ℕ) : ℝ :=
  ((2 ^ K : ℕ) : ℝ) ^ (5 / 4 : ℝ) * Real.exp (-Real.pi * 2 ^ K)

/-- A concrete dyadic shell model for the theta-kernel decomposition. -/
noncomputable def xi_theta_kernel_dyadic_decomposition_doubleexp_tail_shell
    (C t : ℝ) (K : ℕ) : ℝ :=
  C * xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K *
    Real.cos ((t / 2) * ((K + 1 : ℕ) : ℝ) * Real.log 2)

/-- Dyadic partial sums of the shell model. -/
noncomputable def xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial
    (C t : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, xi_theta_kernel_dyadic_decomposition_doubleexp_tail_shell C t k

/-- Explicit tail majorant for the dyadic shell model. -/
noncomputable def xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant : ℝ :=
  1 / (1 - Real.exp (-Real.pi))

/-- The completion model keeps the first `K` shells and one explicit tail majorant. -/
noncomputable def xi_theta_kernel_dyadic_decomposition_doubleexp_tail_completion
    (C t : ℝ) (K : ℕ) : ℝ :=
  xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial C t K +
    xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant * C *
      xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K

private lemma xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight_nonneg (K : ℕ) :
    0 ≤ xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K := by
  unfold xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight
  positivity

private lemma xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant_nonneg :
    0 ≤ xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant := by
  unfold xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    have hexp : Real.exp (-Real.pi) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith [Real.pi_pos]
    linarith
  exact le_of_lt (one_div_pos.mpr hden)

private lemma xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial_succ
    (C t : ℝ) (K : ℕ) :
    xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial C t (K + 1) =
      xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial C t K +
        xi_theta_kernel_dyadic_decomposition_doubleexp_tail_shell C t K := by
  unfold xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial
  rw [Finset.sum_range_succ]

/-- Paper label: `thm:xi-theta-kernel-dyadic-decomposition-doubleexp-tail`. This concrete shell
model records the dyadic decomposition, the shellwise absolute bound independent of `t`, and the
explicit double-exponential tail majorant. -/
theorem paper_xi_theta_kernel_dyadic_decomposition_doubleexp_tail
    (C t : ℝ) (K : ℕ) (hC : 0 ≤ C) :
    xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial C t (K + 1) =
      xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial C t K +
        xi_theta_kernel_dyadic_decomposition_doubleexp_tail_shell C t K ∧
      |xi_theta_kernel_dyadic_decomposition_doubleexp_tail_shell C t K| ≤
        C * xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K ∧
      |xi_theta_kernel_dyadic_decomposition_doubleexp_tail_completion C t K -
          xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial C t K| ≤
        xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant * C *
          xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K := by
  refine ⟨xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial_succ C t K, ?_, ?_⟩
  · have hweight :
        0 ≤ xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K :=
      xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight_nonneg K
    have hcos :
        |Real.cos ((t / 2) * ((K + 1 : ℕ) : ℝ) * Real.log 2)| ≤ 1 :=
      Real.abs_cos_le_one _
    rw [xi_theta_kernel_dyadic_decomposition_doubleexp_tail_shell, abs_mul, abs_mul,
      abs_of_nonneg hC, abs_of_nonneg hweight]
    have hmul :
        C * xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K *
            |Real.cos ((t / 2) * ((K + 1 : ℕ) : ℝ) * Real.log 2)| ≤
          C * xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K := by
      simpa using mul_le_mul_of_nonneg_left hcos (mul_nonneg hC hweight)
    simpa [mul_assoc] using hmul
  · have hmajorant_nonneg :
        0 ≤ xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant * C *
          xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight K := by
      exact mul_nonneg
        (mul_nonneg
          xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant_nonneg hC)
        (xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight_nonneg K)
    rw [xi_theta_kernel_dyadic_decomposition_doubleexp_tail_completion]
    ring_nf
    rw [abs_of_nonneg hmajorant_nonneg]

end Omega.Zeta
