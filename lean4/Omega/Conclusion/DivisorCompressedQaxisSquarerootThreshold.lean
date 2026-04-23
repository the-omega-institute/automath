import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the divisor-compressed `q`-axis square-root threshold package. The
compressed axis value is modeled by a dominant `lambdaRel ^ q` term together with a geometric tail
of order `lambdaRel ^ (2 q)`. -/
structure conclusion_divisor_compressed_qaxis_squareroot_threshold_data where
  q : ℕ
  lambdaRel : ℝ
  rho : ℝ
  mainCoeff : ℝ
  tailCoeff : ℝ
  kernelRH : Prop
  hrho : 0 < rho
  hlambda : 0 ≤ lambdaRel
  htail : 0 ≤ tailCoeff
  hkernel : kernelRH ↔ lambdaRel ≤ 1 / Real.sqrt rho
  hsqrt_tail : lambdaRel ^ (2 * q) ≤ (1 / Real.sqrt rho) ^ q

/-- The `l = 1` contribution. -/
def conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term
    (D : conclusion_divisor_compressed_qaxis_squareroot_threshold_data) : ℝ :=
  D.mainCoeff * D.lambdaRel ^ D.q

/-- The compressed `l ≥ 2` geometric tail surrogate. -/
def conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term
    (D : conclusion_divisor_compressed_qaxis_squareroot_threshold_data) : ℝ :=
  D.tailCoeff * D.lambdaRel ^ (2 * D.q)

/-- The divisor-compressed `q`-axis observable. -/
def conclusion_divisor_compressed_qaxis_squareroot_threshold_signal
    (D : conclusion_divisor_compressed_qaxis_squareroot_threshold_data) : ℝ :=
  conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D +
    conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term D

/-- The concrete `rho^(-q/2)` envelope, encoded as `(1 / sqrt rho)^q`. -/
noncomputable def conclusion_divisor_compressed_qaxis_squareroot_threshold_rho_neg_half_pow
    (D : conclusion_divisor_compressed_qaxis_squareroot_threshold_data) : ℝ :=
  (1 / Real.sqrt D.rho) ^ D.q

/-- The paper-facing square-root threshold consequence. -/
def conclusion_divisor_compressed_qaxis_squareroot_threshold_data.sqrt_threshold_statement
    (D : conclusion_divisor_compressed_qaxis_squareroot_threshold_data) : Prop :=
  conclusion_divisor_compressed_qaxis_squareroot_threshold_signal D =
      conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D +
        conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term D ∧
    |conclusion_divisor_compressed_qaxis_squareroot_threshold_signal D -
        conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D| ≤
      D.tailCoeff * D.lambdaRel ^ (2 * D.q) ∧
    (D.kernelRH ↔ D.lambdaRel ≤ 1 / Real.sqrt D.rho) ∧
    |conclusion_divisor_compressed_qaxis_squareroot_threshold_signal D -
        conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D| ≤
      D.tailCoeff * conclusion_divisor_compressed_qaxis_squareroot_threshold_rho_neg_half_pow D

open conclusion_divisor_compressed_qaxis_squareroot_threshold_data

/-- Paper label: `thm:conclusion-divisor-compressed-qaxis-squareroot-threshold`. -/
theorem paper_conclusion_divisor_compressed_qaxis_squareroot_threshold
    (D : conclusion_divisor_compressed_qaxis_squareroot_threshold_data) :
    D.sqrt_threshold_statement := by
  have htail_nonneg :
      0 ≤ conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term D := by
    unfold conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term
    exact mul_nonneg D.htail (pow_nonneg D.hlambda _)
  have hdiff :
      conclusion_divisor_compressed_qaxis_squareroot_threshold_signal D -
          conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D =
        conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term D := by
    unfold conclusion_divisor_compressed_qaxis_squareroot_threshold_signal
    ring
  have hdiff_abs :
      |conclusion_divisor_compressed_qaxis_squareroot_threshold_signal D -
          conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D| =
        conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term D := by
    rw [hdiff, abs_of_nonneg htail_nonneg]
  refine ⟨rfl, ?_, D.hkernel, ?_⟩
  · calc
      |conclusion_divisor_compressed_qaxis_squareroot_threshold_signal D -
          conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D| =
          conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term D := hdiff_abs
      _ = D.tailCoeff * D.lambdaRel ^ (2 * D.q) := rfl
      _ ≤ D.tailCoeff * D.lambdaRel ^ (2 * D.q) := le_rfl
  · calc
      |conclusion_divisor_compressed_qaxis_squareroot_threshold_signal D -
          conclusion_divisor_compressed_qaxis_squareroot_threshold_main_term D| =
          conclusion_divisor_compressed_qaxis_squareroot_threshold_tail_term D := hdiff_abs
      _ = D.tailCoeff * D.lambdaRel ^ (2 * D.q) := rfl
      _ ≤ D.tailCoeff * conclusion_divisor_compressed_qaxis_squareroot_threshold_rho_neg_half_pow D := by
            unfold conclusion_divisor_compressed_qaxis_squareroot_threshold_rho_neg_half_pow
            exact mul_le_mul_of_nonneg_left D.hsqrt_tail D.htail

end Omega.Conclusion
