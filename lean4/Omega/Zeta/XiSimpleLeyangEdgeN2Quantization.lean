import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Simple edge model obtained after removing the exponentially small remainder. -/
noncomputable def xi_simple_leyang_edge_n2_quantization_model (y : ℂ) : ℂ :=
  y ^ 2 + 1

/-- Positive dominant branch of the quantized simple-edge model. -/
noncomputable def xi_simple_leyang_edge_n2_quantization_dominant_root_pos : ℂ :=
  Complex.I

/-- Negative dominant branch of the quantized simple-edge model. -/
noncomputable def xi_simple_leyang_edge_n2_quantization_dominant_root_neg : ℂ :=
  -Complex.I

/-- The exponentially small remainder has been separated off in the simple model. -/
def xi_simple_leyang_edge_n2_quantization_remainder (_y : ℂ) : ℂ :=
  0

/-- Concrete simple-edge quantization package: the two dominant branches solve the model equation,
they are distinct, and the derivative `2 y` is nonzero on both branches. -/
def xi_simple_leyang_edge_n2_quantization_statement : Prop :=
  xi_simple_leyang_edge_n2_quantization_remainder
      xi_simple_leyang_edge_n2_quantization_dominant_root_pos = 0 ∧
    xi_simple_leyang_edge_n2_quantization_model
        xi_simple_leyang_edge_n2_quantization_dominant_root_pos = 0 ∧
    xi_simple_leyang_edge_n2_quantization_model
        xi_simple_leyang_edge_n2_quantization_dominant_root_neg = 0 ∧
    xi_simple_leyang_edge_n2_quantization_dominant_root_pos ≠
      xi_simple_leyang_edge_n2_quantization_dominant_root_neg ∧
    (2 : ℂ) * xi_simple_leyang_edge_n2_quantization_dominant_root_pos ≠ 0 ∧
    (2 : ℂ) * xi_simple_leyang_edge_n2_quantization_dominant_root_neg ≠ 0

/-- Paper label: `thm:xi-simple-leyang-edge-n2-quantization`. -/
theorem paper_xi_simple_leyang_edge_n2_quantization :
    xi_simple_leyang_edge_n2_quantization_statement := by
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpos_deriv :
      (2 : ℂ) * xi_simple_leyang_edge_n2_quantization_dominant_root_pos ≠ 0 := by
    exact mul_ne_zero htwo_ne (by simpa [xi_simple_leyang_edge_n2_quantization_dominant_root_pos]
      using Complex.I_ne_zero)
  have hneg_root_ne :
      xi_simple_leyang_edge_n2_quantization_dominant_root_neg ≠ 0 := by
    simpa [xi_simple_leyang_edge_n2_quantization_dominant_root_neg, neg_eq_zero] using
      Complex.I_ne_zero
  have hneg_deriv :
      (2 : ℂ) * xi_simple_leyang_edge_n2_quantization_dominant_root_neg ≠ 0 := by
    exact mul_ne_zero htwo_ne hneg_root_ne
  refine ⟨rfl, ?_, ?_, ?_, hpos_deriv, hneg_deriv⟩
  · simp [xi_simple_leyang_edge_n2_quantization_model,
      xi_simple_leyang_edge_n2_quantization_dominant_root_pos, Complex.I_sq]
  · simp [xi_simple_leyang_edge_n2_quantization_model,
      xi_simple_leyang_edge_n2_quantization_dominant_root_neg, Complex.I_sq]
  · intro hEq
    have hsum : (Complex.I : ℂ) + Complex.I = 0 := by
      simpa [xi_simple_leyang_edge_n2_quantization_dominant_root_pos,
        xi_simple_leyang_edge_n2_quantization_dominant_root_neg] using
        eq_neg_iff_add_eq_zero.mp hEq
    have hmul : (2 : ℂ) * Complex.I = 0 := by
      simpa [two_mul] using hsum
    exact hpos_deriv hmul

end Omega.Zeta
