import Mathlib.Tactic

namespace Omega.Zeta

/-- Normalized cubic coefficient of the quartic in the translated primitive element. -/
def xi_terminal_zm_translation_r_trace_norm_a3 (y : ℚ) : ℚ :=
  (-y ^ 3 + 4 * y ^ 2 + 6 * y) / (y + 1) ^ 4

/-- Normalized quadratic coefficient of the quartic in the translated primitive element. -/
def xi_terminal_zm_translation_r_trace_norm_a2 (y : ℚ) : ℚ :=
  (-9 * y ^ 3 + 13 * y ^ 2 - 2 * y - 2) / (y + 1) ^ 4

/-- Normalized linear coefficient of the quartic in the translated primitive element. -/
def xi_terminal_zm_translation_r_trace_norm_a1 (y : ℚ) : ℚ :=
  (-5 * y * (y - 1) ^ 2) / (y + 1) ^ 4

/-- Normalized constant coefficient of the quartic in the translated primitive element. -/
def xi_terminal_zm_translation_r_trace_norm_a0 (y : ℚ) : ℚ :=
  (-(y - 1) ^ 3) / (y + 1) ^ 4

/-- Trace read from the normalized quartic. -/
def xi_terminal_zm_translation_r_trace_norm_trace (y : ℚ) : ℚ :=
  -xi_terminal_zm_translation_r_trace_norm_a3 y

/-- Norm read from the normalized quartic. -/
def xi_terminal_zm_translation_r_trace_norm_norm (y : ℚ) : ℚ :=
  xi_terminal_zm_translation_r_trace_norm_a0 y

/-- Second elementary symmetric coefficient read from the normalized quartic. -/
def xi_terminal_zm_translation_r_trace_norm_e2 (y : ℚ) : ℚ :=
  xi_terminal_zm_translation_r_trace_norm_a2 y

/-- Third elementary symmetric coefficient read from the normalized quartic. -/
def xi_terminal_zm_translation_r_trace_norm_e3 (y : ℚ) : ℚ :=
  -xi_terminal_zm_translation_r_trace_norm_a1 y

/-- The four displayed trace, norm, `e₂`, and `e₃` identities. -/
def xi_terminal_zm_translation_r_trace_norm_statement (y : ℚ) : Prop :=
  xi_terminal_zm_translation_r_trace_norm_trace y =
      (y ^ 3 - 4 * y ^ 2 - 6 * y) / (y + 1) ^ 4 ∧
    xi_terminal_zm_translation_r_trace_norm_norm y =
      (-(y - 1) ^ 3) / (y + 1) ^ 4 ∧
    xi_terminal_zm_translation_r_trace_norm_e2 y =
      (-9 * y ^ 3 + 13 * y ^ 2 - 2 * y - 2) / (y + 1) ^ 4 ∧
    xi_terminal_zm_translation_r_trace_norm_e3 y =
      5 * y * (y - 1) ^ 2 / (y + 1) ^ 4

/-- Paper label: `cor:xi-terminal-zm-translation-r-trace-norm`. -/
theorem paper_xi_terminal_zm_translation_r_trace_norm (y : ℚ) (hy : y + 1 ≠ 0) :
    xi_terminal_zm_translation_r_trace_norm_statement y := by
  unfold xi_terminal_zm_translation_r_trace_norm_statement
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [xi_terminal_zm_translation_r_trace_norm_trace,
      xi_terminal_zm_translation_r_trace_norm_a3]
    field_simp [hy]
    ring
  · rfl
  · rfl
  · simp only [xi_terminal_zm_translation_r_trace_norm_e3,
      xi_terminal_zm_translation_r_trace_norm_a1]
    field_simp [hy]

end Omega.Zeta
