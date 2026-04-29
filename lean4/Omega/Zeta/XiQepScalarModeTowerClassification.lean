import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete coefficients for the normalized scalar quadratic mode
`z ^ 2 + damping * z + stiffness`. -/
structure xi_qep_scalar_mode_tower_classification_data where
  damping : ℝ
  stiffness : ℝ

/-- The discriminant of the scalar quadratic mode. -/
def xi_qep_scalar_mode_tower_classification_discriminant
    (D : xi_qep_scalar_mode_tower_classification_data) : ℝ :=
  D.damping ^ 2 - 4 * D.stiffness

/-- The scalar quadratic mode, viewed over `ℂ`. -/
def xi_qep_scalar_mode_tower_classification_polynomial
    (D : xi_qep_scalar_mode_tower_classification_data) (z : ℂ) : ℂ :=
  z ^ 2 + (D.damping : ℂ) * z + (D.stiffness : ℂ)

/-- The scalar quadratic mode over `ℝ`. -/
def xi_qep_scalar_mode_tower_classification_real_polynomial
    (D : xi_qep_scalar_mode_tower_classification_data) (x : ℝ) : ℝ :=
  x ^ 2 + D.damping * x + D.stiffness

/-- The upper real root in the nonnegative-discriminant case. -/
def xi_qep_scalar_mode_tower_classification_real_root_plus
    (D : xi_qep_scalar_mode_tower_classification_data) : ℝ :=
  (-D.damping + Real.sqrt (xi_qep_scalar_mode_tower_classification_discriminant D)) / 2

/-- The lower real root in the nonnegative-discriminant case. -/
def xi_qep_scalar_mode_tower_classification_real_root_minus
    (D : xi_qep_scalar_mode_tower_classification_data) : ℝ :=
  (-D.damping - Real.sqrt (xi_qep_scalar_mode_tower_classification_discriminant D)) / 2

/-- The upper complex-conjugate root in the negative-discriminant case. -/
def xi_qep_scalar_mode_tower_classification_complex_root_plus
    (D : xi_qep_scalar_mode_tower_classification_data) : ℂ :=
  (-(D.damping / 2) : ℂ) +
    ((Real.sqrt (-(xi_qep_scalar_mode_tower_classification_discriminant D)) / 2 : ℝ) : ℂ) *
      Complex.I

/-- The lower complex-conjugate root in the negative-discriminant case. -/
def xi_qep_scalar_mode_tower_classification_complex_root_minus
    (D : xi_qep_scalar_mode_tower_classification_data) : ℂ :=
  (-(D.damping / 2) : ℂ) -
    ((Real.sqrt (-(xi_qep_scalar_mode_tower_classification_discriminant D)) / 2 : ℝ) : ℂ) *
      Complex.I

/-- Scalar-mode classification by discriminant sign, including the tower step in the
complex-conjugate case as the imaginary separation. -/
def xi_qep_scalar_mode_tower_classification_statement
    (D : xi_qep_scalar_mode_tower_classification_data) : Prop :=
  (0 ≤ xi_qep_scalar_mode_tower_classification_discriminant D →
      xi_qep_scalar_mode_tower_classification_real_polynomial D
          (xi_qep_scalar_mode_tower_classification_real_root_plus D) = 0 ∧
        xi_qep_scalar_mode_tower_classification_real_polynomial D
          (xi_qep_scalar_mode_tower_classification_real_root_minus D) = 0 ∧
        xi_qep_scalar_mode_tower_classification_real_root_plus D +
            xi_qep_scalar_mode_tower_classification_real_root_minus D =
          -D.damping ∧
        xi_qep_scalar_mode_tower_classification_real_root_plus D *
            xi_qep_scalar_mode_tower_classification_real_root_minus D =
          D.stiffness) ∧
    (xi_qep_scalar_mode_tower_classification_discriminant D < 0 →
      (xi_qep_scalar_mode_tower_classification_complex_root_plus D).re = -D.damping / 2 ∧
        (xi_qep_scalar_mode_tower_classification_complex_root_minus D).re = -D.damping / 2 ∧
        (xi_qep_scalar_mode_tower_classification_complex_root_plus D).im =
          Real.sqrt (-(xi_qep_scalar_mode_tower_classification_discriminant D)) / 2 ∧
        (xi_qep_scalar_mode_tower_classification_complex_root_minus D).im =
          -Real.sqrt (-(xi_qep_scalar_mode_tower_classification_discriminant D)) / 2 ∧
        (xi_qep_scalar_mode_tower_classification_complex_root_plus D).im -
            (xi_qep_scalar_mode_tower_classification_complex_root_minus D).im =
          Real.sqrt (-(xi_qep_scalar_mode_tower_classification_discriminant D))) ∧
    (xi_qep_scalar_mode_tower_classification_discriminant D = 0 →
      xi_qep_scalar_mode_tower_classification_real_root_plus D =
          xi_qep_scalar_mode_tower_classification_real_root_minus D ∧
        xi_qep_scalar_mode_tower_classification_real_root_plus D = -D.damping / 2)

/-- Paper label: `thm:xi-qep-scalar-mode-tower-classification`. -/
theorem paper_xi_qep_scalar_mode_tower_classification
    (D : xi_qep_scalar_mode_tower_classification_data) :
    xi_qep_scalar_mode_tower_classification_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdisc
    have hsqrt :
        Real.sqrt (xi_qep_scalar_mode_tower_classification_discriminant D) ^ 2 =
          xi_qep_scalar_mode_tower_classification_discriminant D := by
      exact Real.sq_sqrt hdisc
    have hsqrt' : Real.sqrt (D.damping ^ 2 - 4 * D.stiffness) ^ 2 =
        D.damping ^ 2 - 4 * D.stiffness := by
      simpa [xi_qep_scalar_mode_tower_classification_discriminant] using hsqrt
    have hsqrt'' : Real.sqrt (D.damping ^ 2 - D.stiffness * 4) ^ 2 =
        D.damping ^ 2 - D.stiffness * 4 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsqrt'
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_real_polynomial
        xi_qep_scalar_mode_tower_classification_real_root_plus
        xi_qep_scalar_mode_tower_classification_discriminant
      ring_nf
      rw [hsqrt'']
      ring
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_real_polynomial
        xi_qep_scalar_mode_tower_classification_real_root_minus
        xi_qep_scalar_mode_tower_classification_discriminant
      ring_nf
      rw [hsqrt'']
      ring
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_real_root_plus
        xi_qep_scalar_mode_tower_classification_real_root_minus
      ring
    · unfold xi_qep_scalar_mode_tower_classification_real_root_plus
        xi_qep_scalar_mode_tower_classification_real_root_minus
        xi_qep_scalar_mode_tower_classification_discriminant
      ring_nf
      rw [hsqrt'']
      ring
  · intro hdisc
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_complex_root_plus
      simp
      ring
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_complex_root_minus
      simp
      ring
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_complex_root_plus
      simp
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_complex_root_minus
      simp
      ring
    · unfold xi_qep_scalar_mode_tower_classification_complex_root_plus
        xi_qep_scalar_mode_tower_classification_complex_root_minus
      simp
  · intro hdisc
    constructor
    · unfold xi_qep_scalar_mode_tower_classification_real_root_plus
        xi_qep_scalar_mode_tower_classification_real_root_minus
      rw [hdisc]
      norm_num
    · unfold xi_qep_scalar_mode_tower_classification_real_root_plus
      rw [hdisc]
      norm_num

end

end Omega.Zeta
