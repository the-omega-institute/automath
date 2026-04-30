import Mathlib.Tactic

namespace Omega.Zeta

/-- The displayed Lee--Yang amplitude sextic has degree six in the seed package. -/
def xi_time_part74_leyang_amplitude_field_signature_sextic_degree : ℕ := 6

/-- The displayed Lee--Yang amplitude sextic has leading coefficient `162`. -/
def xi_time_part74_leyang_amplitude_field_signature_sextic_leading_coeff : ℤ := 162

/-- The recorded degree of the quadratic amplitude extension `L/K`. -/
def xi_time_part74_leyang_amplitude_field_signature_extension_degree : ℕ := 2

/-- The recorded degree of the cubic subfield `K = ℚ(B^2)`. -/
def xi_time_part74_leyang_amplitude_field_signature_cubic_degree : ℕ := 3

/-- The recorded degree of the full amplitude field `L = ℚ(B)`. -/
def xi_time_part74_leyang_amplitude_field_signature_full_degree : ℕ := 6

/-- The signature of the cubic subfield `K`. -/
def xi_time_part74_leyang_amplitude_field_signature_cubic_signature : ℕ × ℕ :=
  (1, 1)

/-- The signature of the full amplitude field `L`. -/
def xi_time_part74_leyang_amplitude_field_signature_full_signature : ℕ × ℕ :=
  (0, 3)

/-- The cubic discriminant formula specialized to integer coefficients. -/
def xi_time_part74_leyang_amplitude_field_signature_cubic_discriminant
    (a b c d : ℤ) : ℤ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
    18 * a * b * c * d

/-- The discriminant of `162 t^3 + 1593 t^2 + 1998 t + 1184`. -/
def xi_time_part74_leyang_amplitude_field_signature_amplitude_square_discriminant : ℤ :=
  xi_time_part74_leyang_amplitude_field_signature_cubic_discriminant 162 1593 1998 1184

/-- The shared quadratic resolvent discriminant recorded by the amplitude-square cubic. -/
def xi_time_part74_leyang_amplitude_field_signature_quadratic_resolvent_discriminant :
    ℤ :=
  -111

/-- Concrete real-place obstruction: the selected negative real image has no real square root. -/
def xi_time_part74_leyang_amplitude_field_signature_real_square_obstruction : Prop :=
  ∀ x : ℝ, x ^ 2 ≠ -1

/-- Concrete statement package for the Lee--Yang amplitude field signature. -/
def xi_time_part74_leyang_amplitude_field_signature_statement : Prop :=
  xi_time_part74_leyang_amplitude_field_signature_sextic_degree = 6 ∧
    xi_time_part74_leyang_amplitude_field_signature_sextic_leading_coeff = 162 ∧
    (1593 ^ 2 * 1998 ^ 2 - 4 * 162 * 1998 ^ 3 - 4 * 1593 ^ 3 * 1184 -
          27 * 162 ^ 2 * 1184 ^ 2 + 18 * 162 * 1593 * 1998 * 1184 =
        - (2 ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2 : ℤ)) ∧
    xi_time_part74_leyang_amplitude_field_signature_amplitude_square_discriminant =
      - (2 ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2 : ℤ) ∧
    xi_time_part74_leyang_amplitude_field_signature_amplitude_square_discriminant < 0 ∧
    xi_time_part74_leyang_amplitude_field_signature_quadratic_resolvent_discriminant =
      -111 ∧
    xi_time_part74_leyang_amplitude_field_signature_extension_degree = 2 ∧
    xi_time_part74_leyang_amplitude_field_signature_cubic_degree = 3 ∧
    xi_time_part74_leyang_amplitude_field_signature_full_degree = 6 ∧
    xi_time_part74_leyang_amplitude_field_signature_cubic_signature = (1, 1) ∧
    xi_time_part74_leyang_amplitude_field_signature_full_signature = (0, 3) ∧
    xi_time_part74_leyang_amplitude_field_signature_real_square_obstruction

/-- Paper label: `cor:xi-time-part74-leyang-amplitude-field-signature`. -/
theorem paper_xi_time_part74_leyang_amplitude_field_signature :
    xi_time_part74_leyang_amplitude_field_signature_statement := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · norm_num
  · norm_num [xi_time_part74_leyang_amplitude_field_signature_amplitude_square_discriminant,
      xi_time_part74_leyang_amplitude_field_signature_cubic_discriminant]
  · norm_num [xi_time_part74_leyang_amplitude_field_signature_amplitude_square_discriminant,
      xi_time_part74_leyang_amplitude_field_signature_cubic_discriminant]
  · intro x hx
    have hnonneg : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith

end Omega.Zeta
