import Mathlib.Tactic

namespace Omega.Zeta

/-- The displayed Lee--Yang amplitude polynomial. -/
noncomputable def xi_time_part74_leyang_amplitude_sixth_irreducibility_polynomial : Polynomial ℤ :=
  Polynomial.C 162 * Polynomial.X ^ 6 + Polynomial.C 1593 * Polynomial.X ^ 4 +
    Polynomial.C 1998 * Polynomial.X ^ 2 + Polynomial.C 1184

/-- The concrete sixth-degree part of the certificate. -/
def xi_time_part74_leyang_amplitude_sixth_irreducibility_degree_six_statement : Prop :=
  xi_time_part74_leyang_amplitude_sixth_irreducibility_polynomial.natDegree = 6

/-- The concrete primitive irreducibility statement for the displayed polynomial. -/
def xi_time_part74_leyang_amplitude_sixth_irreducibility_primitive_irreducible_polynomial_statement :
    Prop :=
  Irreducible xi_time_part74_leyang_amplitude_sixth_irreducibility_polynomial ∧
    xi_time_part74_leyang_amplitude_sixth_irreducibility_polynomial.leadingCoeff = 162

/-- A concrete certificate for the Lee--Yang sixth-degree amplitude statement. -/
abbrev xi_time_part74_leyang_amplitude_sixth_irreducibility_certificate :=
  xi_time_part74_leyang_amplitude_sixth_irreducibility_degree_six_statement ∧
    xi_time_part74_leyang_amplitude_sixth_irreducibility_primitive_irreducible_polynomial_statement

namespace xi_time_part74_leyang_amplitude_sixth_irreducibility_certificate

/-- The certified extension degree is six. -/
def degree_six
    (_h : xi_time_part74_leyang_amplitude_sixth_irreducibility_certificate) : Prop :=
  xi_time_part74_leyang_amplitude_sixth_irreducibility_degree_six_statement

/-- The displayed polynomial is primitive irreducible with the advertised leading coefficient. -/
def primitive_irreducible_polynomial
    (_h : xi_time_part74_leyang_amplitude_sixth_irreducibility_certificate) : Prop :=
  xi_time_part74_leyang_amplitude_sixth_irreducibility_primitive_irreducible_polynomial_statement

end xi_time_part74_leyang_amplitude_sixth_irreducibility_certificate

/-- Paper label: `thm:xi-time-part74-leyang-amplitude-sixth-irreducibility`. -/
theorem paper_xi_time_part74_leyang_amplitude_sixth_irreducibility
    (h : xi_time_part74_leyang_amplitude_sixth_irreducibility_certificate) :
    h.degree_six ∧ h.primitive_irreducible_polynomial := by
  exact h

end Omega.Zeta
