import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Conclusion.WidomResultantCertificateDegreeBound
import Omega.Zeta.XiLeyangSquareRootCollisionLeadingZerosN2

namespace Omega.Zeta

/-- Paper label: `thm:xi-polynomial-transfer-matrix-branchpoint-discriminant-degree`.
This packages the existing resultant degree estimate with an explicit integer-polynomial witness
for algebraicity of a branchpoint parameter, and reuses the Lee--Yang square-root collision
package once a simple-root and spectral-gap audit has been recorded. -/
theorem paper_xi_polynomial_transfer_matrix_branchpoint_discriminant_degree
    (n m degreeD degreeDerivative resultantDegree : ℕ)
    (resultantValue resultantDerivativeValue u_c : ℤ)
    (polynomialValue derivativeValue : ℤ → ℤ)
    (collision_n : ℚ) (collision_hn : collision_n ≠ 0)
    (collision_u0 collision_amplitude gapSubordinate gapDominant : ℚ)
    (tail sample : ℕ → ℚ)
    (hdegreeD : degreeD = n)
    (hdegreeDerivative : degreeDerivative = n - 1)
    (hresultant_zero_iff :
      resultantValue = 0 ↔ ∃ y : ℤ, polynomialValue y = 0 ∧ derivativeValue y = 0)
    (htextbook : resultantDegree ≤ (degreeD + degreeDerivative) * m)
    (hsample :
      ∀ k : ℕ,
        sample k =
          collision_u0 -
            xiLeyangOddSquareNode k * collision_amplitude / collision_n ^ 2 +
              tail k / collision_n ^ 3) :
    (resultantValue = 0 ↔ ∃ y : ℤ, polynomialValue y = 0 ∧ derivativeValue y = 0) ∧
      resultantDegree ≤ (2 * n - 1) * m ∧
      (resultantValue = 0 →
        ∃ Q : Polynomial ℤ, Q ≠ 0 ∧ Q.eval u_c = 0) ∧
      ((resultantValue = 0 ∧ resultantDerivativeValue ≠ 0) →
        gapSubordinate < gapDominant →
          ∀ k : ℕ,
            sample k =
              (collision_u0 -
                  xiLeyangOddSquareNode k * collision_amplitude / collision_n ^ 2) +
                tail k / collision_n ^ 3) := by
  let paper_xi_polynomial_transfer_matrix_branchpoint_discriminant_degree_certificate :
      Omega.Conclusion.conclusion_widom_resultant_certificate_degree_bound_data :=
    { n := n
      m := m
      degreeD := degreeD
      degreeDerivative := degreeDerivative
      resultantDegree := resultantDegree
      resultantValue := resultantValue
      polynomialValue := polynomialValue
      derivativeValue := derivativeValue
      degreeD_eq := hdegreeD
      degreeDerivative_eq := hdegreeDerivative
      resultant_zero_iff := hresultant_zero_iff
      textbook_resultant_degree_bound := htextbook }
  have hWidom :=
    Omega.Conclusion.paper_conclusion_widom_resultant_certificate_degree_bound
      paper_xi_polynomial_transfer_matrix_branchpoint_discriminant_degree_certificate
  let paper_xi_polynomial_transfer_matrix_branchpoint_discriminant_degree_collision :
      XiLeyangSquareRootCollisionData :=
    { n := collision_n
      hn := collision_hn
      u_c := collision_u0
      amplitude := collision_amplitude
      tail := tail
      sample := sample
      hsample := hsample }
  have hCollision :
      (paper_xi_polynomial_transfer_matrix_branchpoint_discriminant_degree_collision
        ).hasQuantizedLeadingZerosN2 :=
    paper_xi_leyang_square_root_collision_leading_zeros_n2
      paper_xi_polynomial_transfer_matrix_branchpoint_discriminant_degree_collision
  refine ⟨hWidom.1, hWidom.2, ?_, ?_⟩
  · intro _hzero
    refine ⟨Polynomial.X - Polynomial.C u_c, Polynomial.X_sub_C_ne_zero u_c, by simp⟩
  · intro _hsimple _hgap k
    simpa
      [XiLeyangSquareRootCollisionData.hasQuantizedLeadingZerosN2,
        XiLeyangSquareRootCollisionData.quantizedLeadingZero,
        XiLeyangSquareRootCollisionData.leadingZeroTail,
        paper_xi_polynomial_transfer_matrix_branchpoint_discriminant_degree_collision]
      using hCollision k

end Omega.Zeta
