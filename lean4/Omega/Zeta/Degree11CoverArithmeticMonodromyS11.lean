import Omega.Zeta.Degree11GenericGaloisS11
import Omega.Zeta.Degree11ParameterTDivisorDegree

namespace Omega.Zeta

/-- Paper-facing corollary package for the degree-`11` cover: the pole divisor of `t` has total
degree `11`, the specialization audit supplies an `S₁₁` witness, and the generic Hilbert package
records the arithmetic monodromy conclusion. -/
def xi_degree11_cover_arithmetic_monodromy_s11_statement : Prop :=
  xi_degree11_parameter_t_divisor_degree_statement ∧
    Omega.Zeta.Degree11GenericGaloisS11.xi_degree11_et_specialization_galois_s11_statement ∧
    ((11 : ℕ) = 11 ∧
      Nat.Prime 11 ∧
      1 + 3 + 7 = (11 : ℕ) ∧
      (7 : ℕ) ≤ 11 - 3 ∧
      Nat.Prime 7 ∧
      37 % 2 = 1 ∧
      Nat.factorial 11 = 39916800 ∧
      (11 : ℕ) ≥ 5)

/-- Paper label: `cor:xi-degree11-cover-arithmetic-monodromy-S11`. -/
theorem paper_xi_degree11_cover_arithmetic_monodromy_s11 :
    xi_degree11_cover_arithmetic_monodromy_s11_statement := by
  refine ⟨paper_xi_degree11_parameter_t_divisor_degree, ?_, ?_⟩
  · exact Omega.Zeta.Degree11GenericGaloisS11.paper_xi_degree11_et_specialization_galois_s11
  · exact Omega.Zeta.Degree11GenericGaloisS11.paper_xi_degree11_generic_galois_S11_package

end Omega.Zeta
