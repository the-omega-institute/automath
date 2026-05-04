import Omega.Conclusion.S4HurwitzJacobianFourGeneratorSemiring

namespace Omega.Conclusion

/-- Corollary-level exponent-vector statement for all conjugacy-class quotient Jacobians. -/
def conclusion_s4_hurwitz_jacobian_exponent_vectors_statement (_Q : Polynomial ℚ) : Prop :=
  Omega.Folding.killo_s4_genus49_jacobian_computable_isogeny_factor_dimensions = [5, 4, 3, 9] ∧
    Omega.Folding.killo_s4_genus49_jacobian_computable_isogeny_factor_multiplicities =
      [1, 2, 3, 3] ∧
    ∀ U : conclusion_s4_hurwitz_jacobian_four_generator_semiring_subgroup,
      ∃ a b c d,
        conclusion_s4_hurwitz_jacobian_four_generator_semiring_exponent_vector U =
            (a, b, c, d) ∧
          conclusion_s4_hurwitz_jacobian_four_generator_semiring_quotient_dimension U =
            5 * a + 4 * b + 3 * c + 9 * d

/-- Paper label: `cor:conclusion-s4-hurwitz-jacobian-exponent-vectors`.
The quotient Jacobians in the `S₄` Hurwitz tower have the explicit four-generator exponent
vectors recorded by the finite subgroup table. -/
theorem paper_conclusion_s4_hurwitz_jacobian_exponent_vectors (Q : Polynomial ℚ) :
    conclusion_s4_hurwitz_jacobian_exponent_vectors_statement Q := by
  rcases paper_conclusion_s4_hurwitz_jacobian_four_generator_semiring Q with
    ⟨hdim, hmult, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hall⟩
  refine ⟨hdim, hmult, ?_⟩
  intro U
  rcases hall U with ⟨a, b, c, d, hvec⟩
  refine ⟨a, b, c, d, hvec, ?_⟩
  simp [conclusion_s4_hurwitz_jacobian_four_generator_semiring_quotient_dimension, hvec]

end Omega.Conclusion
