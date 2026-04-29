import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangCoverPrimitive

namespace Omega.Conclusion

/-- Concrete Lee--Yang quartic-cover package, carrying the existing monodromy certificate from the
Zeta chapter. -/
structure conclusion_leyang_no_global_quadratic_quadratic_factorization_data where
  conclusion_leyang_no_global_quadratic_quadratic_factorization_primitiveCertificate :
    Omega.Zeta.xi_terminal_zm_leyang_cover_primitive_data := {}

namespace conclusion_leyang_no_global_quadratic_quadratic_factorization_data

/-- A global quadratic--quadratic factorization is a `2+2` intermediate block system on the four
sheets of the Lee--Yang quartic cover. -/
def conclusion_leyang_no_global_quadratic_quadratic_factorization_hasFactorization
    (D : conclusion_leyang_no_global_quadratic_quadratic_factorization_data) : Prop :=
  Omega.Zeta.xi_terminal_zm_leyang_cover_primitive_data.has_degree_two_factorization
    D.conclusion_leyang_no_global_quadratic_quadratic_factorization_primitiveCertificate

/-- The primitive-cover certificate says that no such `2+2` block system exists. -/
def conclusion_leyang_no_global_quadratic_quadratic_factorization_isPrimitive
    (D : conclusion_leyang_no_global_quadratic_quadratic_factorization_data) : Prop :=
  ¬ D.conclusion_leyang_no_global_quadratic_quadratic_factorization_hasFactorization

/-- Paper-facing statement: the primitive quartic Lee--Yang cover admits no global
quadratic--quadratic intermediate factorization. -/
def conclusion_leyang_no_global_quadratic_quadratic_factorization_statement
    (D : conclusion_leyang_no_global_quadratic_quadratic_factorization_data) : Prop :=
  D.conclusion_leyang_no_global_quadratic_quadratic_factorization_isPrimitive ∧
    ¬ D.conclusion_leyang_no_global_quadratic_quadratic_factorization_hasFactorization

end conclusion_leyang_no_global_quadratic_quadratic_factorization_data

open conclusion_leyang_no_global_quadratic_quadratic_factorization_data

lemma conclusion_leyang_no_global_quadratic_quadratic_factorization_primitive_obstruction
    (D : conclusion_leyang_no_global_quadratic_quadratic_factorization_data) :
    ¬ D.conclusion_leyang_no_global_quadratic_quadratic_factorization_hasFactorization := by
  simpa
    [conclusion_leyang_no_global_quadratic_quadratic_factorization_hasFactorization] using
      Omega.Zeta.paper_xi_terminal_zm_leyang_cover_primitive
        D.conclusion_leyang_no_global_quadratic_quadratic_factorization_primitiveCertificate

/-- Paper label:
`prop:conclusion-leyang-no-global-quadratic-quadratic-factorization`. -/
theorem paper_conclusion_leyang_no_global_quadratic_quadratic_factorization
    (D : conclusion_leyang_no_global_quadratic_quadratic_factorization_data) :
    conclusion_leyang_no_global_quadratic_quadratic_factorization_statement D := by
  have h :=
    conclusion_leyang_no_global_quadratic_quadratic_factorization_primitive_obstruction D
  exact ⟨h, h⟩

end Omega.Conclusion
