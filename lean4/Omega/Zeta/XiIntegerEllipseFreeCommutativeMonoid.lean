import Mathlib.Data.Fintype.Perm
import Omega.Folding.KilloEllipseDiagonalPrimeRegisterEquivalence
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Zeta

/-- The two prime axes used by the integer-axis ellipse monoid. -/
abbrev xi_integer_ellipse_free_commutative_monoid_atom_axis :=
  Omega.Conclusion.PrimeRegisterVector × Bool

/-- The concrete free-register model for the two independent ellipse axes. -/
abbrev xi_integer_ellipse_free_commutative_monoid_register_model :=
  Omega.Folding.KilloPrimeRegisterPair

/-- The concrete integer-axis ellipse model. -/
abbrev xi_integer_ellipse_free_commutative_monoid_ellipse_model :=
  Omega.Folding.KilloDiagonalEllipse

/-- The registered prime-factorization equivalence supplies the free coordinate chart. -/
noncomputable def xi_integer_ellipse_free_commutative_monoid_register_equiv :
    xi_integer_ellipse_free_commutative_monoid_register_model ≃
      xi_integer_ellipse_free_commutative_monoid_ellipse_model :=
  Equiv.ofBijective Omega.Folding.killoPrimeRegisterToEllipse
    Omega.Folding.paper_killo_ellipse_diagonal_prime_register_equivalence.1

/-- Concrete free-commutative-monoid package for integer-axis ellipses. -/
def xi_integer_ellipse_free_commutative_monoid_statement : Prop :=
  Nonempty
      (xi_integer_ellipse_free_commutative_monoid_register_model ≃
        xi_integer_ellipse_free_commutative_monoid_ellipse_model) ∧
    Omega.Folding.killoEllipseDiagonalPrimeRegisterEquivalence ∧
    Omega.Folding.killoPrimeExponentEmbeddingFaithful ∧
    Omega.Conclusion.primeRegisterMonoidHomLaw ∧
    Nonempty (Equiv.Perm xi_integer_ellipse_free_commutative_monoid_atom_axis)

/-- Paper label: `thm:xi-integer-ellipse-free-commutative-monoid`. -/
theorem paper_xi_integer_ellipse_free_commutative_monoid :
    xi_integer_ellipse_free_commutative_monoid_statement := by
  rcases Omega.Folding.paper_killo_prime_freedom_non_finitizability with ⟨hfaithful, _⟩
  refine ⟨⟨xi_integer_ellipse_free_commutative_monoid_register_equiv⟩,
    Omega.Folding.paper_killo_ellipse_diagonal_prime_register_equivalence,
    hfaithful, ?_, ⟨Equiv.refl _⟩⟩
  exact Omega.Conclusion.paper_conclusion_prime_register_ellipse_complete_equivalence.1

end Omega.Zeta
