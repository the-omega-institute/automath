import Mathlib.Data.Finsupp.Basic
import Omega.Folding.KilloEllipseDiagonalPrimeRegisterEquivalence
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Zeta

/-- Grothendieck completion of one countable prime-register component. -/
abbrev xi_integer_ellipse_grothendieck_double_countable_rank_component := ℕ →₀ ℤ

/-- The integer ellipse has two independent countable prime-register components. -/
abbrev xi_integer_ellipse_grothendieck_double_countable_rank_completion :=
  xi_integer_ellipse_grothendieck_double_countable_rank_component ×
    xi_integer_ellipse_grothendieck_double_countable_rank_component

/-- Finite rational-coordinate host of rank `k`. -/
abbrev xi_integer_ellipse_grothendieck_double_countable_rank_finite_host (k : ℕ) :=
  Omega.Folding.KilloFiniteRegister k

/-- A finite generated cancellative linearization would inject the first `k + 1` prime axes into
a rank-`k` rational host. -/
def xi_integer_ellipse_grothendieck_double_countable_rank_finite_generated_obstructed
    (k : ℕ) : Prop :=
  ¬ ∃ Φ : Omega.Folding.KilloPrimeWindow k →ₗ[ℚ]
      xi_integer_ellipse_grothendieck_double_countable_rank_finite_host k,
    Function.Injective Φ

/-- The same obstruction stated for faithful `Nat^k`-coordinate prime-register embeddings after
Grothendieck completion. -/
def xi_integer_ellipse_grothendieck_double_countable_rank_nat_power_obstructed
    (k : ℕ) : Prop :=
  ¬ ∃ Φ : Omega.Folding.KilloPrimeWindow k →ₗ[ℚ] Omega.Folding.KilloFiniteRegister k,
    Function.Injective Φ

/-- Concrete statement for
`thm:xi-integer-ellipse-grothendieck-double-countable-rank`. -/
def xi_integer_ellipse_grothendieck_double_countable_rank_statement : Prop :=
  Nonempty xi_integer_ellipse_grothendieck_double_countable_rank_completion ∧
    Omega.Folding.killoEllipseDiagonalPrimeRegisterEquivalence ∧
    Omega.Folding.killoPrimeExponentEmbeddingFaithful ∧
    ∀ k : ℕ,
      xi_integer_ellipse_grothendieck_double_countable_rank_finite_generated_obstructed k ∧
        xi_integer_ellipse_grothendieck_double_countable_rank_nat_power_obstructed k

/-- Paper label: `thm:xi-integer-ellipse-grothendieck-double-countable-rank`. -/
theorem paper_xi_integer_ellipse_grothendieck_double_countable_rank :
    xi_integer_ellipse_grothendieck_double_countable_rank_statement := by
  rcases Omega.Folding.paper_killo_prime_freedom_non_finitizability with ⟨hfaithful, hobstruct⟩
  refine ⟨⟨0, 0⟩, Omega.Folding.paper_killo_ellipse_diagonal_prime_register_equivalence,
    hfaithful, ?_⟩
  intro k
  exact ⟨hobstruct k, hobstruct k⟩

end Omega.Zeta
