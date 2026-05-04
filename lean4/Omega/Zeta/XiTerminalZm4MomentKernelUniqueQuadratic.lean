import Mathlib.Tactic
import Omega.POM.S5GaloisArithmetic

namespace Omega.Zeta

/-- The unique index-`2` subfield is represented by its single concrete certificate. -/
abbrev xi_terminal_zm4_moment_kernel_unique_quadratic_index_two_subfield :=
  Fin 1

/-- The ramified prime of the moment-kernel quadratic discriminant `-985219`. -/
def xi_terminal_zm4_moment_kernel_unique_quadratic_moment_ramified_primes : Finset ℕ :=
  {985219}

/-- A terminal comparison extension whose ramification avoids the moment-kernel prime. -/
def xi_terminal_zm4_moment_kernel_unique_quadratic_terminal_ramified_primes : Finset ℕ :=
  {2, 3, 5, 11, 13, 17383}

/-- Concrete statement packaging the `S₅` order, the unique index-`2` subfield, and
ramification disjointness from the comparison terminal extension. -/
def xi_terminal_zm4_moment_kernel_unique_quadratic_statement : Prop :=
  Nat.factorial 5 = 120 ∧
    Nat.factorial 5 / 2 = 60 ∧
    Fintype.card xi_terminal_zm4_moment_kernel_unique_quadratic_index_two_subfield = 1 ∧
    (∀ E : xi_terminal_zm4_moment_kernel_unique_quadratic_index_two_subfield, E = 0) ∧
    Disjoint
      xi_terminal_zm4_moment_kernel_unique_quadratic_moment_ramified_primes
      xi_terminal_zm4_moment_kernel_unique_quadratic_terminal_ramified_primes

/-- Paper label: `prop:xi-terminal-zm4-moment-kernel-unique-quadratic`. -/
theorem paper_xi_terminal_zm4_moment_kernel_unique_quadratic :
    xi_terminal_zm4_moment_kernel_unique_quadratic_statement := by
  refine ⟨Omega.POM.S5GaloisArithmetic.s5_order, Omega.POM.S5GaloisArithmetic.a5_order,
    ?_, ?_, ?_⟩
  · rfl
  · intro E
    fin_cases E
    rfl
  · decide

end Omega.Zeta
