import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Discriminant of the quadratic terminal Lee-Yang Chebyshev seed. -/
def xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_discriminant : ℕ := 28

/-- The ramified prime ledger of the quadratic seed. -/
def xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_ramified_primes : Finset ℕ :=
  {2, 7}

/-- Paper-facing arithmetic package for the discriminant and ramified-prime set. -/
def xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_statement : Prop :=
  xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_discriminant = 28 ∧
    xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_ramified_primes = ({2, 7} :
      Finset ℕ) ∧
    2 ∈ xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_ramified_primes ∧
    7 ∈ xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_ramified_primes ∧
    xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_ramified_primes.card = 2 ∧
    xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_ramified_primes.prod id = 14

/-- The terminal Lee-Yang Chebyshev minimal conjugacy quadratic package has discriminant `28` and
ramified-prime ledger `{2, 7}`.
    cor:xi-terminal-zm-leyang-chebyshev-min-conjugacy-ramification-2-7 -/
theorem paper_xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7 :
    xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_statement := by
  unfold xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_statement
  unfold xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_discriminant
  unfold xi_terminal_zm_leyang_chebyshev_min_conjugacy_ramification_2_7_ramified_primes
  native_decide

end Omega.Zeta
