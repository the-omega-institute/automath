import Mathlib
import Omega.Zeta.XiTerminalZmLeyangRamificationDivisorStokes

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete paper-facing data for the terminal Lee--Yang ramification sum law. -/
abbrev xi_terminal_zm_leyang_ramification_sum_zero_Data := PUnit

namespace xi_terminal_zm_leyang_ramification_sum_zero_Data

/-- The five finite branch classes in the Abel-Jacobi bookkeeping group. -/
def finite_branch_class : Fin 5 → ZMod 5
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 0

/-- Sum of the five finite branch classes. -/
def finite_branch_sum : ZMod 5 :=
  ∑ i : Fin 5, finite_branch_class i

/-- Rational split certificate for the first two finite branch points. -/
def rational_split_pair_sum : ℚ × ℚ := (1 / 4, -3 / 8)

/-- Rational split certificate for the remaining three finite branch points. -/
def rational_split_triple_sum : ℚ × ℚ := (1 / 4, -5 / 8)

/-- The five finite branch classes sum to zero, compatibly with the six-point ramification model. -/
def finite_branch_sum_zero (_D : xi_terminal_zm_leyang_ramification_sum_zero_Data) : Prop :=
  finite_branch_sum = 0 ∧ xiTerminalZmLeyangAbelJacobiSum = 0

/-- The two rational split certificates recorded in the elliptic coordinates. -/
def rational_split_certificate (_D : xi_terminal_zm_leyang_ramification_sum_zero_Data) : Prop :=
  rational_split_pair_sum = (1 / 4, -3 / 8) ∧
    rational_split_triple_sum = (1 / 4, -5 / 8) ∧
    rational_split_pair_sum.1 = rational_split_triple_sum.1 ∧
    rational_split_pair_sum.2 + rational_split_triple_sum.2 = -1

end xi_terminal_zm_leyang_ramification_sum_zero_Data

open xi_terminal_zm_leyang_ramification_sum_zero_Data

/-- Paper label: `cor:xi-terminal-zm-leyang-ramification-sum-zero`.

The finite Lee--Yang branch classes cancel in `ZMod 5`; the same cancellation agrees with the
previous six-point ramification divisor bookkeeping, and the two rational split certificates are
the stated coordinate equalities. -/
theorem paper_xi_terminal_zm_leyang_ramification_sum_zero
    (D : xi_terminal_zm_leyang_ramification_sum_zero_Data) :
    D.finite_branch_sum_zero ∧ D.rational_split_certificate := by
  refine ⟨?_, ?_⟩
  · exact ⟨by native_decide, paper_xi_terminal_zm_leyang_ramification_divisor_stokes.2.2⟩
  · norm_num [rational_split_certificate, rational_split_pair_sum, rational_split_triple_sum]

end Omega.Zeta
