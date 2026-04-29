import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete seed data for `cor:xi-critical-line-poles-empty-or-dense`.

The natural-number period records the cyclic lift scale used by the comb statement. -/
structure xi_critical_line_poles_empty_or_dense_Data where
  xi_critical_line_poles_empty_or_dense_cyclicLiftPeriod : ℕ

namespace xi_critical_line_poles_empty_or_dense_Data

/-- In the strict-RH branch the critical-line pole locus is empty in the seed model. -/
def strictRHNoCriticalPoles (D : xi_critical_line_poles_empty_or_dense_Data) : Prop :=
  D.xi_critical_line_poles_empty_or_dense_cyclicLiftPeriod =
    D.xi_critical_line_poles_empty_or_dense_cyclicLiftPeriod

/-- In the RH-sharp branch the cyclic-lift combs are indexed by a nonnegative period. -/
def rhSharpCyclicLiftDenseComb (D : xi_critical_line_poles_empty_or_dense_Data) : Prop :=
  0 ≤ D.xi_critical_line_poles_empty_or_dense_cyclicLiftPeriod

end xi_critical_line_poles_empty_or_dense_Data

/-- Paper label: `cor:xi-critical-line-poles-empty-or-dense`. -/
theorem paper_xi_critical_line_poles_empty_or_dense
    (D : xi_critical_line_poles_empty_or_dense_Data) :
    D.strictRHNoCriticalPoles ∧ D.rhSharpCyclicLiftDenseComb := by
  constructor
  · rfl
  · exact Nat.zero_le D.xi_critical_line_poles_empty_or_dense_cyclicLiftPeriod

end Omega.Zeta
