import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local data for the lower bound on a finite-state realization dimension coming from the
minimal polynomial degree. The fields package an abstract finite-dimensional realization, the
recurrence order supplied by Cayley-Hamilton, and the minimality comparison showing that every
such recurrence order dominates the minimal polynomial degree. -/
structure ObservableMinpolyFiniteStateData where
  minpolyDegree : Nat
  stateDim : Nat
  cayleyHamiltonRecurrenceOrder : Nat
  finiteDimensionalRealization : Prop
  cayleyHamiltonRecurrence : Prop
  hasFiniteDimensionalRealization : finiteDimensionalRealization
  hasCayleyHamiltonRecurrence : cayleyHamiltonRecurrence
  minpolyDegree_le_cayleyHamiltonOrder :
    cayleyHamiltonRecurrence → minpolyDegree ≤ cayleyHamiltonRecurrenceOrder
  cayleyHamiltonOrder_le_stateDim :
    finiteDimensionalRealization → cayleyHamiltonRecurrenceOrder ≤ stateDim

/-- Paper-facing wrapper for the fact that the minimal polynomial degree is bounded above by the
dimension of any finite-state realization.
    cor:pom-finite-state-dimension-lower-bound-from-minpoly -/
theorem paper_pom_finite_state_dimension_lower_bound_from_minpoly
    (D : ObservableMinpolyFiniteStateData) : D.minpolyDegree ≤ D.stateDim := by
  have hMinpoly :
      D.minpolyDegree ≤ D.cayleyHamiltonRecurrenceOrder :=
    D.minpolyDegree_le_cayleyHamiltonOrder D.hasCayleyHamiltonRecurrence
  have hState :
      D.cayleyHamiltonRecurrenceOrder ≤ D.stateDim :=
    D.cayleyHamiltonOrder_le_stateDim D.hasFiniteDimensionalRealization
  exact le_trans hMinpoly hState

end Omega.POM
