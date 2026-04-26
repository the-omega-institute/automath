import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper label: `thm:cdim-phase-residual-budget-lower-bound`. This is the paper-facing wrapper
for the finite-cardinality phase/residual budget inequality already used elsewhere in the chapter.
-/
theorem paper_cdim_phase_residual_budget_lower_bound (b r k t R : ℕ)
    (hinj : ∃ f : Fin ((2 ^ (b * r)) * t) → Fin ((2 ^ (b * k)) * R), Function.Injective f) :
    (2 ^ (b * r)) * t ≤ (2 ^ (b * k)) * R := by
  simpa using phaseResidualBudget_lower_bound_finite b r k t R hinj

end Omega.CircleDimension
