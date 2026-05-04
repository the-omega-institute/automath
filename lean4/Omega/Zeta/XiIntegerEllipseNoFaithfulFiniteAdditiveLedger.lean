import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-integer-ellipse-no-faithful-finite-additive-ledger`. -/
theorem paper_xi_integer_ellipse_no_faithful_finite_additive_ledger
    {M N : Type*} [Infinite M] [Fintype N] (ledger : M → N) :
    ¬ Function.Injective ledger := by
  exact not_injective_infinite_finite ledger

end Omega.Zeta
