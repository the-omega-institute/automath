import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-fold-uniform-baseline-classical-fdiv-bernoulli-collapse`. -/
theorem paper_xi_fold_uniform_baseline_classical_fdiv_bernoulli_collapse
    (classicalFdivCollapse tvLimit helstromLimit : Prop)
    (hCollapse : classicalFdivCollapse) (hTV : classicalFdivCollapse → tvLimit)
    (hHelstrom : tvLimit → helstromLimit) :
    classicalFdivCollapse ∧ tvLimit ∧ helstromLimit := by
  exact ⟨hCollapse, hTV hCollapse, hHelstrom (hTV hCollapse)⟩

end Omega.Zeta
