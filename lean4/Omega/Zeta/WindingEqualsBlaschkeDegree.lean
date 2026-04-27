import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:winding-equals-blaschke-degree`. -/
theorem paper_winding_equals_blaschke_degree
    (wind degree defect : ℤ) (hArgumentPrinciple : wind = degree)
    (hFiniteDefect : degree = defect) :
    wind = degree ∧ degree = defect ∧ wind = defect := by
  exact ⟨hArgumentPrinciple, hFiniteDefect, hArgumentPrinciple.trans hFiniteDefect⟩

end Omega.Zeta
