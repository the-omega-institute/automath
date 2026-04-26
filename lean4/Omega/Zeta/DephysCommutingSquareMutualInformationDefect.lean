import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:dephys-commuting-square-mutual-information-defect`. -/
theorem paper_dephys_commuting_square_mutual_information_defect
    (Delta1 Delta2 Delta12 : ℝ) (commutingSquare noExtraLoss : Prop)
    (hNonneg : commutingSquare → 0 ≤ Delta1 + Delta2 - Delta12)
    (hEq : commutingSquare → ((Delta1 + Delta2 - Delta12 = 0) ↔ noExtraLoss))
    (hCS : commutingSquare) :
    0 ≤ Delta1 + Delta2 - Delta12 ∧
      ((Delta1 + Delta2 - Delta12 = 0) ↔ noExtraLoss) := by
  exact ⟨hNonneg hCS, hEq hCS⟩

end Omega.Zeta
