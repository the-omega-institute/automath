import Mathlib.Tactic
import Omega.GU.Window6FamilyProjectionWequivariantUniqueness

namespace Omega.GU

/-- The window-6 family projection is a `16`-sheet fibration over the three boundary labels, so
the carrier has cardinality `48 = 16 * 3`.
    prop:window6-family-fibration-15plus1 -/
theorem paper_window6_family_fibration_15plus1 :
    (∀ i : Fin 3, Fintype.card (window6FamilyFiber i) = 16) ∧
    Fintype.card Window6FamilyCarrier = 48 := by
  refine ⟨?_, ?_⟩
  · intro i
    simpa using (Fintype.card_congr (window6FamilyFiberEquiv i)).symm
  · simp [Window6FamilyCarrier]

end Omega.GU
