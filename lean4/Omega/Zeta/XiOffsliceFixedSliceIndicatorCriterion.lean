import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-offslice-fixed-slice-indicator-criterion`. -/
theorem xi_offslice_fixed_slice_indicator_criterion_scalar_equivalence_chain
    {α : Type _} [DecidableEq α]
    (Zplus : Finset α) (Ind : Nat) (W B0 : ℝ) (hInd : (Zplus = ∅ ↔ Ind = 0))
    (hW : (Zplus = ∅ ↔ W = 0)) (hB : (W = 0 ↔ B0 = 1)) :
    (Zplus = ∅ ↔ Ind = 0) ∧ (Ind = 0 ↔ W = 0) ∧ (W = 0 ↔ B0 = 1) := by
  refine ⟨hInd, ?_, hB⟩
  constructor
  · intro hIndZero
    exact hW.mp (hInd.mpr hIndZero)
  · intro hWZero
    exact hInd.mp (hW.mpr hWZero)

end Omega.Zeta
