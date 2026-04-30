import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-resonance-pencil-reconstruction`. -/
theorem paper_xi_resonance_pencil_reconstruction
    (finiteWindowConsistent hasKappaPoles pencilReadsPoles : Prop)
    (hFiniteWindow : finiteWindowConsistent)
    (hPoles : hasKappaPoles)
    (hPencil : pencilReadsPoles) :
    finiteWindowConsistent ∧ hasKappaPoles ∧ pencilReadsPoles := by
  exact ⟨hFiniteWindow, hPoles, hPencil⟩

end Omega.Zeta
