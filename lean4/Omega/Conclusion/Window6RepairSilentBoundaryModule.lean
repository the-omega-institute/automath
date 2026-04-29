import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The characteristic-two torsion identity used by the boundary-center package. -/
theorem conclusion_window6_repair_silent_boundary_module_zmod2_add_self (a : ZMod 2) :
    a + a = 0 := by
  fin_cases a <;> decide

/-- Concrete boundary-fiber packet for the window-6 repair-silent module. The center charge and
repair bit are functions on the six boundary fibers; the witness pair records the nontrivial
antisymmetric two-torsion class. -/
structure conclusion_window6_repair_silent_boundary_module_data where
  centerCharge : Fin 6 → ZMod 2
  repairBit : Fin 6 → ZMod 2
  boundaryWitnessLeft : Fin 6
  boundaryWitnessRight : Fin 6
  boundaryWitnessDistinct : boundaryWitnessLeft ≠ boundaryWitnessRight
  centerWitnessActive : centerCharge boundaryWitnessLeft + centerCharge boundaryWitnessRight = 1
  repairBitSilent : ∀ x : Fin 6, repairBit x = 0

namespace conclusion_window6_repair_silent_boundary_module_data

/-- The advertised hidden-sector package: a nontrivial antisymmetric two-torsion center class is
present, and every boundary repair bit is zero. -/
def parityActiveAndRepairSilent
    (D : conclusion_window6_repair_silent_boundary_module_data) : Prop :=
  (∃ x y : Fin 6,
      x ≠ y ∧
        D.centerCharge x + D.centerCharge y = 1 ∧
        D.centerCharge x + D.centerCharge x = 0 ∧
        D.centerCharge y + D.centerCharge y = 0) ∧
    ∀ x : Fin 6, D.repairBit x = 0

end conclusion_window6_repair_silent_boundary_module_data

/-- Paper label: `thm:conclusion-window6-repair-silent-boundary-module`. -/
theorem paper_conclusion_window6_repair_silent_boundary_module
    (D : conclusion_window6_repair_silent_boundary_module_data) :
    D.parityActiveAndRepairSilent := by
  refine ⟨?_, D.repairBitSilent⟩
  refine ⟨D.boundaryWitnessLeft, D.boundaryWitnessRight, D.boundaryWitnessDistinct,
    D.centerWitnessActive, ?_, ?_⟩
  · exact conclusion_window6_repair_silent_boundary_module_zmod2_add_self _
  · exact conclusion_window6_repair_silent_boundary_module_zmod2_add_self _

end Omega.Conclusion
