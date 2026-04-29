import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargePrefixDebtStructure

namespace Omega.SyncKernelWeighted

/-- Summing the normalized edge charge along a finite path leaves a telescoping debt bounded below
by `-1`, and the sharp case occurs exactly when no `g = 1` edge is used and the endpoint potential
drops from `0` to `1`.
    cor:real-input-40-arity-charge-prefix-debt -/
def RealInput40ArityChargePrefixDebtStatement : Prop :=
  ∀ pathCharge pathOnes startPotential endPotential : ℤ,
    pathCharge = pathOnes + startPotential - endPotential →
      0 ≤ pathOnes →
      (startPotential = 0 ∨ startPotential = 1) →
      (endPotential = 0 ∨ endPotential = 1) →
      -1 ≤ pathCharge ∧
        (pathCharge = -1 ↔ pathOnes = 0 ∧ startPotential = 0 ∧ endPotential = 1)

theorem paper_real_input_40_arity_charge_prefix_debt :
    RealInput40ArityChargePrefixDebtStatement := by
  intro pathCharge pathOnes startPotential endPotential hdecomp hones hstart hend
  refine ⟨?_, paper_real_input_40_arity_charge_prefix_debt_structure _ _ _ _ hdecomp hones
    hstart hend⟩
  rcases hstart with rfl | rfl <;> rcases hend with rfl | rfl <;> omega

end Omega.SyncKernelWeighted
