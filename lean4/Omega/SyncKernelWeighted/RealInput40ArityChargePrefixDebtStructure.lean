import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargeCoboundary

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:real-input-40-arity-charge-prefix-debt-structure`. -/
theorem paper_real_input_40_arity_charge_prefix_debt_structure
    (pathCharge pathOnes startPotential endPotential : ℤ)
    (hdecomp : pathCharge = pathOnes + startPotential - endPotential)
    (hones : 0 ≤ pathOnes) (hstart : startPotential = 0 ∨ startPotential = 1)
    (hend : endPotential = 0 ∨ endPotential = 1) :
    pathCharge = -1 ↔ pathOnes = 0 ∧ startPotential = 0 ∧ endPotential = 1 := by
  constructor
  · intro hcharge
    rcases hstart with rfl | rfl <;> rcases hend with rfl | rfl
    · simp at hdecomp ⊢
      omega
    · simp at hdecomp ⊢
      omega
    · simp at hdecomp ⊢
      omega
    · simp at hdecomp ⊢
      omega
  · rintro ⟨rfl, rfl, rfl⟩
    simpa using hdecomp

end Omega.SyncKernelWeighted
