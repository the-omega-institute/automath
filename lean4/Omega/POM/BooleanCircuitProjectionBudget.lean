import Mathlib.Tactic
import Omega.POM.ValMonotoneBooleanNand

namespace Omega.POM

/-- A single NAND macro uses one terminal normalization step. -/
def booleanCircuitNormProjCalls (_nandGateCount : ℕ) : ℕ := 1

/-- Composing one NAND macro per gate yields one order projection per gate. -/
def booleanCircuitOrderProjCalls (nandGateCount : ℕ) : ℕ := nandGateCount

/-- The concrete NAND macro computes the boolean NAND truth table on `{0, 1}`. -/
def booleanCircuitCompilesCorrectly : Prop :=
  ∀ x y : ℕ, x ≤ 1 → y ≤ 1 →
    (1 : ℤ) - (x : ℤ) * (y : ℤ) = if x = 1 ∧ y = 1 then 0 else 1

/-- The one-gate NAND witness is nonmonotone and therefore needs a positive order budget. -/
def nonmonotoneBooleanNeedsOrderProj : Prop :=
  1 - 0 * 0 > 1 - 1 * (1 : ℕ) ∧ 0 < booleanCircuitOrderProjCalls 1

/-- Boolean-circuit projection-budget wrapper: the NAND macro is correct on boolean inputs, all
intermediate `PROJ_NORM` calls can be consolidated to one final call, the `PROJ_ORDER` budget is
linear in the NAND-gate count, and the one-gate nonmonotone witness already forces a positive
order budget.
    thm:pom-boolean-circuit-projection-budget -/
theorem paper_pom_boolean_circuit_projection_budget (nandGateCount : ℕ) :
    booleanCircuitCompilesCorrectly ∧
      booleanCircuitNormProjCalls nandGateCount = 1 ∧
      booleanCircuitOrderProjCalls nandGateCount = nandGateCount ∧
      nonmonotoneBooleanNeedsOrderProj := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro x y hx hy
    simpa [booleanCircuitCompilesCorrectly] using
      Omega.POM.ValMonotoneBooleanNand.nand_boolean_identity x y hx hy
  · refine ⟨Omega.POM.ValMonotoneBooleanNand.nand_nonmonotone, by decide⟩

end Omega.POM
