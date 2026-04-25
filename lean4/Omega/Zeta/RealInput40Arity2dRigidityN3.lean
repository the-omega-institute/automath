import Mathlib.Tactic
import Omega.Zeta.RealInput40Arity2dRigidityN2

namespace Omega.Zeta

/-- The explicit coefficient table extracted from `P₃(q,r) = 4 q`. -/
def real_input_40_arity_2d_rigidity_n3_table : List RealInput40Arity2dOrbitClass :=
  [(1, 0, 4)]

/-- Concrete audited input for the length-`3` real-input-40 rigidity table. -/
structure RealInput40Arity2dRigidityN3Data where
  auditedTable : List RealInput40Arity2dOrbitClass
  auditedTable_spec : auditedTable = real_input_40_arity_2d_rigidity_n3_table

namespace RealInput40Arity2dRigidityN3Data

/-- The length-`3` table has total count `4`, and every primitive orbit lies in the unique
`(χ, N₋) = (1, 0)` class extracted from `P₃(q,r) = 4 q`. -/
def Holds (D : RealInput40Arity2dRigidityN3Data) : Prop :=
  realInput40Arity2dOrbitTotal D.auditedTable = 4 ∧
    realInput40Arity2dOrbitMultiplicity D.auditedTable 1 0 = 4

end RealInput40Arity2dRigidityN3Data

/-- Paper label: `cor:real-input-40-arity-2d-rigidity-n3`.
The explicit `P₃(q,r)` coefficient table contains `4` primitive length-`3` orbits, all lying in
the unique `(χ, N₋) = (1, 0)` class. -/
theorem paper_real_input_40_arity_2d_rigidity_n3 (D : RealInput40Arity2dRigidityN3Data) :
    D.Holds := by
  rcases D with ⟨auditedTable, rfl⟩
  change
    realInput40Arity2dOrbitTotal real_input_40_arity_2d_rigidity_n3_table = 4 ∧
      realInput40Arity2dOrbitMultiplicity real_input_40_arity_2d_rigidity_n3_table 1 0 = 4
  native_decide

end Omega.Zeta
