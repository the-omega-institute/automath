import Mathlib.Tactic

namespace Omega.Zeta

/-- Orbit-class audit data for the explicit length-`2` coefficient table of
`P₂(q,r) = 2 q r + 4 q + r²`.  Each entry records `(χ, N₋, multiplicity)`. -/
abbrev RealInput40Arity2dOrbitClass := Int × Nat × Nat

/-- The explicit coefficient table extracted from `P₂(q,r) = 2 q r + 4 q + r²`. -/
def realInput40Arity2dRigidityN2Table : List RealInput40Arity2dOrbitClass :=
  [(0, 2, 1), (1, 1, 2), (1, 0, 4)]

/-- Total primitive-orbit count carried by a finite coefficient table. -/
def realInput40Arity2dOrbitTotal (table : List RealInput40Arity2dOrbitClass) : Nat :=
  (table.map fun entry => entry.2.2).sum

/-- Multiplicity of the `(χ, N₋)` orbit class in a finite coefficient table. -/
def realInput40Arity2dOrbitMultiplicity
    (table : List RealInput40Arity2dOrbitClass) (chi : Int) (nminus : Nat) : Nat :=
  ((table.filter fun entry => entry.1 = chi ∧ entry.2.1 = nminus).map fun entry => entry.2.2).sum

/-- Concrete audited input for the length-`2` real-input-40 rigidity table. -/
structure RealInput40Arity2dRigidityN2Data where
  auditedTable : List RealInput40Arity2dOrbitClass
  auditedTable_spec : auditedTable = realInput40Arity2dRigidityN2Table

namespace RealInput40Arity2dRigidityN2Data

/-- The length-`2` table has total count `7`, exactly one `(χ, N₋) = (0, 2)` orbit, together with
the remaining `(1, 1)` and `(1, 0)` multiplicities extracted from the same coefficient table. -/
def Holds (D : RealInput40Arity2dRigidityN2Data) : Prop :=
  realInput40Arity2dOrbitTotal D.auditedTable = 7 ∧
    realInput40Arity2dOrbitMultiplicity D.auditedTable 0 2 = 1 ∧
    realInput40Arity2dOrbitMultiplicity D.auditedTable 1 1 = 2 ∧
    realInput40Arity2dOrbitMultiplicity D.auditedTable 1 0 = 4

end RealInput40Arity2dRigidityN2Data

/-- Paper label: `cor:real-input-40-arity-2d-rigidity-n2`.
The explicit `P₂(q,r)` coefficient table contains `7` primitive length-`2` orbits, with a unique
`(χ, N₋) = (0, 2)` class and the remaining distribution `(1, 1)` twice and `(1, 0)` four times. -/
theorem paper_real_input_40_arity_2d_rigidity_n2 (D : RealInput40Arity2dRigidityN2Data) :
    D.Holds := by
  rcases D with ⟨auditedTable, rfl⟩
  change
    realInput40Arity2dOrbitTotal realInput40Arity2dRigidityN2Table = 7 ∧
      realInput40Arity2dOrbitMultiplicity realInput40Arity2dRigidityN2Table 0 2 = 1 ∧
      realInput40Arity2dOrbitMultiplicity realInput40Arity2dRigidityN2Table 1 1 = 2 ∧
      realInput40Arity2dOrbitMultiplicity realInput40Arity2dRigidityN2Table 1 0 = 4
  native_decide

end Omega.Zeta
