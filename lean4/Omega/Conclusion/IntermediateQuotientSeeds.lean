import Mathlib.Tactic

namespace Omega.Conclusion.IntermediateQuotientSeeds

/-- Small Stirling number helper for concrete partition-count seeds. -/
def stirling2 : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

@[simp] theorem stirling2_3_1 : stirling2 3 1 = 1 := by
  native_decide

@[simp] theorem stirling2_3_2 : stirling2 3 2 = 3 := by
  native_decide

@[simp] theorem stirling2_3_3 : stirling2 3 3 = 1 := by
  native_decide

@[simp] theorem stirling2_4_2 : stirling2 4 2 = 7 := by
  native_decide

@[simp] theorem stirling2_4_3 : stirling2 4 3 = 6 := by
  native_decide

@[simp] theorem stirling2_4_4 : stirling2 4 4 = 1 := by
  native_decide

/-- Concrete Stirling-partition seeds for the intermediate quotient stage.
    thm:conclusion-intermediate-quotient -/
theorem paper_conclusion_intermediate_quotient_seeds :
    stirling2 3 1 = 1 ∧
    stirling2 3 2 = 3 ∧
    stirling2 3 3 = 1 ∧
    stirling2 4 2 = 7 ∧
    stirling2 4 3 = 6 ∧
    stirling2 4 4 = 1 ∧
    stirling2 4 2 / stirling2 3 2 = 2 ∧
    stirling2 4 3 / stirling2 3 3 = 6 ∧
    (stirling2 4 2 + stirling2 4 3 + stirling2 4 4 = 14) := by
  simp

end Omega.Conclusion.IntermediateQuotientSeeds
