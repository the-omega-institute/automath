import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-affine-fiber-arithmetic-support`. -/
theorem paper_conclusion_window6_affine_fiber_arithmetic_support :
    let R2lin : Finset Nat := {13, 14, 15, 16, 17, 18, 19, 20}
    let R3punc : Finset Nat := {9, 10, 11, 12}
    let R4flat : Finset Nat := {0, 4, 8}
    let R4skew : Finset Nat := {1, 2, 3, 5, 6, 7}
    R2lin ∪ R3punc ∪ R4flat ∪ R4skew = Finset.range 21 ∧
      R2lin.card = 8 ∧
      R3punc.card = 4 ∧
      R4flat.card = 3 ∧
      R4skew.card = 6 ∧
      R2lin ∩ R3punc = ∅ ∧
      R2lin ∩ R4flat = ∅ ∧
      R2lin ∩ R4skew = ∅ ∧
      R3punc ∩ R4flat = ∅ ∧
      R3punc ∩ R4skew = ∅ ∧
      R4flat ∩ R4skew = ∅ := by
  native_decide

end Omega.Conclusion
