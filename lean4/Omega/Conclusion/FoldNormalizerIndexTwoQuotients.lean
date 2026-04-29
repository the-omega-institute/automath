import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fold-normalizer-index-two-quotients`. -/
theorem paper_conclusion_fold_normalizer_index_two_quotients (alpha : ℕ) :
    Fintype.card {v : Fin alpha → ZMod 2 // v ≠ 0} = 2 ^ alpha - 1 := by
  classical
  let V := Fin alpha → ZMod 2
  have hV : Fintype.card V = 2 ^ alpha := by
    simp [V,
      (Fintype.card_fun : Fintype.card (Fin alpha → ZMod 2) =
        Fintype.card (ZMod 2) ^ Fintype.card (Fin alpha))]
  haveI : Unique {v : V // v = 0} := {
    default := ⟨0, rfl⟩
    uniq x := by
      ext i
      exact congrFun x.property i
  }
  have hzero : Fintype.card {v : V // v = 0} = 1 := Fintype.card_unique
  have hcompl := Fintype.card_subtype_compl (fun v : V => v = 0)
  change Fintype.card {v : V // v ≠ 0} = Fintype.card V - Fintype.card {v : V // v = 0}
    at hcompl
  rw [hV, hzero] at hcompl
  exact hcompl

end Omega.Conclusion
