import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-choice-rigidification-minimal-external-bit-budget`. -/
theorem paper_conclusion_choice_rigidification_minimal_external_bit_budget {R C : Type*}
    [Fintype R] [Fintype C] (Sel : R → C) (hSel : Function.Surjective Sel) :
    Fintype.card C ≤ Fintype.card R := by
  classical
  let pick : C → R := fun c => Classical.choose (hSel c)
  have hpick : ∀ c : C, Sel (pick c) = c := by
    intro c
    exact Classical.choose_spec (hSel c)
  refine Fintype.card_le_of_injective pick ?_
  intro c1 c2 h
  calc
    c1 = Sel (pick c1) := (hpick c1).symm
    _ = Sel (pick c2) := congrArg Sel h
    _ = c2 := hpick c2

end Omega.Conclusion
