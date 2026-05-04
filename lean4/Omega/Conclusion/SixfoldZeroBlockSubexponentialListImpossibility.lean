import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-sixfold-zero-block-subexponential-list-impossibility`. -/
theorem paper_conclusion_sixfold_zero_block_subexponential_list_impossibility
    {Z C : Type*} [Fintype Z] [Fintype C] [DecidableEq C] (E : Z → C) (L : ℕ)
    (hfiber : ∀ c : C, Fintype.card {z : Z // E z = c} ≤ L) :
    Fintype.card Z ≤ Fintype.card C * L := by
  classical
  have hpartition :
      Fintype.card Z = ∑ c : C, Fintype.card {z : Z // E z = c} := by
    calc
      Fintype.card Z = (Finset.univ : Finset Z).card := by simp
      _ = ∑ c ∈ (Finset.univ : Finset C),
          ((Finset.univ : Finset Z).filter fun z => E z = c).card := by
            exact Finset.card_eq_sum_card_fiberwise (f := E) (s := Finset.univ)
              (t := Finset.univ) (by intro z hz; simp)
      _ = ∑ c : C, Fintype.card {z : Z // E z = c} := by
        simp [Fintype.card_subtype]
  calc
    Fintype.card Z = ∑ c : C, Fintype.card {z : Z // E z = c} := hpartition
    _ ≤ ∑ _c : C, L := Finset.sum_le_sum fun c _hc => hfiber c
    _ = Fintype.card C * L := by simp

end Omega.Conclusion
