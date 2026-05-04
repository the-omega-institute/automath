import Mathlib.Data.Set.PowersetCard
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-semisimple-boundary-forgetfulness`. -/
theorem paper_conclusion_window6_semisimple_boundary_forgetfulness {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 8) :
    (∀ S T : Finset ι, S.card = 3 → T.card = 3 →
      ∃ e : ι ≃ ι, ∀ x : ι, x ∈ S ↔ e x ∈ T) ∧
      1 < Fintype.card {S : Finset ι // S.card = 3} := by
  constructor
  · intro S T hS hT
    let eS : {x : ι // x ∈ S} ≃ {x : ι // x ∈ T} :=
      Fintype.equivOfCardEq (by simp [Fintype.card_subtype, hS, hT])
    let eC : {x : ι // ¬ x ∈ S} ≃ {x : ι // ¬ x ∈ T} :=
      Fintype.equivOfCardEq (by
        rw [Fintype.card_subtype_compl (fun x => x ∈ S),
          Fintype.card_subtype_compl (fun x => x ∈ T)]
        simp [Fintype.card_subtype, hS, hT])
    refine ⟨Equiv.subtypeCongr eS eC, ?_⟩
    intro x
    by_cases hx : x ∈ S
    · simp [Equiv.subtypeCongr, hx]
    · have hnT : (Equiv.subtypeCongr eS eC x) ∉ T := by
        simpa [Equiv.subtypeCongr, hx] using (eC ⟨x, hx⟩).property
      simp [hx, hnT]
  · have hchoose : Fintype.card {S : Finset ι // S.card = 3} = Nat.choose 8 3 := by
      rw [Fintype.card_eq_nat_card]
      change Nat.card (Set.powersetCard ι 3) = Nat.choose 8 3
      calc
        Nat.card (Set.powersetCard ι 3) = Nat.choose (Nat.card ι) 3 := by
          exact Set.powersetCard.card (α := ι) (n := 3)
        _ = Nat.choose 8 3 := by
          simp [Nat.card_eq_fintype_card, hι]
    rw [hchoose]
    norm_num [Nat.choose]

end Omega.Conclusion
