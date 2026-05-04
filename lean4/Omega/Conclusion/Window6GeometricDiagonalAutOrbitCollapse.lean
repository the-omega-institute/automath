import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Classical

/-- Paper label: `thm:conclusion-window6-geometric-diagonal-aut-orbit-collapse`. -/
theorem paper_conclusion_window6_geometric_diagonal_aut_orbit_collapse {V G : Type*}
    [Zero V] [Fintype V] [DecidableEq V] [Group G] [MulAction G V] (z : V)
    (hzero : ∀ g : G, g • z ≠ 0)
    (htrans : ∀ v : V, v ≠ 0 → ∃ g : G, g • z = v)
    (hcard : Fintype.card V = 2 ^ 8) :
    {v : V | ∃ g : G, g • z = v} = {v : V | v ≠ 0} ∧
      Fintype.card {v : V // ∃ g : G, g • z = v} = 255 := by
  classical
  have hset : {v : V | ∃ g : G, g • z = v} = {v : V | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩
      exact hzero g
    · exact htrans v
  have hiff : ∀ v : V, (∃ g : G, g • z = v) ↔ v ≠ 0 := by
    intro v
    exact Set.ext_iff.mp hset v
  have horbitCard :
      Fintype.card {v : V // ∃ g : G, g • z = v} =
        Fintype.card {v : V // v ≠ 0} := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun v => ⟨v.1, (hiff v.1).mp v.2⟩
        invFun := fun v => ⟨v.1, (hiff v.1).mpr v.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro v
      cases v
      rfl
    · intro v
      cases v
      rfl
  have hnonzeroCard : Fintype.card {v : V // v ≠ 0} = 255 := by
    haveI : Unique {v : V // v = 0} := {
      default := ⟨0, rfl⟩
      uniq v := by
        cases v with
        | mk v hv =>
            cases hv
            rfl
    }
    have hzeroCard : Fintype.card {v : V // v = 0} = 1 := Fintype.card_unique
    have hcompl := Fintype.card_subtype_compl (fun v : V => v = 0)
    change Fintype.card {v : V // v ≠ 0} =
        Fintype.card V - Fintype.card {v : V // v = 0} at hcompl
    rw [hcompl, hcard, hzeroCard]
    norm_num
  exact ⟨hset, by rw [horbitCard, hnonzeroCard]⟩

end Omega.Conclusion
