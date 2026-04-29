import Mathlib.Data.Set.PowersetCard
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Abstract choices of a boundary ideal are the `3` selected `M₂` summands among the `8`
available `M₂` summands in the window-`6` semisimple algebra. -/
abbrev conclusion_window6_boundary_ideal_six_bit_barrier_choice :=
  {S : Finset (Fin 8) // S.card = 3}

/-- Concrete statement for the `56` boundary-ideal choices and the binary label lower bound. -/
def conclusion_window6_boundary_ideal_six_bit_barrier_statement : Prop :=
  Fintype.card conclusion_window6_boundary_ideal_six_bit_barrier_choice = 56 ∧
    Nat.choose 8 3 = 56 ∧
    2 ^ 5 < 56 ∧
    56 ≤ 2 ^ 6 ∧
    Nat.log 2 56 + 1 = 6

/-- Paper label: `thm:conclusion-window6-boundary-ideal-six-bit-barrier`. -/
theorem paper_conclusion_window6_boundary_ideal_six_bit_barrier :
    conclusion_window6_boundary_ideal_six_bit_barrier_statement := by
  have hchoose :
      Fintype.card conclusion_window6_boundary_ideal_six_bit_barrier_choice = Nat.choose 8 3 := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Set.powersetCard (Fin 8) 3) = Nat.choose 8 3
    calc
      Nat.card (Set.powersetCard (Fin 8) 3) = Nat.choose (Nat.card (Fin 8)) 3 := by
        exact Set.powersetCard.card (α := Fin 8) (n := 3)
      _ = Nat.choose 8 3 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hchoose]
    norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · norm_num
  · norm_num
  · native_decide

end Omega.Conclusion
