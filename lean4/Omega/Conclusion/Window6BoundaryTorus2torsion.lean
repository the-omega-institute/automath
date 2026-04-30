import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-torus-2torsion`. -/
theorem paper_conclusion_window6_boundary_torus_2torsion :
    Fintype.card (Fin 3 → ZMod 2) = 8 ∧
      (∀ g : Fin 3 → ZMod 2, g + g = 0) ∧
      (∀ i : Fin 3, ∃ g : Fin 3 → ZMod 2,
        g i = 1 ∧ ∀ j : Fin 3, j ≠ i → g j = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  · intro g
    funext i
    exact CharTwo.add_self_eq_zero (g i)
  · intro i
    refine ⟨fun j => if j = i then (1 : ZMod 2) else 0, ?_, ?_⟩
    · simp
    · intro j hji
      simp [hji]

end Omega.Conclusion
