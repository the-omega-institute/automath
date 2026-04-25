import Mathlib.Tactic
import Omega.Conclusion.ScreenGraphicMatroidCorankSupermodularity

namespace Omega.Conclusion

open Finset

/-- Paper label: `thm:conclusion-delayed-completion-collision-torsor-rank-law`.
Enlarging the visible screen decreases the corank-style completion cost by exactly the amount that
the graphic-matroid rank increases. -/
theorem paper_conclusion_delayed_completion_collision_torsor_rank_law
    (D : ScreenGraphicMatroidData) (S T : Finset D.Edge) (hST : S ⊆ T) :
    let lambdaS := D.screenCost S
    let lambdaT := D.screenCost T
    lambdaT <= lambdaS ∧ (lambdaS - lambdaT = D.rank T - D.rank S) := by
  dsimp
  rcases paper_conclusion_screen_graphic_matroid_corank_supermodularity D with ⟨hcorank, _⟩
  rcases hcorank with ⟨_, _, hscreenCost_mono⟩
  have hrank_mono : D.rank S ≤ D.rank T := D.rank_mono hST
  have hS_bdd : D.rank S ≤ D.vertexCount - 1 := D.rank_bounded S
  have hT_bdd : D.rank T ≤ D.vertexCount - 1 := D.rank_bounded T
  constructor
  · exact hscreenCost_mono hST
  · simp [ScreenGraphicMatroidData.screenCost]
    omega

end Omega.Conclusion
