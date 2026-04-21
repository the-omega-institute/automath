import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-serrin-shell-rank-single-coordinate-completeness`. -/
theorem paper_conclusion_serrin_shell_rank_single_coordinate_completeness {Ω R S : Type}
    (q : Ω → R) (hq : Function.Surjective q) (A : Ω → S)
    (hA : ∀ x y, q x = q y → A x = A y) : ∃! A' : R → S, A = A' ∘ q := by
  classical
  let A' : R → S := fun r => A (Classical.choose (hq r))
  refine ⟨A', ?_, ?_⟩
  · funext x
    dsimp [A']
    exact hA x (Classical.choose (hq (q x))) (Classical.choose_spec (hq (q x))).symm
  · intro B hB
    funext r
    rcases hq r with ⟨x, rfl⟩
    have hBx : A x = B (q x) := congrFun hB x
    have hA'x : A x = A' (q x) := by
      dsimp [A']
      exact hA x (Classical.choose (hq (q x))) (Classical.choose_spec (hq (q x))).symm
    exact hBx.symm.trans hA'x

end Omega.Conclusion
