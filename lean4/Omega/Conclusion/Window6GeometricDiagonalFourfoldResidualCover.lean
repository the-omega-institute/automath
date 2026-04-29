import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-geometric-diagonal-fourfold-residual-cover`. -/
theorem paper_conclusion_window6_geometric_diagonal_fourfold_residual_cover {C : Type*}
    [Fintype C] (extensionCount mass : C → ℕ) (hC : Fintype.card C = 2 ^ 2)
    (hext : ∀ c : C, extensionCount c = 2 ^ 19)
    (hmass : ∀ c : C, mass c = 2 ^ 37 * 3 ^ 13) :
    Fintype.card C = 4 ∧ (∀ c : C, extensionCount c = 2 ^ 19) ∧
      (∀ c : C, mass c = 2 ^ 37 * 3 ^ 13) := by
  norm_num at hC
  exact ⟨hC, hext, hmass⟩

end Omega.Conclusion
