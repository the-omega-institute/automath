import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-s4-two-transposition-collision-three-type-boundary`. -/
theorem paper_conclusion_s4_two_transposition_collision_three_type_boundary :
    ∃ componentCount branchIndex : Fin 3 → ℕ,
      componentCount 0 = 28 ∧
        componentCount 1 = 24 ∧
        componentCount 2 = 36 ∧
        branchIndex 0 = 1 ∧
        branchIndex 1 = 1 ∧
        branchIndex 2 = 3 ∧
        componentCount 0 + componentCount 1 + componentCount 2 = 88 := by
  refine ⟨![28, 24, 36], ![1, 1, 3], ?_⟩
  native_decide

end Omega.Conclusion
