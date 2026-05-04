import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-odd-cardinality-nontrivial-jump-forces-super-symmetry`. -/
theorem paper_conclusion_odd_cardinality_nontrivial_jump_forces_super_symmetry
    (NontrivialJump NoExtraSign SuperSymmetric : Nat → Prop)
    (hBlocks : ∀ d, Odd d → 3 ≤ d → NontrivialJump d → ¬ NoExtraSign d)
    (hSuper : ∀ d, Odd d → 3 ≤ d → ¬ NoExtraSign d → SuperSymmetric d) (d : Nat)
    (hdOdd : Odd d) (hd3 : 3 ≤ d) :
    NontrivialJump d → SuperSymmetric d := by
  intro hJump
  exact hSuper d hdOdd hd3 (hBlocks d hdOdd hd3 hJump)

end Omega.Conclusion
