import Omega.Conclusion.Period3FiberExactMultiplicity

namespace Omega.Conclusion

open Omega.Conclusion.Period3FiberExactMultiplicity

/-- Paper label: `cor:conclusion-single-fiber-wedderburn-big-block`. -/
theorem paper_conclusion_single_fiber_wedderburn_big_block (n : ℕ) :
    ∃ blockSize : ℕ,
      blockSize =
          Fintype.card
            (Omega.Conclusion.Period3FiberExactMultiplicity.Period3FiberBlockChoices n) ∧
        blockSize = 2 ^ n := by
  refine ⟨Fintype.card
    (Omega.Conclusion.Period3FiberExactMultiplicity.Period3FiberBlockChoices n), rfl, ?_⟩
  exact (paper_conclusion_period3_fiber_exact_multiplicity n).2

end Omega.Conclusion
