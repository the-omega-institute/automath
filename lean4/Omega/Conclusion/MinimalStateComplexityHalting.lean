import Mathlib.Tactic

namespace Omega.Conclusion

attribute [local instance] Classical.propDecidable

/-- Concrete threshold-transducer package for the halting reduction. In the halting case the
Myhill-Nerode lower bound from the distinguishable prefixes `1^i` is paired with an explicit
counter automaton on `haltingSteps + 1` states. In the non-halting case a uniform bound suffices.
-/
structure ConclusionMinimalStateComplexityHaltingData where
  halts : Prop
  haltingSteps : ℕ
  minStateCount : ℕ
  uniformBound : ℕ
  haltingLowerBound : halts → haltingSteps + 1 ≤ minStateCount
  haltingUpperBound : halts → minStateCount ≤ haltingSteps + 1
  nonhaltingUpperBound : ¬ halts → minStateCount ≤ uniformBound
  uniformGap : halts → uniformBound < haltingSteps + 1

namespace ConclusionMinimalStateComplexityHaltingData

/-- The state count encodes halting exactly when it jumps above the non-halting uniform bound. -/
def stateCountEncodesHalting (h : ConclusionMinimalStateComplexityHaltingData) : Prop :=
  h.halts ↔ h.uniformBound < h.minStateCount

end ConclusionMinimalStateComplexityHaltingData

open ConclusionMinimalStateComplexityHaltingData

/-- Paper label: `thm:conclusion-minimal-state-complexity-halting`. -/
theorem paper_conclusion_minimal_state_complexity_halting
    (h : ConclusionMinimalStateComplexityHaltingData) :
    (h.halts -> h.minStateCount = h.haltingSteps + 1) /\
      (Not h.halts -> h.minStateCount <= h.uniformBound) /\
      h.stateCountEncodesHalting := by
  refine ⟨?_, h.nonhaltingUpperBound, ?_⟩
  · intro hhalts
    exact le_antisymm (h.haltingUpperBound hhalts) (h.haltingLowerBound hhalts)
  · dsimp [ConclusionMinimalStateComplexityHaltingData.stateCountEncodesHalting]
    constructor
    · intro hhalts
      have hEq : h.minStateCount = h.haltingSteps + 1 := by
        exact le_antisymm (h.haltingUpperBound hhalts) (h.haltingLowerBound hhalts)
      rw [hEq]
      exact h.uniformGap hhalts
    · intro hlarge
      by_cases hhalts : h.halts
      · exact hhalts
      · have hsmall : h.minStateCount ≤ h.uniformBound := h.nonhaltingUpperBound hhalts
        exact False.elim (not_lt_of_ge hsmall hlarge)

end Omega.Conclusion
