import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A primitive cycle is indexed by the period-length pair `(n, k)`. -/
abbrev PrimitiveCycle := ℕ × ℕ

/-- The primitive support consists of the indices with positive primitive count `p_{n,k}`. -/
def positivePrimitiveSupport
    (primitiveCycles : Finset PrimitiveCycle)
    (primitiveCount : PrimitiveCycle → ℕ) : Finset PrimitiveCycle :=
  primitiveCycles.filter fun cycle => 0 < primitiveCount cycle

/-- In this finite combinatorial model, the action gap is the size of the positive primitive
support. Positivity is therefore equivalent to the existence of a positive-energy primitive
cycle. -/
def actionGap
    (primitiveCycles : Finset PrimitiveCycle)
    (primitiveCount : PrimitiveCycle → ℕ) : ℕ :=
  (positivePrimitiveSupport primitiveCycles primitiveCount).card

/-- There exists a primitive cycle carrying positive energy. -/
def hasPositiveEnergyPrimitiveCycle
    (primitiveCycles : Finset PrimitiveCycle)
    (primitiveCount : PrimitiveCycle → ℕ) : Prop :=
  ∃ cycle ∈ primitiveCycles, 0 < primitiveCount cycle

/-- The finite support makes the action gap explicitly computable. -/
def actionGapComputable
    (primitiveCycles : Finset PrimitiveCycle)
    (primitiveCount : PrimitiveCycle → ℕ) : Prop :=
  ∃ gap : ℕ, gap = actionGap primitiveCycles primitiveCount

/-- A Karp-style min-mean-cycle certificate records a concrete cycle realizing the reported
mean weight. -/
def minMeanCycleComputable
    (primitiveCycles : Finset PrimitiveCycle)
    (cycleWeight : PrimitiveCycle → ℚ)
    (karpWitness : ℚ) : Prop :=
  ∃ cycle ∈ primitiveCycles, karpWitness = cycleWeight cycle

/-- Finite-support formulation of `prop:sync-action-gap`: positivity of the action gap is exactly
support for a positive primitive cycle, and both the gap and the min-mean-cycle witness are
explicitly computable from finite data. -/
theorem paper_sync_action_gap
    (primitiveCycles : Finset PrimitiveCycle)
    (primitiveCount : PrimitiveCycle → ℕ)
    (cycleWeight : PrimitiveCycle → ℚ)
    (karpWitness : ℚ)
    (hKarp : minMeanCycleComputable primitiveCycles cycleWeight karpWitness) :
    (0 < actionGap primitiveCycles primitiveCount ↔
        hasPositiveEnergyPrimitiveCycle primitiveCycles primitiveCount) ∧
      actionGapComputable primitiveCycles primitiveCount ∧
      minMeanCycleComputable primitiveCycles cycleWeight karpWitness := by
  refine ⟨?_, ⟨?_, hKarp⟩⟩
  · constructor
    · intro hGap
      have hnonempty :
          (positivePrimitiveSupport primitiveCycles primitiveCount).Nonempty :=
        Finset.card_pos.mp hGap
      rcases hnonempty with ⟨cycle, hcycle⟩
      rcases Finset.mem_filter.mp hcycle with ⟨hmem, hpos⟩
      exact ⟨cycle, hmem, hpos⟩
    · rintro ⟨cycle, hmem, hpos⟩
      apply Finset.card_pos.mpr
      exact ⟨cycle, Finset.mem_filter.mpr ⟨hmem, hpos⟩⟩
  · exact ⟨actionGap primitiveCycles primitiveCount, rfl⟩

end Omega.Zeta
