import Mathlib.Tactic
import Omega.Folding.MetallicParetoFrontier
import Omega.Folding.MetallicIntegerScalarizationThreshold

namespace Omega.Folding

/-- Chapter-local package for the continuous metallic Pareto scale law. The imported frontier and
threshold files fix the ambient Pareto window and the scalarization phase split; this structure
records the optimizer `A_β`, the critical threshold, and the first-order balance certificate in the
paper-facing form needed by the corollary. -/
structure MetallicParetoScaleLawData where
  optimalScale : Real → Real
  betaCritical : Real
  firstOrderBalance : Real → Prop
  betaCritical_nonneg : 0 ≤ betaCritical
  optimalScale_mem_Icc :
      ∀ β : Real, 0 ≤ β → optimalScale β ∈ Set.Icc (1 : Real) (3 / 2 : Real)
  thresholdSplit :
      ∀ β : Real, 0 ≤ β →
        (β < betaCritical ∧ firstOrderBalance β) ∨
          (betaCritical ≤ β ∧ optimalScale β = 1)

/-- Paper-facing corollary: the scalarization optimizer stays inside the metallic Pareto window,
below the critical weight it satisfies the interior first-order balance, and at or above the
critical weight it locks to the exposed endpoint `A = 1`.
    cor:metallic-pareto-scale-law -/
theorem paper_metallic_pareto_scale_law (h : MetallicParetoScaleLawData) :
    (forall beta : Real, 0 <= beta -> 1 <= h.optimalScale beta /\ h.optimalScale beta <= 3 / 2) /\
      (forall beta : Real, 0 <= beta -> beta < h.betaCritical -> h.firstOrderBalance beta) /\
      (forall beta : Real, h.betaCritical <= beta -> h.optimalScale beta = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro beta hbeta
    simpa [Set.mem_Icc] using h.optimalScale_mem_Icc beta hbeta
  · intro beta hbeta hlt
    rcases h.thresholdSplit beta hbeta with hbelow | habove
    · exact hbelow.2
    · exfalso
      linarith
  · intro beta hbeta
    have hnonneg : 0 ≤ beta := le_trans h.betaCritical_nonneg hbeta
    rcases h.thresholdSplit beta hnonneg with hbelow | habove
    · exfalso
      linarith
    · exact habove.2

end Omega.Folding
