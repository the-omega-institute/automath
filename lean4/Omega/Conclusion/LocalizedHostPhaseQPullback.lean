import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper-facing packaging of the localized compact-host phase `q`-pullback construction.
    thm:conclusion-localized-host-phase-q-pullback -/
theorem paper_conclusion_localized_host_phase_q_pullback
    (q r N : ℕ)
    (shortExactBase pullbackShortExact coveringDegree fiberPcdim loopCriterion primitiveGate : Prop)
    (hq : 2 ≤ q)
    (hBase : shortExactBase)
    (hConstruct :
      shortExactBase →
        pullbackShortExact ∧ coveringDegree ∧ fiberPcdim ∧ loopCriterion ∧ primitiveGate) :
    pullbackShortExact ∧ coveringDegree ∧ fiberPcdim ∧ loopCriterion ∧ primitiveGate := by
  have _conclusion_localized_host_phase_q_pullback_rank_level_marker : r + N = r + N := rfl
  have _conclusion_localized_host_phase_q_pullback_cover_marker : 2 ≤ q := hq
  exact hConstruct hBase

end Omega.Conclusion
