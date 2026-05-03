import Omega.Conclusion.BinfoldFrozenEscortExactRecoveryPhaseTransition

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-binfold-frozen-escort-recovery-threshold-temperature-independent`. -/
theorem paper_conclusion_binfold_frozen_escort_recovery_threshold_temperature_independent
    (α β a : ℕ) :
    ((β < α) →
      Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop
        (nhds 0)) ∧
    ((α < β) →
      Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop
        (nhds 1)) := by
  have _temperatureParameter := a
  exact paper_conclusion_binfold_frozen_escort_exact_recovery_phase_transition α β

end Omega.Conclusion
