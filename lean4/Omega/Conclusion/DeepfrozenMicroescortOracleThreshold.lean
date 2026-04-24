import Omega.Conclusion.BinfoldFrozenEscortExactRecoveryPhaseTransition

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-deepfrozen-microescort-oracle-threshold`.
In the frozen regime the microescort success probability is the reduced ratio
`min(M_m, 2^{B_m}) / M_m`; the threshold directions are exactly the two asymptotic phases
already verified for the frozen-escort phase transition. -/
theorem paper_conclusion_deepfrozen_microescort_oracle_threshold (α β : ℕ) :
    (∀ m, binfoldFrozenEscortReducedSuccess α β m =
      min ((2 : ℝ) ^ (α * m)) ((2 : ℝ) ^ (β * m)) / (2 : ℝ) ^ (α * m)) ∧
      ((β < α) →
        Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop (nhds 0)) ∧
      ((α < β) →
        Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop (nhds 1)) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · exact (paper_conclusion_binfold_frozen_escort_exact_recovery_phase_transition α β).1
  · exact (paper_conclusion_binfold_frozen_escort_exact_recovery_phase_transition α β).2

end Omega.Conclusion
