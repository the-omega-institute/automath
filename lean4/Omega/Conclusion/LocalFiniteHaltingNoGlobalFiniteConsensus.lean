import Mathlib.Tactic
import Omega.Conclusion.GlobalClockVanishing

namespace Omega.Conclusion

/-- A finite global consensus time is a single natural time slice that matches every local clock
section simultaneously. -/
def conclusion_local_finite_halting_no_global_finite_consensus_uniform_time
    (D : GlobalClockObstructionData) : Prop :=
  ∃ T : ℕ, ∀ i : Fin D.coverSize, D.localClock i = Int.ofNat T

/-- Paper label: `cor:conclusion-local-finite-halting-no-global-finite-consensus`. A hypothetical
uniform finite consensus time is a global terminal readout, so the global-clock obstruction theorem
rules it out as soon as the Cech-H2 obstruction is nonzero. -/
theorem paper_conclusion_local_finite_halting_no_global_finite_consensus
    (D : GlobalClockObstructionData) (hω : D.cechH2Obstruction ≠ 0) :
    ¬ conclusion_local_finite_halting_no_global_finite_consensus_uniform_time D := by
  intro hConsensus
  apply paper_conclusion_global_clock_vanishing D hω
  rcases hConsensus with ⟨T, hT⟩
  exact ⟨Int.ofNat T, hT⟩

end Omega.Conclusion
