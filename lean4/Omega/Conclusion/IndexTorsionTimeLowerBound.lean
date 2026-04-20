import Mathlib.Tactic

namespace Omega.Conclusion

/-- Number of joint fiber-and-torsion outcomes that an online lift must distinguish. -/
def jointLiftOutcomeCount (fiberSize p r : Nat) : Nat :=
  fiberSize * p ^ r

/-- Number of transcripts of length `steps` over an alphabet of size `alphabet`. -/
def transcriptOutcomeCount (alphabet steps : Nat) : Nat :=
  alphabet ^ steps

/-- Feasibility means that joint outcomes inject into the transcript space. -/
def OnlineLiftFeasible (fiberSize p r alphabet steps : Nat) : Prop :=
  ∃ encode : Fin (jointLiftOutcomeCount fiberSize p r) → Fin (transcriptOutcomeCount alphabet steps),
    Function.Injective encode

/-- Counting lower bound for online lifts with fiber and torsion output data.
    prop:conclusion-index-torsion-time-lower-bound -/
theorem paper_conclusion_index_torsion_time_lower_bound
    (fiberSize p r alphabet steps : Nat) :
    OnlineLiftFeasible fiberSize p r alphabet steps ->
      fiberSize * p ^ r <= alphabet ^ steps := by
  intro h
  rcases h with ⟨encode, hencode⟩
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [jointLiftOutcomeCount, transcriptOutcomeCount, Fintype.card_fin] using hcard

end Omega.Conclusion
