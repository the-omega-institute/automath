import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete visible-channel data: a phase layer together with a rank-one profinite ledger. -/
structure conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_data where
  conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_phaseLayer :
    Bool
  conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_profiniteLedgerRank :
    ℕ

/-- Fixed-prime exactness of the visible channel: the phase is present and the ledger remains
rank one. -/
def conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_fixedPrimeExact
    (D :
      conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_data) :
    Prop :=
  D.conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_phaseLayer =
      true ∧
    D.conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_profiniteLedgerRank =
      1

/-- Rank-at-least-two p-adic faithfulness for the profinite ledger. -/
def conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_rankTwoPadicFaithful
    (D :
      conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_data) :
    Prop :=
  2 ≤
    D.conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_profiniteLedgerRank

/-- The phase-layer/rank-one ledger exactness and rank-two p-adic faithfulness cannot coexist. -/
def conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_statement
    (D :
      conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_data) :
    Prop :=
  ¬
    (conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_fixedPrimeExact
        D ∧
      conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_rankTwoPadicFaithful
        D)

/-- Paper label:
`prop:conclusion-completion-side-faithful-pi-channel-phase-ledger-double-obstruction`. -/
theorem paper_conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction
    (D :
      conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_data) :
    conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_statement D := by
  rintro ⟨hfixed, hfaithful⟩
  rcases hfixed with ⟨_hphase, hrank⟩
  dsimp
    [conclusion_completion_side_faithful_pi_channel_phase_ledger_double_obstruction_rankTwoPadicFaithful]
    at hfaithful
  omega

end Omega.Conclusion
