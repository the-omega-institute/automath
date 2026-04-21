import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Sentence roles used in the canonical window-6 results paragraph skeleton. -/
inductive ResultSentenceRole where
  | claim
  | evidence
  | statistic
  | mechanism
  deriving DecidableEq, Repr

/-- Canonical four-step paragraph skeleton for the first window-6 results paragraphs. -/
def window6ResultsParagraphRoles : List ResultSentenceRole :=
  [ResultSentenceRole.claim, ResultSentenceRole.evidence,
    ResultSentenceRole.statistic, ResultSentenceRole.mechanism]

/-- Paragraphs that have not passed the protocol gate remain placeholders. -/
def window6PreProtocolParagraphIsPlaceholder (protocolPassed : Bool) : Bool :=
  !protocolPassed

private theorem window6PreProtocolParagraphIsPlaceholder_true :
    window6PreProtocolParagraphIsPlaceholder false = true := by
  rfl

/-- Paper label: `prop:typed-address-biaxial-completion-window6-results-organization-principle`. -/
theorem paper_typed_address_biaxial_completion_window6_results_organization_principle :
    window6ResultsParagraphRoles = [ResultSentenceRole.claim, ResultSentenceRole.evidence,
      ResultSentenceRole.statistic, ResultSentenceRole.mechanism] := by
  have hPlaceholder : window6PreProtocolParagraphIsPlaceholder false = true :=
    window6PreProtocolParagraphIsPlaceholder_true
  simp at hPlaceholder
  rfl

end Omega.TypedAddressBiaxialCompletion
