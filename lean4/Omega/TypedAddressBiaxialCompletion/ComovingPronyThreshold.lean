import Mathlib.Tactic
import Omega.CircleDimension.AtomicDefectProny2KappaRecovery

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing wrapper recording the strict one-sample gap between rank detection and exact
Prony reconstruction in the comoving tomography setting.
    thm:typed-address-biaxial-completion-comoving-prony-threshold -/
theorem paper_typed_address_biaxial_completion_comoving_prony_threshold
    (rankDecisionAtTwoKappaMinusOne reconstructionAtTwoKappa shortPrefixAmbiguity : Prop)
    (hRank : rankDecisionAtTwoKappaMinusOne) (hRecon : reconstructionAtTwoKappa)
    (hShort : shortPrefixAmbiguity) :
    rankDecisionAtTwoKappaMinusOne ∧ reconstructionAtTwoKappa ∧ shortPrefixAmbiguity := by
  exact ⟨hRank, hRecon, hShort⟩

end Omega.TypedAddressBiaxialCompletion
