import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.NullExhaustive

namespace Omega.Zeta

/-- Paper label: `thm:xi-null-complete-trichotomy-offline`. -/
theorem paper_xi_null_complete_trichotomy_offline
    (h : Omega.TypedAddressBiaxialCompletion.TypedAddressNullTrichotomyData) :
    h.exhaustive ∧ h.semanticFailuresRequireAddressChange ∧
      h.protocolFailuresNeedProtocolRepair ∧ h.collisionFailuresNeedSupportAxisBudget := by
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_null_exhaustive h

end Omega.Zeta
