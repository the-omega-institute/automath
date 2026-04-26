import Omega.CircleDimension.UnitarySliceDecidable
import Omega.Zeta.XiNullCompleteTrichotomyOffline

namespace Omega.Zeta

open Omega.CircleDimension.UnitarySliceDecidable

/-- Paper-facing `xi` wrapper over the unitary-slice decidability criterion: the existing finite
positive/readout witness package decides addressability on the unitary slice, and the offline
null-trichotomy wrapper supplies the three `NULL` failure modes.
    cor:xi-unitary-slice-decidable -/
theorem paper_xi_unitary_slice_decidable :
    Omega.CircleDimension.UnitarySliceDecidable.paper_cdim_unitary_slice_decidable ∧
      (∀ h : Omega.TypedAddressBiaxialCompletion.TypedAddressNullTrichotomyData,
        h.exhaustive ∧ h.semanticFailuresRequireAddressChange ∧
          h.protocolFailuresNeedProtocolRepair ∧ h.collisionFailuresNeedSupportAxisBudget) := by
  refine ⟨?_, ?_⟩
  · intro State Ref Value _ Adm Vis Γ hΓ p r _ _
    exact paper_cdim_unitary_slice_decidable_package Adm Vis Γ hΓ
  · intro h
    exact paper_xi_null_complete_trichotomy_offline h

end Omega.Zeta
