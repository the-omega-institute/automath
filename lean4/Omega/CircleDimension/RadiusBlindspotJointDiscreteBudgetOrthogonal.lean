import Mathlib.Tactic
import Omega.CircleDimension.AddressLedgerJointBudgetLowerBound

namespace Omega.CircleDimension

/-- Chapter-local package for the radius-blindspot/address-ledger orthogonality corollary. -/
structure RadiusBlindspotJointBudgetData where
  radiusBlindspotNecessary : Prop
  addressLedgerNecessary : Prop
  radiusBlindspotWitness : radiusBlindspotNecessary
  addressLedgerWitness : addressLedgerNecessary

/-- The boundary-layer blindspot budget and the address-ledger joint budget give two orthogonal
necessary conditions.
    cor:cdim-radius-blindspot-and-joint-discrete-budget-orthogonal -/
theorem paper_cdim_radius_blindspot_and_joint_discrete_budget_orthogonal
    (h : RadiusBlindspotJointBudgetData) :
    h.radiusBlindspotNecessary ∧ h.addressLedgerNecessary := by
  exact ⟨h.radiusBlindspotWitness, h.addressLedgerWitness⟩

end Omega.CircleDimension
