import Mathlib.Tactic
import Omega.CircleDimension.ComovingHorizonScanFirstLayerExtraction
import Omega.CircleDimension.RadiusBlindspotJointDiscreteBudgetOrthogonal
import Omega.TypedAddressBiaxialCompletion.BoundaryAddressCollision
import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization
import Omega.TypedAddressBiaxialCompletion.OffsliceDichotomy

namespace Omega.TypedAddressBiaxialCompletion

open scoped BigOperators

/-- Paper-facing wrapper for the finite-radius Jensen-defect blindspot dichotomy: the finite-radius
readout carries the usual nonnegativity/zero-free equivalence, the radius blindspot and address
ledger remain orthogonal necessary resources, the comoving Fourier route gives the audited
recovery path, and any fixed-chart blindspot instance either enters that recovery path or yields a
null witness while still forcing an address-collision budget witness.
    prop:typed-address-biaxial-completion-jensen-defect-blindspot -/
theorem paper_typed_address_biaxial_completion_jensen_defect_blindspot
    (B : Omega.CircleDimension.RadiusBlindspotJointBudgetData)
    (J : JensenDefectFiniteizationData) {rho : ℝ} (hrho : 0 < rho) (hrho_lt : rho < 1)
    (D : Omega.CircleDimension.ComovingHorizonScanFirstLayerExtractionData)
    (offsliceAssertion prefixRecoveryRoute nullBlindspotWitness noThirdPath : Prop)
    (hSplit : offsliceAssertion → prefixRecoveryRoute ∨ nullBlindspotWitness)
    (hNoThird : offsliceAssertion → noThirdPath)
    (c T : ℝ) (b : ℕ) (addressOccupancy : Fin (2 ^ b) → ℝ)
    (hNonneg : ∀ a, 0 ≤ addressOccupancy a)
    (hTotal : c * T^2 * Real.log T ≤ ∑ a, addressOccupancy a) :
    offsliceAssertion →
      (prefixRecoveryRoute ∨ nullBlindspotWitness) ∧
      noThirdPath ∧
      (0 ≤ J.defect rho ∧ (J.defect rho = 0 ↔ J.zeroFree rho)) ∧
      (B.radiusBlindspotNecessary ∧ B.addressLedgerNecessary) ∧
      (D.leadingAsymptoticSeparation ∧ D.leadingLayerRecovered) ∧
      ∃ a : Fin (2 ^ b), c * T^2 * Real.log T / (2 : ℝ) ^ b ≤ addressOccupancy a := by
  intro hOffslice
  have hOffsliceSplit :
      (prefixRecoveryRoute ∨ nullBlindspotWitness) ∧ noThirdPath :=
    paper_typed_address_biaxial_completion_offslice_dichotomy
      offsliceAssertion prefixRecoveryRoute nullBlindspotWitness noThirdPath hSplit hNoThird hOffslice
  have hJensen :
      0 ≤ J.defect rho ∧ (J.defect rho = 0 ↔ J.zeroFree rho) :=
    paper_typed_address_biaxial_completion_jensen_defect_finiteization J hrho hrho_lt
  have hBlindspot :
      B.radiusBlindspotNecessary ∧ B.addressLedgerNecessary :=
    Omega.CircleDimension.paper_cdim_radius_blindspot_and_joint_discrete_budget_orthogonal B
  have hRecovery :
      D.leadingAsymptoticSeparation ∧ D.leadingLayerRecovered :=
    Omega.CircleDimension.paper_cdim_comoving_horizon_scan_first_layer_extraction D
  rcases
      BoundaryAddressCollision.paper_typed_address_biaxial_completion_boundary_address_collision
        c T b addressOccupancy hNonneg hTotal with
    ⟨a, ha⟩
  exact ⟨hOffsliceSplit.1, hOffsliceSplit.2, hJensen, hBlindspot, hRecovery, a, ha⟩

end Omega.TypedAddressBiaxialCompletion
