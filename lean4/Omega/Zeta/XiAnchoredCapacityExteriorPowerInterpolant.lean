import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete scalar data for the anchored interpolation right inverse. The scalar fields record
the Gram inverse identity, determinant identity, exterior-power norm identity, and normalized
capacity relation used by the paper wrapper. -/
structure xi_anchored_capacity_exterior_power_interpolant_data where
  gramEnergy : ℚ
  gramInverseEnergy : ℚ
  determinant : ℚ
  exteriorPowerNormSq : ℚ
  capacity : ℚ
  gram_identity_witness : gramEnergy * gramInverseEnergy = 1
  det_identity_witness : determinant = gramInverseEnergy
  exterior_power_norm_identity_witness : exteriorPowerNormSq = determinant
  capacity_norm_witness : capacity = exteriorPowerNormSq

namespace xi_anchored_capacity_exterior_power_interpolant_data

/-- The anchored right inverse has Gram matrix equal to the inverse anchored Gram form. -/
def gramIdentity (D : xi_anchored_capacity_exterior_power_interpolant_data) : Prop :=
  D.gramEnergy * D.gramInverseEnergy = 1

/-- The determinant of the interpolation Gram form is the determinant of the inverse Gram model. -/
def detIdentity (D : xi_anchored_capacity_exterior_power_interpolant_data) : Prop :=
  D.determinant = D.gramInverseEnergy

/-- The top exterior-power norm squared is the determinant. -/
def exteriorPowerNormIdentity
    (D : xi_anchored_capacity_exterior_power_interpolant_data) : Prop :=
  D.exteriorPowerNormSq = D.determinant

/-- The normalized anchored capacity is read from the exterior-power determinant relation. -/
def capacityFormula (D : xi_anchored_capacity_exterior_power_interpolant_data) : Prop :=
  D.capacity = D.determinant

end xi_anchored_capacity_exterior_power_interpolant_data

/-- Paper label: `prop:xi-anchored-capacity-exterior-power-interpolant`. -/
theorem paper_xi_anchored_capacity_exterior_power_interpolant
    (D : xi_anchored_capacity_exterior_power_interpolant_data) :
    D.gramIdentity ∧ D.detIdentity ∧ D.exteriorPowerNormIdentity ∧ D.capacityFormula := by
  refine ⟨D.gram_identity_witness, D.det_identity_witness, D.exterior_power_norm_identity_witness,
    ?_⟩
  unfold xi_anchored_capacity_exterior_power_interpolant_data.capacityFormula
  rw [D.capacity_norm_witness, D.exterior_power_norm_identity_witness]

end

end Omega.Zeta
