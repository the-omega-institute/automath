import Omega.GU.U1ThroatIdentity

namespace Omega.GU

/-- Local witness for the three ingredients used in the paper-facing Möbius-duality package. -/
structure MobiusDualityWitness where
  u : ℝ
  u_pos : 0 < u
  omegaInversionFixedPoint : u = 1 / u
  cayleySignFlip : Prop
  poleBarrierBoundaryNormalization : Prop
  hasCayleySignFlip : cayleySignFlip
  hasPoleBarrierBoundaryNormalization : poleBarrierBoundaryNormalization

/-- Unified Möbius duality means the inversion fixed point collapses to `u = 1`, while the Cayley
sign-flip and pole-barrier boundary normalization are simultaneously available. -/
def MobiusDualityWitness.admitsUnifiedMobiusDuality (D : MobiusDualityWitness) : Prop :=
  D.u = 1 ∧ D.cayleySignFlip ∧ D.poleBarrierBoundaryNormalization

/-- Paper-facing GU wrapper for the unified Möbius duality package.
    prop:mobius-duality-unified -/
theorem paper_gut_mobius_duality_unified (D : MobiusDualityWitness) :
    D.admitsUnifiedMobiusDuality := by
  have hu1 : D.u = 1 := by
    exact (Omega.GU.U1ThroatIdentity.paper_gut_u1_throat_identity_package D.u_pos).mp
      D.omegaInversionFixedPoint
  exact ⟨hu1, D.hasCayleySignFlip, D.hasPoleBarrierBoundaryNormalization⟩

end Omega.GU
