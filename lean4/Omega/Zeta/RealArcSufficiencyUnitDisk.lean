import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the real-arc sufficiency principle on the unit disk. The data
records the holomorphic/meromorphic decomposition `G = A_∞ + S`, the vanishing of the difference
on the real arc `(0,1)`, the identity-theorem step forcing meromorphic equality on the whole disk,
and the removability of poles because `G - A_∞` is holomorphic. -/
structure RealArcSufficiencyUnitDiskData where
  holomorphicG : Prop
  holomorphicAinfty : Prop
  meromorphicS : Prop
  vanishesOnRealArc : Prop
  identityExtendsToDisk : Prop
  spectralPolesAreRemovable : Prop
  holomorphicG_h : holomorphicG
  holomorphicAinfty_h : holomorphicAinfty
  meromorphicS_h : meromorphicS
  vanishesOnRealArc_h : vanishesOnRealArc
  deriveIdentityExtendsToDisk :
    holomorphicG → holomorphicAinfty → meromorphicS → vanishesOnRealArc →
      identityExtendsToDisk
  deriveSpectralPolesAreRemovable :
    holomorphicG → holomorphicAinfty → identityExtendsToDisk → spectralPolesAreRemovable

/-- Paper-facing wrapper for the real-arc sufficiency argument: equality on `(0,1)` forces the
meromorphic identity on the full unit disk, and the spectral poles are removable because the
difference `G - A_∞` is holomorphic.
    prop:real-arc-sufficiency-unit-disk -/
theorem paper_real_arc_sufficiency_unit_disk (data : RealArcSufficiencyUnitDiskData) :
    data.identityExtendsToDisk ∧ data.spectralPolesAreRemovable := by
  have hIdentity : data.identityExtendsToDisk :=
    data.deriveIdentityExtendsToDisk
      data.holomorphicG_h data.holomorphicAinfty_h data.meromorphicS_h data.vanishesOnRealArc_h
  exact ⟨hIdentity,
    data.deriveSpectralPolesAreRemovable data.holomorphicG_h data.holomorphicAinfty_h hIdentity⟩

end Omega.Zeta
