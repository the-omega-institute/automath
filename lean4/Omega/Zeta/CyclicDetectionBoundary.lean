import Mathlib.LinearAlgebra.Span.Basic
import Omega.Zeta.AbelianShadowDefect
import Omega.Zeta.CyclicQuotientsOneDimensionalCharacters

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact boundary of cyclic detection in
    `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`.
    thm:cyclic-detection-boundary -/
theorem paper_etds_cyclic_detection_boundary
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (cyclicPullbacks oneDimensional : Set V)
    (orthogonal factorsThroughAbelian nonabelianDefectZero higherCoefficientsZero : Prop)
    (abelianEnergy nonabelianEnergy oneDimensionalEnergy higherDimensionalEnergy : ℝ)
    (hforward : ∀ ⦃v : V⦄, v ∈ cyclicPullbacks → v ∈ oneDimensional)
    (hbackward : ∀ ⦃v : V⦄, v ∈ oneDimensional → v ∈ cyclicPullbacks)
    (hAbEnergy : abelianEnergy = oneDimensionalEnergy)
    (hNaEnergy : nonabelianEnergy = higherDimensionalEnergy)
    (hFactorToCoeff : factorsThroughAbelian → higherCoefficientsZero)
    (hCoeffToDefect : higherCoefficientsZero → nonabelianDefectZero)
    (hDefectToFactor : nonabelianDefectZero → factorsThroughAbelian)
    (hOrthogonal : orthogonal) :
    Submodule.span K cyclicPullbacks = Submodule.span K oneDimensional ∧
      orthogonal ∧
      (factorsThroughAbelian ↔ nonabelianDefectZero) ∧
      (nonabelianDefectZero ↔ higherCoefficientsZero) := by
  have hSpan :=
    paper_etds_cyclic_quotients_one_dimensional_characters
      (K := K) cyclicPullbacks oneDimensional hforward hbackward
  have hShadow :=
    paper_etds_abelian_shadow_defect
      orthogonal factorsThroughAbelian nonabelianDefectZero higherCoefficientsZero
      abelianEnergy nonabelianEnergy oneDimensionalEnergy higherDimensionalEnergy
      hAbEnergy hNaEnergy hFactorToCoeff hCoeffToDefect hDefectToFactor hOrthogonal
  exact ⟨hSpan, hShadow.1, hShadow.2.2.2.1, hShadow.2.2.2.2⟩

end Omega.Zeta
