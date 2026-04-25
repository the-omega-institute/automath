import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.GMAffineInverseMajorArc

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The `L²` mass carried by the phase-coherent set extracted from a strict major-arc excess. -/
def gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
    (majorArcMass signalNorm concentrationConstant : ℝ) : ℝ :=
  majorArcMass - concentrationConstant * signalNorm

/-- The admissible affine-parameter window attached to the phase-coherent mass. -/
def gm_major_arc_rigidity_affine_autocorr_parameterRadius
    (majorArcMass signalNorm concentrationConstant : ℝ) : ℝ :=
  gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
    majorArcMass signalNorm concentrationConstant / 2

/-- A concrete lower model for the affine autocorrelation integral on the coherent window. -/
def gm_major_arc_rigidity_affine_autocorr_autocorrelationIntegral
    (majorArcMass signalNorm concentrationConstant t : ℝ) : ℝ :=
  gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
      majorArcMass signalNorm concentrationConstant -
    |t|

/-- Paper label: `prop:gm-major-arc-rigidity-affine-autocorr`. Major-arc concentration forces the
near-saturation branch of the affine inverse theorem, and any strict major-arc excess yields a
positive phase-coherent mass together with a macroscopic affine parameter window on which the
autocorrelation lower model stays uniformly positive. -/
theorem paper_gm_major_arc_rigidity_affine_autocorr
    (scale residualEnergy signalNorm majorArcMass saturationConstant concentrationConstant : ℝ)
    (hforward :
      gm_affine_inverse_major_arc_near_saturation_statement
          scale residualEnergy signalNorm saturationConstant →
        gm_affine_inverse_major_arc_major_arc_concentration_statement
          majorArcMass signalNorm concentrationConstant)
    (hback :
      gm_affine_inverse_major_arc_major_arc_concentration_statement
          majorArcMass signalNorm concentrationConstant →
        gm_affine_inverse_major_arc_near_saturation_statement
          scale residualEnergy signalNorm saturationConstant)
    (hmajor :
      gm_affine_inverse_major_arc_major_arc_concentration_statement
        majorArcMass signalNorm concentrationConstant)
    (hstrict : concentrationConstant * signalNorm < majorArcMass) :
    gm_affine_inverse_major_arc_near_saturation_statement
        scale residualEnergy signalNorm saturationConstant ∧
      0 < gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
        majorArcMass signalNorm concentrationConstant ∧
      0 < gm_major_arc_rigidity_affine_autocorr_parameterRadius
        majorArcMass signalNorm concentrationConstant ∧
      ∀ t : ℝ,
        |t| ≤ gm_major_arc_rigidity_affine_autocorr_parameterRadius
            majorArcMass signalNorm concentrationConstant →
          0 < gm_major_arc_rigidity_affine_autocorr_autocorrelationIntegral
            majorArcMass signalNorm concentrationConstant t := by
  let D : gm_affine_inverse_major_arc_data :=
    { gm_affine_inverse_major_arc_scale := scale
      gm_affine_inverse_major_arc_residual_energy := residualEnergy
      gm_affine_inverse_major_arc_signal_norm := signalNorm
      gm_affine_inverse_major_arc_major_arc_mass := majorArcMass
      gm_affine_inverse_major_arc_saturation_constant := saturationConstant
      gm_affine_inverse_major_arc_concentration_constant := concentrationConstant
      gm_affine_inverse_major_arc_near_saturation_implies_major_arc_concentration := hforward
      gm_affine_inverse_major_arc_major_arc_concentration_implies_near_saturation := hback }
  have hmajorD :
      gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_major_arc_concentration D := by
    simpa [gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_major_arc_concentration, D]
      using hmajor
  have hnearD :
      gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_near_saturation D :=
    (paper_gm_affine_inverse_major_arc D).2 hmajorD
  have hnear :
      gm_affine_inverse_major_arc_near_saturation_statement
        scale residualEnergy signalNorm saturationConstant := by
    simpa [gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_near_saturation, D] using
      hnearD
  have hmass_pos :
      0 < gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
        majorArcMass signalNorm concentrationConstant := by
    unfold gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
    linarith
  have hradius_pos :
      0 < gm_major_arc_rigidity_affine_autocorr_parameterRadius
        majorArcMass signalNorm concentrationConstant := by
    unfold gm_major_arc_rigidity_affine_autocorr_parameterRadius
    linarith
  refine ⟨hnear, hmass_pos, hradius_pos, ?_⟩
  intro t ht
  have ht' :
      |t| ≤ gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
        majorArcMass signalNorm concentrationConstant / 2 := by
    simpa [gm_major_arc_rigidity_affine_autocorr_parameterRadius] using ht
  have hbound :
      |t| <
        gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
          majorArcMass signalNorm concentrationConstant := by
    linarith
  unfold gm_major_arc_rigidity_affine_autocorr_autocorrelationIntegral
  exact sub_pos.mpr hbound

end

end Omega.SyncKernelWeighted
