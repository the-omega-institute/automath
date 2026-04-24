import Mathlib.Tactic
import Omega.SyncKernelWeighted.GMEnergyExponentTwistCriterion
import Omega.SyncKernelWeighted.GMajorArcRigidityAffineAutocorr

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:gm-triple-complementarity`. In the arithmetic-obstruction branch, the
obstruction forces a major-arc witness; the inverse-major-arc theorem upgrades that witness to
affine near-saturation, the rigidity package yields a positive affine-autocorrelation window, and
the resonant twist criterion upgrades the energy exponent to the phase-transition regime. -/
theorem paper_gm_triple_complementarity
    (scale residualEnergy signalNorm majorArcMass saturationConstant concentrationConstant : ℝ)
    (modulus cycleGcd : ℕ)
    (baselineExponent energyExponent perronRadius twistedRadius mainArcContribution : ℝ)
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
    (hobstruction : modulus ∣ cycleGcd)
    (hmajor_of_obstruction : modulus ∣ cycleGcd →
      gm_affine_inverse_major_arc_major_arc_concentration_statement
        majorArcMass signalNorm concentrationConstant)
    (hstrict_of_obstruction : modulus ∣ cycleGcd →
      concentrationConstant * signalNorm < majorArcMass)
    (hresonant_of_obstruction : modulus ∣ cycleGcd →
      gm_energy_exponent_twist_criterion_resonant_case
        baselineExponent energyExponent perronRadius twistedRadius mainArcContribution) :
    gm_affine_inverse_major_arc_near_saturation_statement
        scale residualEnergy signalNorm saturationConstant ∧
      gm_energy_exponent_twist_criterion_phase_transition
        baselineExponent energyExponent ∧
      0 < gm_major_arc_rigidity_affine_autocorr_phaseCoherentMass
        majorArcMass signalNorm concentrationConstant ∧
      0 < gm_major_arc_rigidity_affine_autocorr_parameterRadius
        majorArcMass signalNorm concentrationConstant ∧
      ∀ t : ℝ,
        |t| ≤ gm_major_arc_rigidity_affine_autocorr_parameterRadius
            majorArcMass signalNorm concentrationConstant →
          0 < gm_major_arc_rigidity_affine_autocorr_autocorrelationIntegral
            majorArcMass signalNorm concentrationConstant t := by
  have hmajor :
      gm_affine_inverse_major_arc_major_arc_concentration_statement
        majorArcMass signalNorm concentrationConstant :=
    hmajor_of_obstruction hobstruction
  have hstrict : concentrationConstant * signalNorm < majorArcMass :=
    hstrict_of_obstruction hobstruction
  have hphase :
      gm_energy_exponent_twist_criterion_phase_transition
        baselineExponent energyExponent :=
    (paper_gm_energy_exponent_twist_criterion
      baselineExponent energyExponent perronRadius twistedRadius 0 0 mainArcContribution).2
        (hresonant_of_obstruction hobstruction)
  rcases
      paper_gm_major_arc_rigidity_affine_autocorr
        scale residualEnergy signalNorm majorArcMass saturationConstant concentrationConstant
        hforward hback hmajor hstrict with
    ⟨hnear, hmass, hradius, hauto⟩
  exact ⟨hnear, hphase, hmass, hradius, hauto⟩

end Omega.SyncKernelWeighted
