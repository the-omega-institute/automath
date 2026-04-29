import Omega.UnitCirclePhaseArithmetic.DirichletDoubleDepthTranslation
import Omega.Zeta.XiUniqueContinuousTransverseRegister

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:unit-circle-complete-phase-recorder-uniqueness`. If the recorder class is
represented by the radial logarithmic depth `log |u|` on the positive ray `u = exp radius`, then
it is phase-blind, factors through the unique continuous radial class, and any remaining datum is
carried by the discrete certificate package. -/
theorem paper_unit_circle_complete_phase_recorder_uniqueness
    (register : ℝ × ℝ → ℝ) (discreteCertificate : Prop)
    (hclass :
      ∀ u : ℝ × ℝ,
        register u =
          dirichletTimeDepth (Real.exp (Omega.Zeta.xiRadiusProjection u)))
    (hcertificate : discreteCertificate) :
    Omega.Zeta.xiFactorsThroughRadius register ∧
      Omega.Zeta.xiUniqueUpToMonotoneReparam register ∧
      (∀ u : ℝ × ℝ,
        register u =
          dirichletTimeDepth (Real.exp (Omega.Zeta.xiRadiusProjection u))) ∧
      discreteCertificate := by
  have hphase :
      ∀ radius phase₁ phase₂,
        register (radius, phase₁) = register (radius, phase₂) := by
    intro radius phase₁ phase₂
    calc
      register (radius, phase₁) =
          dirichletTimeDepth (Real.exp (Omega.Zeta.xiRadiusProjection (radius, phase₁))) :=
        hclass (radius, phase₁)
      _ = dirichletTimeDepth (Real.exp radius) := by
        simp [Omega.Zeta.xiRadiusProjection]
      _ = dirichletTimeDepth (Real.exp (Omega.Zeta.xiRadiusProjection (radius, phase₂))) := by
        simp [Omega.Zeta.xiRadiusProjection]
      _ = register (radius, phase₂) := (hclass (radius, phase₂)).symm
  have hmono : StrictMono fun radius => register (radius, 0) := by
    intro a b hab
    calc
      register (a, 0) = dirichletTimeDepth (Real.exp a) := by
        simpa [Omega.Zeta.xiRadiusProjection] using hclass (a, 0)
      _ = a := by
        simp [dirichletTimeDepth, abs_of_pos (Real.exp_pos a)]
      _ < b := hab
      _ = dirichletTimeDepth (Real.exp b) := by
        simp [dirichletTimeDepth, abs_of_pos (Real.exp_pos b)]
      _ = register (b, 0) := by
        simpa [Omega.Zeta.xiRadiusProjection] using (hclass (b, 0)).symm
  have hunique :=
    Omega.Zeta.paper_xi_unique_continuous_transverse_register register hphase hmono
  exact ⟨hunique.1, hunique.2, hclass, hcertificate⟩

end Omega.UnitCirclePhaseArithmetic
