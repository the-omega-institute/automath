import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiPickPoissonSchurFluxClosedForm

namespace Omega.Conclusion

open Omega.Zeta

/-- Homothetic scaling of the Pick--Poisson Schur flux. -/
noncomputable def conclusion_pick_poisson_radial_shape_separation_scaledFlux
    (lam pointWeight rho : ℝ) : ℝ :=
  xiPickPoissonSchurFlux (lam * pointWeight) rho

/-- Homothetic scaling of the corresponding trace observable. -/
noncomputable def conclusion_pick_poisson_radial_shape_separation_scaledTrace
    (lam trace : ℝ) : ℝ :=
  lam * trace

/-- Normalized share of one Schur block inside a total flux budget. -/
noncomputable def conclusion_pick_poisson_radial_shape_separation_share
    (flux totalFlux : ℝ) : ℝ :=
  flux / totalFlux

/-- Boundary potential written as the negative logarithm of the Schur flux. -/
noncomputable def conclusion_pick_poisson_radial_shape_separation_boundaryPotential
    (pointWeight rho : ℝ) : ℝ :=
  xiPickPoissonNegLogFlux pointWeight rho

/-- Boundary information combines the boundary potential with the logarithmic trace term. -/
noncomputable def conclusion_pick_poisson_radial_shape_separation_boundaryInformation
    (pointWeight rho trace : ℝ) : ℝ :=
  conclusion_pick_poisson_radial_shape_separation_boundaryPotential pointWeight rho + Real.log trace

/-- Paper label: `thm:conclusion-pick-poisson-radial-shape-separation`.
Under a positive homothety `lam`, the Schur flux and trace both scale by `lam`, hence the
normalized share is unchanged, the boundary potential shifts by `-log lam`, and the boundary
information
remains invariant. -/
theorem paper_conclusion_pick_poisson_radial_shape_separation
    (lam pointWeight rho totalFlux trace : ℝ)
    (hlam : 0 < lam) (hpoint : 0 < pointWeight) (hrho : 0 < rho)
    (htotal : 0 < totalFlux) (htrace : 0 < trace) :
    conclusion_pick_poisson_radial_shape_separation_share
        (conclusion_pick_poisson_radial_shape_separation_scaledFlux lam pointWeight rho)
        (conclusion_pick_poisson_radial_shape_separation_scaledTrace lam totalFlux) =
      conclusion_pick_poisson_radial_shape_separation_share
        (xiPickPoissonSchurFlux pointWeight rho) totalFlux ∧
      conclusion_pick_poisson_radial_shape_separation_boundaryPotential
          (lam * pointWeight) rho =
        conclusion_pick_poisson_radial_shape_separation_boundaryPotential pointWeight rho -
          Real.log lam ∧
      conclusion_pick_poisson_radial_shape_separation_boundaryInformation
          (lam * pointWeight) rho
          (conclusion_pick_poisson_radial_shape_separation_scaledTrace lam trace) =
        conclusion_pick_poisson_radial_shape_separation_boundaryInformation
          pointWeight rho trace := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have htrace_ne : trace ≠ 0 := ne_of_gt htrace
  have hshare :
      conclusion_pick_poisson_radial_shape_separation_share
          (conclusion_pick_poisson_radial_shape_separation_scaledFlux lam pointWeight rho)
          (conclusion_pick_poisson_radial_shape_separation_scaledTrace lam totalFlux) =
        conclusion_pick_poisson_radial_shape_separation_share
          (xiPickPoissonSchurFlux pointWeight rho) totalFlux := by
    unfold conclusion_pick_poisson_radial_shape_separation_share
      conclusion_pick_poisson_radial_shape_separation_scaledFlux
      conclusion_pick_poisson_radial_shape_separation_scaledTrace xiPickPoissonSchurFlux
    field_simp [hlam_ne]
  have hboundary :
      conclusion_pick_poisson_radial_shape_separation_boundaryPotential (lam * pointWeight) rho =
        conclusion_pick_poisson_radial_shape_separation_boundaryPotential pointWeight rho -
          Real.log lam := by
    have hflux_pos : 0 < xiPickPoissonSchurFlux pointWeight rho := by
      unfold xiPickPoissonSchurFlux
      exact mul_pos hpoint (sq_pos_of_pos hrho)
    have hfactor_ne : pointWeight * rho ^ 2 ≠ 0 := ne_of_gt (mul_pos hpoint (sq_pos_of_pos hrho))
    have hlog :
        Real.log (lam * (pointWeight * rho ^ 2)) =
          Real.log lam + Real.log (pointWeight * rho ^ 2) := by
      rw [Real.log_mul hlam_ne hfactor_ne]
    unfold conclusion_pick_poisson_radial_shape_separation_boundaryPotential
      xiPickPoissonNegLogFlux xiPickPoissonSchurFlux
    calc
      -Real.log (lam * pointWeight * rho ^ 2)
          = -Real.log (lam * (pointWeight * rho ^ 2)) := by rw [← mul_assoc]
      _ = -(Real.log lam + Real.log (pointWeight * rho ^ 2)) := by rw [hlog]
      _ = -Real.log (pointWeight * rho ^ 2) - Real.log lam := by ring
  have hinformation :
      conclusion_pick_poisson_radial_shape_separation_boundaryInformation
          (lam * pointWeight) rho
          (conclusion_pick_poisson_radial_shape_separation_scaledTrace lam trace) =
        conclusion_pick_poisson_radial_shape_separation_boundaryInformation pointWeight rho trace := by
    unfold conclusion_pick_poisson_radial_shape_separation_boundaryInformation
      conclusion_pick_poisson_radial_shape_separation_scaledTrace
    rw [hboundary, Real.log_mul hlam_ne htrace_ne]
    ring
  exact ⟨hshare, hboundary, hinformation⟩

end Omega.Conclusion
