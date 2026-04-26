import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppBusemannPoissonMinusOne
import Omega.Zeta.OffcriticalHorocycleBusemann
import Omega.Zeta.OffcriticalQuadraticRadialCompression

namespace Omega.Zeta

open Omega.Zeta.CayleyDepthIdentity

noncomputable section

/-- The Cayley image of the off-critical point `γ + iδ`. -/
def xi_horocycle_depth_quadratic_suppression_cayleyPoint (γ δ : ℝ) : ℂ :=
  let t : ℂ := (γ : ℂ) + δ * Complex.I
  (1 + Complex.I * t) / (1 - Complex.I * t)

/-- The endpoint horocycle/Busemann depth at `-1`. -/
def xi_horocycle_depth_quadratic_suppression_busemannDepth (γ δ : ℝ) : ℝ :=
  let w := xi_horocycle_depth_quadratic_suppression_cayleyPoint γ δ
  (1 - ‖w‖ ^ 2) / ‖1 + w‖ ^ 2

/-- Concrete statement of the horocycle-depth identities and the corresponding quadratic
boundary-depth compression. -/
def xi_horocycle_depth_quadratic_suppression_statement : Prop :=
  ∀ γ δ : ℝ, 0 < δ →
    xi_horocycle_depth_quadratic_suppression_busemannDepth γ δ = δ ∧
      appOffcriticalBoundaryDepth γ δ = δ * (4 / (γ ^ 2 + (1 + δ) ^ 2)) ∧
      appOffcriticalBoundaryDepth γ δ = cayleyDepth δ γ 0 ∧
      appOffcriticalModSq γ δ < 1

/-- Paper label: `thm:xi-horocycle-depth-quadratic-suppression`. -/
theorem paper_xi_horocycle_depth_quadratic_suppression :
    xi_horocycle_depth_quadratic_suppression_statement := by
  intro γ δ hδ
  have hbusemann :=
    Omega.UnitCirclePhaseArithmetic.paper_app_busemann_poisson_minus1 γ δ hδ
  have hhorocycle := paper_app_offcritical_horocycle_busemann γ δ hδ
  have hradial := paper_xi_offcritical_quadratic_radial_compression γ δ hδ
  refine ⟨?_, hhorocycle.2, hhorocycle.1, hradial.1.1⟩
  simpa [xi_horocycle_depth_quadratic_suppression_busemannDepth,
    xi_horocycle_depth_quadratic_suppression_cayleyPoint] using hbusemann

end

end Omega.Zeta
