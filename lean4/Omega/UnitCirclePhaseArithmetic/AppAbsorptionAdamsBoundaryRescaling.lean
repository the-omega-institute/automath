import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.BoundaryAbsorptionJuliaCaratheodory

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators

noncomputable section

/-- The rescaled boundary absorption profile obtained by evaluating the base profile at `ξ^m`
and multiplying by the Adams factor `m`. -/
def app_absorption_adams_boundary_rescaling_phi (roots : List ℂ) (ξ : ℂ) (m : ℕ) : ℝ :=
  (m : ℝ) * boundaryAbsorption roots (ξ ^ m)

/-- The corresponding rescaled Julia indicator. -/
def app_absorption_adams_boundary_rescaling_j (roots : List ℂ) (ξ : ℂ) (m : ℕ) : ℝ :=
  (m : ℝ) * boundaryJuliaIndicator roots (ξ ^ m)

/-- Paper label: `cor:app-absorption-adams-boundary-rescaling`. In the finite Blaschke seed
model, the Adams pullback rescales the boundary absorption profile by evaluating at `ξ^m`; the
transported Julia indicator follows by the boundary absorption theorem. -/
theorem paper_app_absorption_adams_boundary_rescaling
    (roots : List ℂ) (ξ : ℂ) (m : ℕ) (hξ : ‖ξ‖ = 1) (hroots : ∀ a ∈ roots, ‖a‖ < 1) :
    app_absorption_adams_boundary_rescaling_phi roots ξ m =
      (m : ℝ) * ∑ i, boundaryPoissonKernel (roots.get i) (ξ ^ m) ∧
      app_absorption_adams_boundary_rescaling_j roots ξ m =
        app_absorption_adams_boundary_rescaling_phi roots ξ m ∧
      0 ≤ app_absorption_adams_boundary_rescaling_phi roots ξ m := by
  have hξpow : ‖ξ ^ m‖ = 1 := by
    simpa [norm_pow, hξ]
  have hboundary :=
    paper_app_boundary_absorption_julia_caratheodory roots (ξ ^ m) hξpow hroots
  refine ⟨?_, ?_, ?_⟩
  · unfold app_absorption_adams_boundary_rescaling_phi
    rw [hboundary.1]
  · unfold app_absorption_adams_boundary_rescaling_j app_absorption_adams_boundary_rescaling_phi
    rw [hboundary.2.1]
  · unfold app_absorption_adams_boundary_rescaling_phi
    exact mul_nonneg (show 0 ≤ (m : ℝ) by exact_mod_cast Nat.zero_le m) hboundary.2.2.2

end

end Omega.UnitCirclePhaseArithmetic
