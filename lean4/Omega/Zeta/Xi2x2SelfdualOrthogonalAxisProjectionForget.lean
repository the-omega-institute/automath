import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-2x2-selfdual-orthogonal-axis-projection-forget`. -/
theorem paper_xi_2x2_selfdual_orthogonal_axis_projection_forget_coordinate_projection
    (rho theta rho' : ℝ) (hneq : rho ≠ rho') :
    (fun p : ℝ × ℝ => p.2) (rho, theta) = (fun p : ℝ × ℝ => p.2) (rho', theta) ∧
      ((rho, theta).1 = 0 ↔ rho = 0) := by
  have _ : rho ≠ rho' := hneq
  exact ⟨rfl, Iff.rfl⟩

/-- The real-axis polar factor of `L ^ (2s - 1)` written in real coordinates. -/
noncomputable def xi_2x2_selfdual_orthogonal_axis_projection_forget_rho
    (L realPart : ℝ) : ℝ :=
  (2 * realPart - 1) * Real.log L

/-- The phase-axis polar factor of `L ^ (2s - 1)` written in real coordinates. -/
noncomputable def xi_2x2_selfdual_orthogonal_axis_projection_forget_theta
    (L imaginaryPart : ℝ) : ℝ :=
  2 * imaginaryPart * Real.log L

/-- Projection to the phase axis forgets the radial coordinate. -/
def xi_2x2_selfdual_orthogonal_axis_projection_forget_phase_projection
    (_rho theta : ℝ) : ℝ :=
  theta

/-- Paper label: `cor:xi-2x2-selfdual-orthogonal-axis-projection-forget`.
The unitary slice is exactly `rho = 0`, and the phase projection is insensitive to the radial
axis retained by off-slice towers. -/
theorem paper_xi_2x2_selfdual_orthogonal_axis_projection_forget
    (L realPart imaginaryPart : ℝ) (hlog : Real.log L ≠ 0) :
    (xi_2x2_selfdual_orthogonal_axis_projection_forget_rho L realPart = 0 ↔
        realPart = 1 / 2) ∧
      xi_2x2_selfdual_orthogonal_axis_projection_forget_phase_projection
          (xi_2x2_selfdual_orthogonal_axis_projection_forget_rho L realPart)
          (xi_2x2_selfdual_orthogonal_axis_projection_forget_theta L imaginaryPart) =
        xi_2x2_selfdual_orthogonal_axis_projection_forget_theta L imaginaryPart ∧
        (xi_2x2_selfdual_orthogonal_axis_projection_forget_rho L realPart ≠ 0 →
          xi_2x2_selfdual_orthogonal_axis_projection_forget_phase_projection
              (xi_2x2_selfdual_orthogonal_axis_projection_forget_rho L realPart)
              (xi_2x2_selfdual_orthogonal_axis_projection_forget_theta L imaginaryPart) =
            xi_2x2_selfdual_orthogonal_axis_projection_forget_phase_projection 0
              (xi_2x2_selfdual_orthogonal_axis_projection_forget_theta L imaginaryPart)) := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · intro hrho
      unfold xi_2x2_selfdual_orthogonal_axis_projection_forget_rho at hrho
      rcases mul_eq_zero.mp hrho with hlinear | hlog_zero
      · linarith
      · exact False.elim (hlog hlog_zero)
    · intro hreal
      unfold xi_2x2_selfdual_orthogonal_axis_projection_forget_rho
      rw [hreal]
      ring
  · intro _hoffslice
    rfl

end Omega.Zeta
