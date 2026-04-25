import Mathlib.Tactic
import Omega.Folding.GaugePressureResolventDiscIdentity

namespace Omega.RootUnitCharacterPressureTensor

/-- The homogenized projective plane quartic attached to the gauge-pressure equation. -/
def gauge_pressure_plane_quartic_genus3_projective_model (X Y Z : ℚ) : ℚ :=
  X ^ 4 - X ^ 3 * Z - (2 * Y * Z + Z ^ 2) * X ^ 2 + (2 * Y * Z ^ 2 - Y ^ 3) * X + 2 * Y * Z ^ 3

/-- The derivative of the projective quartic with respect to `X`. -/
def gauge_pressure_plane_quartic_genus3_dX (X Y Z : ℚ) : ℚ :=
  4 * X ^ 3 - 3 * X ^ 2 * Z - 2 * (2 * Y * Z + Z ^ 2) * X + (2 * Y * Z ^ 2 - Y ^ 3)

/-- The derivative of the projective quartic with respect to `Y`. -/
def gauge_pressure_plane_quartic_genus3_dY (X Y Z : ℚ) : ℚ :=
  -(2 * X ^ 2 * Z) + (2 * Z ^ 2 - 3 * Y ^ 2) * X + 2 * Z ^ 3

/-- The classical smooth plane-quartic genus formula. -/
def gauge_pressure_plane_quartic_genus3_genus : ℕ :=
  (4 - 1) * (4 - 2) / 2

/-- Concrete package for the gauge-pressure plane quartic model. -/
def gauge_pressure_plane_quartic_genus3_statement : Prop :=
  (∀ μ u : ℚ,
      gauge_pressure_plane_quartic_genus3_projective_model μ u 1 =
        Omega.Folding.gaugePressureQuartic μ u) ∧
    (∀ X Y Z : ℚ,
      gauge_pressure_plane_quartic_genus3_dX X Y Z =
        4 * X ^ 3 - 3 * X ^ 2 * Z - 2 * (2 * Y * Z + Z ^ 2) * X + (2 * Y * Z ^ 2 - Y ^ 3)) ∧
    (∀ X Y Z : ℚ,
      gauge_pressure_plane_quartic_genus3_dY X Y Z =
        -(2 * X ^ 2 * Z) + (2 * Z ^ 2 - 3 * Y ^ 2) * X + 2 * Z ^ 3) ∧
    gauge_pressure_plane_quartic_genus3_projective_model 0 0 1 = 0 ∧
    gauge_pressure_plane_quartic_genus3_dY 0 0 1 = 2 ∧
    gauge_pressure_plane_quartic_genus3_projective_model 0 1 0 = 0 ∧
    gauge_pressure_plane_quartic_genus3_dX 0 1 0 = -1 ∧
    (∀ X Y : ℚ,
      gauge_pressure_plane_quartic_genus3_projective_model X Y 0 =
        X * (X ^ 3 - Y ^ 3)) ∧
    gauge_pressure_plane_quartic_genus3_genus = 3

/-- Paper label: `thm:gauge-pressure-plane-quartic-genus3`. -/
theorem paper_gauge_pressure_plane_quartic_genus3 :
    gauge_pressure_plane_quartic_genus3_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
  · intro μ u
    dsimp [gauge_pressure_plane_quartic_genus3_projective_model, Omega.Folding.gaugePressureQuartic]
    ring
  · intro X Y Z
    rfl
  · intro X Y Z
    rfl
  · norm_num [gauge_pressure_plane_quartic_genus3_projective_model]
  · norm_num [gauge_pressure_plane_quartic_genus3_dY]
  · norm_num [gauge_pressure_plane_quartic_genus3_projective_model]
  · norm_num [gauge_pressure_plane_quartic_genus3_dX]
  · intro X Y
    dsimp [gauge_pressure_plane_quartic_genus3_projective_model]
    ring
  · norm_num [gauge_pressure_plane_quartic_genus3_genus]

end Omega.RootUnitCharacterPressureTensor
